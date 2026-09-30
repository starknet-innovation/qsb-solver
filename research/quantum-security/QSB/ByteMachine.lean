import QSB.ByteIndex

/-!
A byte-string model of the opcodes emitted by Config A. Unlike the tagged
symbolic machine, equality here compares actual bytes and the hash operations
are supplied as arbitrary functions. Thus hash collisions are not excluded by
the type model. The numeric operations use the source-shaped ScriptNum parser
and serializer in `QSB.ByteIndex`.

This is an intermediate semantics, not a full Bitcoin Core refinement:
scriptSig execution, transaction parsing, signature encoding, FindAndDelete,
sighash and ECDSA are still external. The Boolean signature outcomes supplied
to a state must eventually be justified by Core's byte-level checker.
-/
namespace QSB.ByteMachine

abbrev Bytes := List UInt8

structure Hashes where
  h160 : Bytes → Bytes
  h256 : Bytes → Bytes
  h160_width : ∀ x, (h160 x).length = 20
  h256_width : ∀ x, (h256 x).length = 32

inductive Op where
  | push : Bytes → Op
  | dup | over | swap | roll | min | add | hash160 | sha256 | equalverify
  | checksigverify | checkmultisig
  deriving DecidableEq, Repr

structure State where
  stack : List Bytes
  outcomes : List Bool
  ops : Nat := 0
  deriving DecidableEq, Repr

def boolBytes (b : Bool) : Bytes := if b then [1] else []

def step (hashes : Hashes) (op : Op) (s : State) : Option State := do
  let cost := match op with | .push _ => 0 | _ => 1
  let s := { s with ops := s.ops + cost }
  if s.ops > 201 then none else
  match op, s.stack with
  | .push x, xs =>
      if x.length > 520 then none else some { s with stack := x :: xs }
  | .dup, x :: xs => some { s with stack := x :: x :: xs }
  | .over, x :: y :: xs => some { s with stack := y :: x :: y :: xs }
  | .swap, x :: y :: xs => some { s with stack := y :: x :: xs }
  | .roll, raw :: xs => do
      let n ← ByteIndex.parseScriptNum raw
      if n < 0 then none else do
        let x ← xs[n.toNat]?
        some { s with stack := x :: xs.eraseIdx n.toNat }
  | .min, x :: y :: xs => do
      let a ← ByteIndex.parseScriptNum x
      let b ← ByteIndex.parseScriptNum y
      let value ← ByteIndex.encodeScriptNum (min a b)
      some { s with stack := value :: xs }
  | .add, x :: y :: xs => do
      let a ← ByteIndex.parseScriptNum x
      let b ← ByteIndex.parseScriptNum y
      let value ← ByteIndex.encodeScriptNum (a + b)
      some { s with stack := value :: xs }
  | .hash160, x :: xs =>
      some { s with stack := hashes.h160 x :: xs }
  | .sha256, x :: xs =>
      some { s with stack := hashes.h256 x :: xs }
  | .equalverify, x :: y :: xs =>
      if x = y then some { s with stack := xs } else none
  | .checksigverify, _pub :: _sig :: xs =>
      match s.outcomes with
      | true :: rest => some { s with stack := xs, outcomes := rest }
      | _ => none
  | .checkmultisig, rawN :: xs => do
      let n ← ByteIndex.parseScriptNum rawN
      if n < 0 ∨ n > 20 ∨ s.ops + n.toNat > 201 then none else do
        let rawM ← xs[n.toNat]?
        let m ← ByteIndex.parseScriptNum rawM
        if m < 0 ∨ m > n then none else do
          let dummy ← xs[n.toNat + 1 + m.toNat]?
          if !dummy.isEmpty then none else do
            let b :: rest := s.outcomes | none
            some { stack := boolBytes b :: xs.drop (n.toNat + m.toNat + 2),
                   outcomes := rest, ops := s.ops + n.toNat }
  | _, _ => none

def run (hashes : Hashes) : List Op → State → Option State
  | [], s => some s
  | op :: rest, s => do
      let s' ← step hashes op s
      if s'.stack.length > 1000 then none else run hashes rest s'

theorem run_append (hashes : Hashes) (before after : List Op) (s : State) :
    run hashes (before ++ after) s =
      (run hashes before s).bind (run hashes after) := by
  induction before generalizing s with
  | nil => rfl
  | cons op rest ih =>
      simp only [List.cons_append, run]
      cases hstep : step hashes op s with
      | none => simp
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large]
          · simp [large, ih]

/-- Executing a sequence of byte pushes places their values, in reverse
instruction order, above an arbitrary starting stack. The size hypotheses
are the legacy Script element and combined-stack limits. -/
theorem run_pushes (hashes : Hashes) (values : List Bytes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (small : ∀ value ∈ values, value.length ≤ 520)
    (capacity : values.length + stack.length ≤ 1000)
    (budget : cost ≤ 201) :
    run hashes (values.map Op.push) (State.mk stack outcomes cost) =
      some (State.mk (values.reverse ++ stack) outcomes cost) := by
  induction values generalizing stack with
  | nil => rfl
  | cons value rest ih =>
      have valueSmall : value.length ≤ 520 := small value (by simp)
      have restSmall : ∀ x ∈ rest, x.length ≤ 520 := by
        intro x hx
        exact small x (by simp [hx])
      have restCapacity : rest.length + (value :: stack).length ≤ 1000 := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using capacity
      have stepPush : step hashes (.push value) (State.mk stack outcomes cost) =
          some (State.mk (value :: stack) outcomes cost) := by
        unfold step
        have within : ¬ (cost > 201) := by omega
        have width : ¬ (value.length > 520) := by omega
        simp [within, width]
      simp only [List.map_cons, run, stepPush]
      have size : ¬ ((value :: stack).length > 1000) := by
        simp only [List.length_cons] at capacity ⊢
        omega
      simp only [List.length_cons] at capacity
      simp [ih (value :: stack) restSmall restCapacity,
        List.reverse_cons, List.append_assoc]
      omega

/-- A nonempty sequence of modeled pushes cannot finish if its final stack
would exceed the 1000-cell combined-stack limit. -/
theorem run_pushes_overflow (hashes : Hashes) (values : List Bytes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (nonempty : values ≠ [])
    (small : ∀ value ∈ values, value.length ≤ 520)
    (over : values.length + stack.length > 1000)
    (budget : cost ≤ 201) :
    run hashes (values.map Op.push) (State.mk stack outcomes cost) = none := by
  induction values generalizing stack with
  | nil => contradiction
  | cons value rest ih =>
      have valueSmall : value.length ≤ 520 := small value (by simp)
      have restSmall : ∀ x ∈ rest, x.length ≤ 520 := by
        intro x hx
        exact small x (by simp [hx])
      have stepPush : step hashes (.push value) (State.mk stack outcomes cost) =
          some (State.mk (value :: stack) outcomes cost) := by
        unfold step
        have within : ¬ (cost > 201) := by omega
        have width : ¬ (value.length > 520) := by omega
        simp [within, width]
      simp only [List.map_cons, run, stepPush]
      by_cases size : (value :: stack).length > 1000
      · simp
        intro h
        simp only [List.length_cons] at size
        omega
      · have restNonempty : rest ≠ [] := by
          intro empty
          subst rest
          simp only [List.length_cons, List.length_nil] at over
          simp only [List.length_cons] at size
          omega
        have restOver : rest.length + (value :: stack).length > 1000 := by
          simp only [List.length_cons] at over ⊢
          omega
        simp
        intro _
        exact ih (value :: stack) restNonempty restSmall restOver

/-- A successful numeric addition has parsed both supplied ScriptNum cells.
The parser rejects encodings longer than four bytes, regardless of their
mathematical value or minimality. -/
theorem add_success_requires_four_byte_operands (hashes : Hashes)
    (x y : Bytes) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat) (next : State)
    (success : step hashes .add
      (State.mk (x :: y :: stack) outcomes cost) = some next) :
    x.length ≤ 4 ∧ y.length ≤ 4 := by
  have parseLong (raw : Bytes) (long : raw.length > 4) :
      ByteIndex.parseScriptNum raw = none := by
    simp [ByteIndex.parseScriptNum, long]
  constructor
  · by_contra long
    have hx : x.length > 4 := by omega
    have bad := parseLong x hx
    unfold step at success
    simp [bad] at success
  · by_contra long
    have hy : y.length > 4 := by omega
    have bad := parseLong y hy
    unfold step at success
    simp [bad] at success

def finalTruth (s : State) : Bool :=
  s.stack.head? = some [1]

/-- A byte-level HORS comparison accepts exactly when the supplied hash of
the actual opening bytes equals the selected commitment bytes. The hash is
arbitrary; this theorem does not assume collision freedom. -/
theorem hash_compare_accepts_iff (hashes : Hashes)
    (opening commitment : Bytes) :
    (run hashes [.hash160, .equalverify]
      (State.mk [opening, commitment] [] 0)).isSome = true ↔
      hashes.h160 opening = commitment := by
  unfold run step
  simp
  unfold run
  unfold step
  by_cases equal : hashes.h160 opening = commitment
  · simp [equal, run]
  · simp [equal, run]

/-- No later suffix can repair a failed HASH160 comparison. This applies to
arbitrary stack tails, operation counts, hash functions, and later opcodes. -/
theorem successful_hash_comparison (hashes : Hashes)
    (opening commitment : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (rest : List Op)
    (accepted : (run hashes (.hash160 :: .equalverify :: rest)
      (State.mk (opening :: commitment :: tail) outcomes cost)).isSome = true) :
    hashes.h160 opening = commitment := by
  by_contra unequal
  unfold run at accepted
  unfold step at accepted
  by_cases cap : cost + 1 > 201
  · simp [cap] at accepted
  · simp [cap] at accepted
    unfold run at accepted
    unfold step at accepted
    simp [unequal] at accepted

/-- A successful whole program forces the hash equation at any reached
`HASH160; EQUALVERIFY` pair, provided the public prefix execution exposes the
opening and compared bytes at the pair boundary. -/
theorem successful_hash_comparison_in_context (hashes : Hashes)
    (before after : List Op) (initial : State)
    (opening commitment : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (before_state : run hashes before initial =
      some (State.mk (opening :: commitment :: tail) outcomes cost))
    (accepted : run hashes
      (before ++ .hash160 :: .equalverify :: after) initial = some final) :
    hashes.h160 opening = commitment := by
  rw [run_append, before_state] at accepted
  simp only [Option.bind_some] at accepted
  apply successful_hash_comparison hashes opening commitment tail outcomes cost after
  rw [accepted]
  rfl

end QSB.ByteMachine
