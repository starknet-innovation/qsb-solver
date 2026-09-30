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

end QSB.ByteMachine
