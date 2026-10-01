import QSB.CoreRoll
import QSB.CoreNumericOps
import QSB.ByteLayout

/-!
A bottom-first, source-shaped transition model for the non-signature opcodes
in the generated locking script. The stack changes follow Bitcoin Core
v27.2's `EvalScript` cases: push-back, stacktop copies, reverse-depth roll,
numeric parse/serialize, hashing, and byte equality. `signature` opcodes are
deliberately outside this transition model. A separate proof must connect
their DER/sighash/ECDSA checks to the supplied outcomes of `ByteMachine`.

This is a mathematical model of the cited source cases, not a refinement of
the compiled C++ interpreter or arbitrary scriptSig execution.
-/
namespace QSB.CoreOpcodeStep
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

structure State where
  stack : List Bytes  -- Core vector order: bottom first
  outcomes : List Bool
  ops : Nat
  deriving DecidableEq, Repr

def ofByte (s : ByteMachine.State) : State :=
  ⟨s.stack.reverse, s.outcomes, s.ops⟩

def supported : Op → Bool
  | .checksigverify | .checkmultisig => false
  | _ => true

/-- One source-shaped non-signature step. The lock has no altstack or control
opcodes; `run` checks its combined stack limit after this step. -/
def step (hashes : Hashes) (op : Op) (s : State) : Option State := do
  let cost := match op with | .push _ => 0 | _ => 1
  let ops := s.ops + cost
  if ops > 201 then none else
  match op, s.stack.reverse with
  | .push x, _ =>
      if x.length > 520 then none else
        some ⟨s.stack ++ [x], s.outcomes, ops⟩
  | .dup, x :: _ => some ⟨s.stack ++ [x], s.outcomes, ops⟩
  | .over, _ :: y :: _ => some ⟨s.stack ++ [y], s.outcomes, ops⟩
  | .swap, x :: y :: xs => some ⟨xs.reverse ++ [x, y], s.outcomes, ops⟩
  | .roll, raw :: xs =>
      let stack ← CoreRoll.coreRollWithRaw raw xs.reverse
      some ⟨stack, s.outcomes, ops⟩
  | .min, x :: y :: xs =>
      let raw ← CoreNumericOps.coreMin x y
      some ⟨xs.reverse ++ [raw], s.outcomes, ops⟩
  | .add, x :: y :: xs =>
      let raw ← CoreNumericOps.coreAdd x y
      some ⟨xs.reverse ++ [raw], s.outcomes, ops⟩
  | .hash160, x :: xs =>
      some ⟨xs.reverse ++ [hashes.h160 x], s.outcomes, ops⟩
  | .sha256, x :: xs =>
      some ⟨xs.reverse ++ [hashes.h256 x], s.outcomes, ops⟩
  | .equalverify, x :: y :: xs =>
      if x = y then some ⟨xs.reverse, s.outcomes, ops⟩ else none
  | _, _ => none

/-- Interpret a non-signature segment, with Core's post-op stack-size check. -/
def run (hashes : Hashes) : List Op → State → Option State
  | [], s => some s
  | op :: rest, s => do
      let s' ← step hashes op s
      if s'.stack.length > 1000 then none else run hashes rest s'

private theorem coreRollWithRaw_empty (raw : Bytes) :
    CoreRoll.coreRollWithRaw raw [] = none := by
  unfold CoreRoll.coreRollWithRaw
  cases parsed : CoreScriptNum.coreSetVch raw with
  | none => simp
  | some value =>
      by_cases negative : value < 0
      · simp [parsed, negative]
      · simp [parsed, negative, CoreRoll.coreRoll]

theorem step_eq_byte (hashes : Hashes) (op : Op) (s : ByteMachine.State)
    (ok : supported op = true) :
    step hashes op (ofByte s) =
      (ByteMachine.step hashes op s).map ofByte := by
  cases s with
  | mk stack outcomes ops =>
    cases op <;> simp [supported] at ok
    all_goals
      unfold step ByteMachine.step
      cases stack with
      | nil =>
          simp [ofByte] <;> split_ifs <;>
            simp [ofByte, List.reverse_cons, List.reverse_append]
      | cons x xs =>
          cases xs with
          | nil =>
              simp [ofByte, coreRollWithRaw_empty] <;>
                try split_ifs <;>
                simp [ofByte, List.reverse_cons, List.reverse_append]
          | cons y ys =>
              simp [ofByte,
                CoreNumericOps.coreMin_eq_model,
                CoreNumericOps.coreAdd_eq_model,
                CoreNumericOps.modelMin, CoreNumericOps.modelAdd,
                CoreRoll.coreRollWithRaw_reverse,
                CoreRoll.byteRollTop, CoreRoll.topRoll] <;>
                try split_ifs <;>
                simp [ofByte, List.reverse_cons, List.reverse_append,
                  Option.bind_assoc] <;>
                simp only [← List.reverse_cons] <;>
                simp [CoreRoll.coreRollWithRaw_reverse,
                  CoreRoll.byteRollTop, CoreRoll.topRoll, Option.bind_assoc] <;>
                (have hrev := CoreRoll.coreRollWithRaw_reverse x (y :: ys)
                 simp only [List.reverse_cons] at hrev
                 rw [hrev]
                 cases parsed : ByteIndex.parseScriptNum x with
                 | none => simp [CoreRoll.byteRollTop, parsed]
                 | some value =>
                     simp [CoreRoll.byteRollTop, CoreRoll.topRoll,
                       parsed, ofByte, Option.bind_assoc] <;>
                     split_ifs <;> simp [ofByte] <;>
                     cases hget : (y :: ys)[value.toNat]? <;> simp [hget])

theorem run_eq_byte (hashes : Hashes) (ops : List Op)
    (ok : ∀ op ∈ ops, supported op = true) (s : ByteMachine.State) :
    run hashes ops (ofByte s) =
      (ByteMachine.run hashes ops s).map ofByte := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      have opOk : supported op = true := ok op (by simp)
      have restOk : ∀ next ∈ rest, supported next = true := by
        intro next member
        exact ok next (by simp [member])
      simp only [run, ByteMachine.run]
      rw [step_eq_byte hashes op s opOk]
      cases hstep : ByteMachine.step hashes op s with
      | none => simp
      | some next =>
          simp only [hstep, Option.map_some, Option.bind_some]
          have sameLength : (ofByte next).stack.length = next.stack.length := by
            simp [ofByte]
          by_cases large : next.stack.length > 1000
          · simp [sameLength, large]
          · simp [sameLength, large, ih restOk next]

def segment (start count : Nat) : List Op :=
  (ByteLayout.program.drop start).take count

/-- The six maximal runs of lock opcodes between its six signature sites. -/
def segments : List (List Op) :=
  [segment 0 2, segment 3 2, segment 6 417,
   segment 424 22, segment 447 409, segment 857 22]

/-- This literal partition covers all 880 generated instructions, with the
signature opcodes only at positions 2, 5, 423, 446, 856, and 879. -/
theorem literal_partition :
    ByteLayout.program =
      segment 0 2 ++ [.checksigverify] ++
      segment 3 2 ++ [.checksigverify] ++
      segment 6 417 ++ [.checksigverify] ++
      segment 424 22 ++ [.checkmultisig] ++
      segment 447 409 ++ [.checksigverify] ++
      segment 857 22 ++ [.checkmultisig] := by
  decide

theorem literal_segments_supported :
    segments.all (fun xs => xs.all supported) = true := by
  decide

theorem supported_of_segment (xs : List Op) (member : xs ∈ segments) :
    ∀ op ∈ xs, supported op = true := by
  have all := (List.all_eq_true.mp literal_segments_supported) xs member
  exact List.all_eq_true.mp all

/-- Every signature-free interval of the actual lock has the same result in
the bottom-first source-step model and the top-first byte model, for any
initial stack, hash functions, outcomes, and opcode count. This leaves six
signature sites and the compiled-interpreter connection as explicit gaps. -/
theorem literal_segment_run_eq_byte (hashes : Hashes) (xs : List Op)
    (member : xs ∈ segments) (s : ByteMachine.State) :
    run hashes xs (ofByte s) =
      (ByteMachine.run hashes xs s).map ofByte :=
  run_eq_byte hashes xs (supported_of_segment xs member) s

end QSB.CoreOpcodeStep
