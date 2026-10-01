import QSB.CoreOpcodeStep

/-!
The bottom-first stack mutation for BASE `OP_CHECKSIGVERIFY` in the exact
lock. The signature checker result remains a supplied Boolean. A true result
removes the top public key and signature; a false result aborts. Core's
compiled checker and sighash behavior remain separate refinement obligations.
-/
namespace QSB.CoreChecksigStep
open ByteMachine

def step (s : CoreOpcodeStep.State) : Option CoreOpcodeStep.State :=
  if s.ops + 1 > 201 then none
  else if s.stack.length < 2 then none
  else match s.outcomes with
    | true :: rest =>
        some ⟨s.stack.take (s.stack.length - 2), rest, s.ops + 1⟩
    | _ => none

theorem step_of_reached_cells (pubKey sig : Bytes) (tail : List Bytes)
    (rest : List Bool) (ops : Nat) (budget : ¬ops + 1 > 201) :
    let initial : ByteMachine.State :=
      ⟨pubKey :: sig :: tail, true :: rest, ops⟩
    let final : ByteMachine.State := ⟨tail, rest, ops + 1⟩
    step (CoreOpcodeStep.ofByte initial) =
      some (CoreOpcodeStep.ofByte final) := by
  simp [step, CoreOpcodeStep.ofByte, budget]

/-- Every successful source-shaped CHECKSIGVERIFY stack transition agrees
with the byte-model transition. This proves the stack/cost effect, not that
Core's DER, key, sighash, and ECDSA checks produced the supplied true result. -/
theorem successful_source_step_refines_byte (hashes : Hashes)
    (before : ByteMachine.State) (after : CoreOpcodeStep.State)
    (source : step (CoreOpcodeStep.ofByte before) = some after) :
    ∃ byteAfter : ByteMachine.State,
      ByteMachine.step hashes .checksigverify before = some byteAfter ∧
      after = CoreOpcodeStep.ofByte byteAfter := by
  cases before with
  | mk stack outcomes ops =>
    cases stack with
    | nil => simp [step, CoreOpcodeStep.ofByte] at source
    | cons pubKey restStack =>
      cases restStack with
      | nil => simp [step, CoreOpcodeStep.ofByte] at source
      | cons sig tail =>
        by_cases budget : ops + 1 > 201
        · simp [step, CoreOpcodeStep.ofByte, budget] at source
        · cases outcomes with
          | nil => simp [step, CoreOpcodeStep.ofByte, budget] at source
          | cons result rest =>
            cases result with
            | false => simp [step, CoreOpcodeStep.ofByte, budget] at source
            | true =>
              let byteAfter : ByteMachine.State := ⟨tail, rest, ops + 1⟩
              have sourceStep := step_of_reached_cells pubKey sig tail rest ops budget
              have byteStep : ByteMachine.step hashes .checksigverify
                  ⟨pubKey :: sig :: tail, true :: rest, ops⟩ = some byteAfter := by
                unfold ByteMachine.step
                simp [budget, byteAfter]
              exact ⟨byteAfter, byteStep,
                Option.some.inj (source.symm.trans sourceStep)⟩

end QSB.CoreChecksigStep
