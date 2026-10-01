import QSB.CoreChecksigStep
import QSB.CoreMultisigStep

/-!
A compositional bottom-first source-shaped interpreter for the generated
opcode vocabulary. Numeric, roll, hash, push, and equality cases come from
`CoreOpcodeStep`; signature opcodes use source-shaped stack transitions with
their scan Booleans supplied explicitly. Successful execution projects to
the top-first `ByteMachine` for any initial stack and opcode list. This is
not compiled Core refinement or proof of the supplied cryptographic checks.
-/
namespace QSB.CoreStructuralRun
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def step (hashes : Hashes) (op : Op)
    (s : CoreOpcodeStep.State) : Option CoreOpcodeStep.State :=
  match op with
  | .checksigverify => CoreChecksigStep.step s
  | .checkmultisig => CoreMultisigStep.step s
  | _ => CoreOpcodeStep.step hashes op s

def run (hashes : Hashes) : List Op → CoreOpcodeStep.State →
    Option CoreOpcodeStep.State
  | [], s => some s
  | op :: rest, s => do
      let next ← step hashes op s
      if next.stack.length > 1000 then none else run hashes rest next

private theorem ordinary_step_refines (hashes : Hashes) (op : Op)
    (s : ByteMachine.State) (after : CoreOpcodeStep.State)
    (supported : CoreOpcodeStep.supported op = true)
    (executed : CoreOpcodeStep.step hashes op
      (CoreOpcodeStep.ofByte s) = some after) :
    ∃ byteAfter,
      ByteMachine.step hashes op s = some byteAfter ∧
      after = CoreOpcodeStep.ofByte byteAfter := by
  rw [CoreOpcodeStep.step_eq_byte hashes op s supported] at executed
  cases h : ByteMachine.step hashes op s with
  | none => simp [h] at executed
  | some byteAfter =>
      simp only [h, Option.map_some] at executed
      exact ⟨byteAfter, rfl, Option.some.inj executed.symm⟩

/-- One successful source-shaped transition has the same byte-model stack,
outcome cursor, and opcode count for every opcode in the generated vocabulary.
At signature sites the Boolean remains a supplied input. -/
theorem step_refines_byte (hashes : Hashes) (op : Op)
    (s : ByteMachine.State) (after : CoreOpcodeStep.State)
    (executed : step hashes op (CoreOpcodeStep.ofByte s) = some after) :
    ∃ byteAfter,
      ByteMachine.step hashes op s = some byteAfter ∧
      after = CoreOpcodeStep.ofByte byteAfter := by
  cases op <;> simp only [step] at executed
  case checksigverify =>
    exact CoreChecksigStep.successful_source_step_refines_byte
      hashes s after executed
  case checkmultisig =>
    exact CoreMultisigStep.successful_source_step_refines_byte
      hashes s after executed
  all_goals
    exact ordinary_step_refines hashes _ s after (by rfl) executed

/-- A successful source-shaped run of any opcode list projects to the same
top-first byte run, including Core's post-op 1000-cell check. This theorem
is one-way because only accepted source runs are needed for extraction. -/
theorem run_refines_byte (hashes : Hashes) (ops : List Op)
    (initial : ByteMachine.State) (after : CoreOpcodeStep.State)
    (executed : run hashes ops (CoreOpcodeStep.ofByte initial) =
      some after) :
    ∃ byteAfter,
      ByteMachine.run hashes ops initial = some byteAfter ∧
      after = CoreOpcodeStep.ofByte byteAfter := by
  induction ops generalizing initial after with
  | nil =>
      exact ⟨initial, rfl, Option.some.inj executed.symm⟩
  | cons op rest ih =>
      simp only [run] at executed
      cases hStep : step hashes op (CoreOpcodeStep.ofByte initial) with
      | none => simp [hStep] at executed
      | some next =>
          obtain ⟨byteNext, byteStep, shape⟩ :=
            step_refines_byte hashes op initial next hStep
          subst next
          have sameLength :
              (CoreOpcodeStep.ofByte byteNext).stack.length =
                byteNext.stack.length := by simp [CoreOpcodeStep.ofByte]
          by_cases oversized : byteNext.stack.length > 1000
          · simp [hStep, sameLength, oversized] at executed
          · have restRun : run hashes rest
                (CoreOpcodeStep.ofByte byteNext) = some after := by
              simpa [hStep, sameLength, oversized] using executed
            obtain ⟨byteAfter, byteRun, resultShape⟩ :=
              ih byteNext after restRun
            refine ⟨byteAfter, ?_, resultShape⟩
            simp only [ByteMachine.run, byteStep]
            simp [oversized, byteRun]

/-- Specialization to the exact 880-opcode disposable lock. It accepts any
post-scriptSig byte stack and any outcome list, provided the source-shaped
structural run succeeds. The real Core-to-source and checker-result bridge
is still outside this theorem. -/
theorem literal_lock_refines_byte (hashes : Hashes)
    (initial : ByteMachine.State) (after : CoreOpcodeStep.State)
    (executed : run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte initial) = some after) :
    ∃ byteAfter,
      ByteMachine.run hashes ByteLayout.program initial = some byteAfter ∧
      after = CoreOpcodeStep.ofByte byteAfter :=
  run_refines_byte hashes ByteLayout.program initial after executed

end QSB.CoreStructuralRun
