import QSB.CoreStructuralEquiv
import QSB.ByteFinalCounts

/-!
Core's source `CastToBool` treats empty and negative-zero byte strings as
false. The generated lock ends in CHECKMULTISIG, whose successful structural
transition pushes a canonical Boolean byte string. Thus the source-shaped
final truth test and `ByteMachine.finalTruth` agree for every successful
modeled full run, regardless of the initial stack and supplied scan outcomes.
This does not prove compiled-Core-to-model execution or ECDSA correctness.
-/
namespace QSB.CoreFinalTruth
open ByteMachine
open FirstAcceptedOrigin
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Recursive form of Core v27.2's `CastToBool` loop: a nonzero byte is true
except for a final 0x80 preceded only by zeros. -/
def castToBool : Bytes → Bool
  | [] => false
  | b :: rest =>
      if b == 0 then castToBool rest
      else if rest.isEmpty && b == 0x80 then false
      else true

theorem castToBool_boolBytes (result : Bool) :
    castToBool (boolBytes result) = result := by
  cases result <;> decide

def coreFinalTruth (s : CoreOpcodeStep.State) : Bool :=
  castToBool (s.stack.getLast?.getD [])

/-- Successful modeled CHECKMULTISIG always places a canonical Boolean cell
on top, including when its supplied scan result is false. -/
theorem byte_multisig_final_boolean (hashes : Hashes)
    (before after : ByteMachine.State)
    (success : ByteMachine.step hashes .checkmultisig before = some after) :
    ∃ result tail, after.stack = boolBytes result :: tail := by
  obtain ⟨n, m, result, _keys, _sigs, cleanup, _outcome, _cost⟩ :=
    CoreMultisigCleanup.successful_byte_multisig_source_cells
      hashes before after success
  obtain ⟨_dummy, shape⟩ :=
    CoreMultisigCleanup.cleanup_success before.stack n.toNat m.toNat
      result after.stack.reverse cleanup
  refine ⟨result, before.stack.drop
    (CoreMultisigStack.sourceArgumentDepth n.toNat m.toNat), ?_⟩
  have reversed := congrArg List.reverse shape
  simpa using reversed

/-- For any successful program ending in CHECKMULTISIG, source-shaped
CastToBool of the final top cell equals the byte model's truth test. -/
theorem byte_run_ending_multisig_final_truth (hashes : Hashes)
    (ops : List Op)
    (initial final : ByteMachine.State)
    (success : ByteMachine.run hashes (ops ++ [.checkmultisig]) initial =
      some final) :
    castToBool (final.stack.head?.getD []) = finalTruth final := by
  rw [ByteMachine.run_append] at success
  cases hprefix : ByteMachine.run hashes ops initial with
  | none => simp [hprefix] at success
  | some before =>
      simp only [hprefix, Option.bind_some] at success
      obtain ⟨after, checked, _capacity, finished⟩ :=
        run_cons_success hashes .checkmultisig [] before final success
      simp [ByteMachine.run] at finished
      subst final
      obtain ⟨result, tail, stackShape⟩ :=
        byte_multisig_final_boolean hashes before after checked
      simp [finalTruth, stackShape, castToBool_boolBytes]
      cases result <;> decide

/-- Exact literal-lock specialization of the general final-opcode result. -/
theorem byte_full_run_final_truth (hashes : Hashes)
    (initial final : ByteMachine.State)
    (success : ByteMachine.run hashes ByteLayout.program initial = some final) :
    castToBool (final.stack.head?.getD []) = finalTruth final := by
  have split : ByteLayout.program =
      ByteLayout.program.take 879 ++ [.checkmultisig] := by decide
  rw [split] at success
  exact byte_run_ending_multisig_final_truth hashes _ initial final success

/-- The general final-truth equivalence in bottom-first Core-shaped stack
order. Signature results are supplied, not computed by actual Core ECDSA. -/
theorem source_run_ending_multisig_final_truth (hashes : Hashes)
    (ops : List Op)
    (initial : ByteMachine.State) (final : CoreOpcodeStep.State)
    (success : CoreStructuralRun.run hashes (ops ++ [.checkmultisig])
      (CoreOpcodeStep.ofByte initial) = some final) :
    coreFinalTruth final =
      finalTruth ⟨final.stack.reverse, final.outcomes, final.ops⟩ := by
  rw [CoreStructuralEquiv.run_eq_byte] at success
  cases hbyte : ByteMachine.run hashes (ops ++ [.checkmultisig]) initial with
  | none => simp [hbyte] at success
  | some byteFinal =>
      simp [hbyte] at success
      subst final
      simpa [coreFinalTruth, CoreOpcodeStep.ofByte] using
        byte_run_ending_multisig_final_truth hashes ops initial byteFinal hbyte

/-- Exact literal-lock specialization of the source-shaped result. -/
theorem source_full_run_final_truth (hashes : Hashes)
    (initial : ByteMachine.State) (final : CoreOpcodeStep.State)
    (success : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte initial) = some final) :
    coreFinalTruth final =
      finalTruth ⟨final.stack.reverse, final.outcomes, final.ops⟩ := by
  have split : ByteLayout.program =
      ByteLayout.program.take 879 ++ [.checkmultisig] := by decide
  rw [split] at success
  exact source_run_ending_multisig_final_truth hashes _ initial final success

/-- A source-shaped acceptance check of the final top cell supplies the
`finalTruth` premise used by the extraction theorems, once structural-run
refinement has been established. -/
theorem source_truth_of_castToBool (hashes : Hashes)
    (initial : ByteMachine.State) (final : CoreOpcodeStep.State)
    (success : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte initial) = some final)
    (accepted : coreFinalTruth final = true) :
    finalTruth ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true := by
  rw [← source_full_run_final_truth hashes initial final success]
  exact accepted

end QSB.CoreFinalTruth
