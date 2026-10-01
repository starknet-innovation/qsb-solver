import QSB.DynamicCheckedCertificate
import QSB.CoreFinalTruth

/-!
The complete parameterized Config A lock ends in CHECKMULTISIG for every
choice of its data bytes. Thus a successful source-shaped structural run has
the same final truth value under Core's CastToBool loop and the byte model's
canonical-Boolean test. This is a Lean-to-Lean source-model bridge, not a
compiled Bitcoin Core refinement.
-/
namespace QSB.DynamicCoreFinalTruth
open ByteMachine

theorem program_ends_in_multisig
    (lock : DynamicCheckedCertificate.Lock) :
    ∃ pre : List Op,
      DynamicCheckedCertificate.program lock =
        pre ++ [.checkmultisig] := by
  let prior := DynamicFullSerialized.priorOps lock.pin lock.nonce0
    lock.firstCommitment
  refine ⟨DynamicWholeSource.beforeLateVerifyProgram prior lock.nonce1
      lock.secondCommitment ++ [.checksigverify] ++
      ByteFinalCounts.finalSetup, ?_⟩
  simpa only [DynamicCheckedCertificate.program, prior,
    List.append_assoc] using
    DynamicWholeSource.full_program_late_verify_split prior lock.nonce1
      lock.secondCommitment

/-- Core-shaped final truth and modeled final truth agree after any successful
full parameterized structural run. Signature outcomes are still supplied. -/
theorem source_run_final_truth (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (initial : ByteMachine.State) (final : CoreOpcodeStep.State)
    (run : CoreStructuralRun.run hashes
      (DynamicCheckedCertificate.program lock)
      (CoreOpcodeStep.ofByte initial) = some final) :
    CoreFinalTruth.coreFinalTruth final =
      ByteMachine.finalTruth
        ⟨final.stack.reverse, final.outcomes, final.ops⟩ := by
  obtain ⟨pre, ending⟩ := program_ends_in_multisig lock
  rw [ending] at run
  exact CoreFinalTruth.source_run_ending_multisig_final_truth
    hashes pre initial final run

/-- A successful parameterized candidate can be read with the source-shaped
bare-script final truth test. Its source-site checks remain explicit. -/
theorem candidate_sound_core_truth (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.candidate hashes lock stack
      validKey verify firstRound = some final) :
    CoreStructuralRun.run hashes (DynamicCheckedCertificate.program lock)
      (DynamicCheckedCertificate.initial stack firstRound) = some final ∧
    CoreFinalTruth.coreFinalTruth final = true ∧
    DynamicCheckedCertificate.sourceSites hashes lock stack validKey verify
      firstRound = true ∧
    DynamicCheckedCertificate.finalChecked hashes lock stack validKey verify
      firstRound = true := by
  obtain ⟨run, truth, sites, checked⟩ :=
    DynamicCheckedCertificate.candidate_sound hashes lock stack validKey
      verify firstRound final found
  have coreTruth := source_run_final_truth hashes lock
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ final run
  exact ⟨run, coreTruth.trans truth, sites, checked⟩

/-- A source-shaped accepted structural run with all reached signature-site
checks is returned by the two-candidate search. Both first-round Booleans
remain possible. The premise is not compiled-Core acceptance. -/
theorem search_complete_from_core_truth (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (available : ∃ firstRound final,
      CoreStructuralRun.run hashes (DynamicCheckedCertificate.program lock)
        (DynamicCheckedCertificate.initial stack firstRound) = some final ∧
      CoreFinalTruth.coreFinalTruth final = true ∧
      DynamicCheckedCertificate.sourceSites hashes lock stack validKey verify
        firstRound = true ∧
      DynamicCheckedCertificate.finalChecked hashes lock stack validKey verify
        firstRound = true) :
    ∃ firstRound final,
      DynamicCheckedCertificate.search hashes lock stack validKey verify =
        some (firstRound, final) := by
  obtain ⟨firstRound, final, run, truth, sites, checked⟩ := available
  apply DynamicCheckedCertificate.search_complete hashes lock stack
    validKey verify
  refine ⟨firstRound, final, run, ?_, sites, checked⟩
  rw [← source_run_final_truth hashes lock
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ final run]
  exact truth

end QSB.DynamicCoreFinalTruth
