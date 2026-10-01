import QSB.CoreCheckedRunCertificate
import QSB.DynamicCheckedCertificate
import QSB.DynamicCoreFinalTruth

/-!
The parameterized Config A program is run with signature-site results computed
at the reached stacks.  These results concern the Lean source-shaped checker;
the compiled Bitcoin Core interpreter, transaction sighash, and ECDSA remain
external to this model.
-/
namespace QSB.CoreCheckedDynamic
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

theorem program_final_split (lock : DynamicCheckedCertificate.Lock) :
    DynamicCheckedCertificate.program lock =
      DynamicCheckedCertificate.beforeFinalProgram lock ++
        [.checkmultisig] := by
  have suffix840 : ByteLayout.program.drop 840 =
      FinalBonusSecond.bothBonusOps ++ ByteLayout.program.drop 850 := by
    decide
  simp [DynamicCheckedCertificate.program,
    DynamicCheckedCertificate.beforeFinalProgram,
    DynamicWholeSource.fullProgram,
    DynamicWholeSource.beforeFinalCheckProgram,
    DynamicBonusChain.finalCheckPrefix,
    DynamicBonusChain.final_round_program_eq,
    suffix840, ByteLatePuzzle.generated_late_final_check_split,
    List.append_assoc]

/-- An accepted, truthy checked execution of any parameterized Config A
program has a true final source-shaped multisignature scan.  The first scan
result is not constrained by this theorem. -/
theorem checked_run_final_scan_true (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ before previous,
      CoreCheckedStep.run hashes (DynamicCheckedCertificate.wire lock)
        validKey verify
        (DynamicCheckedCertificate.beforeFinalProgram lock) initial =
          some (before, previous) ∧
      CoreCheckedStep.checkedMultisig (DynamicCheckedCertificate.wire lock)
        validKey verify before = some (final, true) ∧
      records = previous ++ [true] := by
  have structural := CoreCheckedStep.checked_run_frames hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.program lock) initial final records [] success
  have truth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true := by
    have sourceTruth := DynamicCoreFinalTruth.source_run_final_truth hashes
      lock ⟨initial.stack.reverse, records, initial.ops⟩
      (CoreCheckedStep.lift final []) (by
        simpa [DynamicCheckedCertificate.initial,
          CoreCheckedStep.lift, CoreOpcodeStep.ofByte] using structural)
    have finalEq : CoreFinalTruth.coreFinalTruth
        (CoreCheckedStep.lift final []) =
          CoreFinalTruth.castToBool
            (final.stack.getLast?.getD []) := by
      simp [CoreFinalTruth.coreFinalTruth, CoreCheckedStep.lift]
    rw [finalEq] at sourceTruth
    exact sourceTruth.symm.trans accepted
  rw [program_final_split lock] at success
  exact CoreCheckedStep.checked_run_ending_multisig_true hashes
    (DynamicCheckedCertificate.wire lock) validKey verify _ initial final
    records success truth

/-- Successful dynamic byte execution reaches the fixed ten/ten count cells
and the empty NULLDUMMY cell.  This part is independent of the commitment
bytes and of the signature verdicts. -/
theorem byte_final_layout (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (initial beforeCheck final : ByteMachine.State)
    (prefixRun : ByteMachine.run hashes
      (DynamicCheckedCertificate.beforeFinalProgram lock) initial =
        some beforeCheck)
    (full : ByteMachine.run hashes
      (DynamicCheckedCertificate.program lock) initial = some final) :
    23 ≤ beforeCheck.stack.length ∧
    beforeCheck.stack[0]? = some [0x0a] ∧
    beforeCheck.stack[11]? = some [0x0a] ∧
    beforeCheck.stack[22]? = some [] := by
  let pre : List Op :=
    DynamicFullSerialized.priorOps lock.pin lock.nonce0
      lock.firstCommitment ++ [.checkmultisig] ++
    DynamicSignedChain.dataAndSignedProgram lock.nonce1
      lock.secondCommitment ++ FinalBonusSecond.bothBonusOps ++
    ByteLatePuzzle.lateOps
  have beforeSplit : DynamicCheckedCertificate.beforeFinalProgram lock =
      pre ++ ByteFinalCounts.finalSetup := by
    simp [pre, DynamicCheckedCertificate.beforeFinalProgram,
      DynamicWholeSource.beforeFinalCheckProgram,
      DynamicBonusChain.finalCheckPrefix, List.append_assoc]
  rw [beforeSplit, ByteMachine.run_append] at prefixRun
  cases hpre : ByteMachine.run hashes pre initial with
  | none => simp [hpre] at prefixRun
  | some under =>
      have setup : ByteMachine.run hashes ByteFinalCounts.finalSetup
          under = some beforeCheck := by simpa [hpre] using prefixRun
      obtain ⟨keyCount, sigCount⟩ :=
        ByteFinalCounts.accepted_final_setup_count_operands hashes
          under.stack under.outcomes under.ops beforeCheck setup
      rw [program_final_split lock, ByteMachine.run_append] at full
      have exactPrefix : ByteMachine.run hashes
          (pre ++ ByteFinalCounts.finalSetup) initial =
            some beforeCheck := by
        rw [ByteMachine.run_append, hpre]
        exact setup
      have last : ByteMachine.run hashes [.checkmultisig]
          beforeCheck = some final := by
        simpa [beforeSplit, exactPrefix] using full
      have dummy := ByteFinalCounts.successful_final_check_dummy_empty
        hashes beforeCheck final keyCount sigCount last
      have enough : 23 ≤ beforeCheck.stack.length := by
        obtain ⟨index, _⟩ := List.getElem?_eq_some_iff.mp dummy
        omega
      exact ⟨enough, keyCount, sigCount, dummy⟩

/-- The checked final scan on a parameterized lock supplies the specialized
ten-pair source evaluator at the *same reached stack* as the byte execution.
The checker remains an external key-parser/ECDSA function. -/
theorem checked_run_final_ten_eval (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ before : ByteMachine.State,
      ByteMachine.run hashes
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        ⟨initial.stack.reverse, records, initial.ops⟩ = some before ∧
      CoreMultisigEval.finalTenEval
        (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        before.stack = some true := by
  obtain ⟨before, previous, checkedPrefix, checkedFinal, recorded⟩ :=
    checked_run_final_scan_true hashes lock validKey verify
      initial final records success accepted
  have bytePrefix := CoreCheckedStep.checked_run_refines_byte_tail hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    initial before previous [true] checkedPrefix
  have reached : ByteMachine.run hashes
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      ⟨initial.stack.reverse, records, initial.ops⟩ =
        some ⟨before.stack.reverse, [true], before.ops⟩ := by
    rw [recorded]
    exact bytePrefix
  have whole := CoreCheckedStep.checked_run_refines_byte hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.program lock) initial final records success
  obtain ⟨enough, keys, sigs, dummy⟩ :=
    byte_final_layout hashes lock
      ⟨initial.stack.reverse, records, initial.ops⟩
      ⟨before.stack.reverse, [true], before.ops⟩
      ⟨final.stack.reverse, [], final.ops⟩ reached whole
  have finalEval := CoreCheckedStep.checkedMultisig_final_ten_eval
    (DynamicCheckedCertificate.wire lock) validKey verify
    before final keys sigs dummy (by simpa using enough) checkedFinal
  exact ⟨⟨before.stack.reverse, [true], before.ops⟩, reached, finalEval⟩

/-- A truthy checker-derived run of any parameterized Config A lock fixes
nine distinct second-round positions outside the DER-shaped-commitment setup
exception.  No final signature result, ten-pair scan, or source-site verdict
is supplied separately by the caller.  The result still assumes the Lean
checker and byte execution model, not compiled Bitcoin Core acceptance. -/
theorem checked_run_good_setup_nine_positions (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (width : ∀ i : Fin 150, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      DynamicWholeSource.extractTrace hashes
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment) ⟨stack, records, 0⟩ = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  let prior := DynamicFullSerialized.priorOps lock.pin lock.nonce0
    lock.firstCommitment
  let sourceInitial : CoreCheckedStep.State := ⟨stack.reverse, 0⟩
  let byteInitial : ByteMachine.State := ⟨stack, records, 0⟩
  let byteFinal : ByteMachine.State :=
    ⟨final.stack.reverse, [], final.ops⟩
  have byteRun : ByteMachine.run hashes
      (DynamicWholeSource.fullProgram prior lock.nonce1
        lock.secondCommitment) byteInitial = some byteFinal := by
    simpa [prior, byteInitial, byteFinal, sourceInitial,
      DynamicCheckedCertificate.program] using
      CoreCheckedStep.checked_run_refines_byte hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) sourceInitial final records
      success
  obtain ⟨sourceBefore, beforeRun, finalEval⟩ :=
    checked_run_final_ten_eval hashes lock validKey verify
      sourceInitial final records success accepted
  have finalGate : ∀ beforeCheck : ByteMachine.State,
      ByteMachine.run hashes
        (DynamicWholeSource.beforeFinalCheckProgram prior lock.nonce1
          lock.secondCommitment) byteInitial = some beforeCheck →
      CoreMultisigEval.finalTenEval
        (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        beforeCheck.stack = some true := by
    intro beforeCheck reached
    have same : beforeCheck = sourceBefore :=
      Option.some.inj (reached.symm.trans (by
        simpa [prior, byteInitial, sourceInitial,
          DynamicCheckedCertificate.beforeFinalProgram] using beforeRun))
    subst beforeCheck
    exact finalEval
  exact DynamicWholeSource.accepted_whole_good_setup_nine_positions
    hashes prior lock.nonce1 lock.secondCommitment width
      byteInitial byteFinal byteRun
      (DynamicCheckedCertificate.wire lock)
      (CoreFinalChecksigEval.checker validKey verify)
      finalGate noCommitmentDER

/-- For an arbitrary parameterized lock, a truthy checker-derived execution
either encounters the explicit DER-shaped second-round setup exception or
extracts nine distinct second-round positions. -/
theorem checked_run_der_exception_or_nine_positions (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (width : ∀ i : Fin 150, (lock.secondCommitment i).length = 20)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    (∃ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = true) ∨
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      DynamicWholeSource.extractTrace hashes
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment) ⟨stack, records, 0⟩ = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  by_cases bad : ∃ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = true
  · exact Or.inl bad
  · apply Or.inr
    have good : ∀ i : Fin 150,
        DERSyntax.valid (lock.secondCommitment i) = false := by
      intro i
      cases h : DERSyntax.valid (lock.secondCommitment i) with
      | false => rfl
      | true => exact False.elim (bad ⟨i, h⟩)
    exact checked_run_good_setup_nine_positions hashes lock width good
      stack validKey verify final records success accepted

end QSB.CoreCheckedDynamic
