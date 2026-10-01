import QSB.DynamicBonusTrace

/-!
Connect the parameterized data-push and seven-signed execution to both
literal bonus draws. The selected commitment, when a cap is reached, is
tracked to an original HORS position outside the seven opened positions.
-/
namespace QSB.DynamicBonusChain
open ByteMachine
open FinalSignedLoop
open DynamicSignedSource
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def finalCheckPrefix (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  DynamicSignedChain.dataAndSignedProgram nonce commitmentAt ++
    FinalBonusSecond.bothBonusOps ++
      (ByteLatePuzzle.lateOps ++ ByteFinalCounts.finalSetup)

theorem literal_final_check_prefix :
    finalCheckPrefix finalNonce generatedCommitmentAt =
      (ByteLayout.program.drop 447).take 432 := by decide

theorem final_round_program_eq (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) :
    DynamicFinalInit.finalRoundProgram nonce commitmentAt =
      DynamicSignedChain.dataAndSignedProgram nonce commitmentAt ++
        ByteLayout.program.drop 840 := by
  have suffix : ByteLayout.program.drop 749 =
      FinalSignedChain.allSignedBlocks ++ ByteLayout.program.drop 840 := by decide
  simp [DynamicFinalInit.finalRoundProgram,
    DynamicSignedChain.dataAndSignedProgram, suffix, List.append_assoc]

theorem accepted_data_signed_bonus_trace (hashes : Hashes)
    (nonce prior : Bytes) (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes
      (DynamicFinalInit.finalRoundProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) = some final) :
    ∃ (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150))
      (gathered dummies commitments tail' : List Bytes)
      (candidate : Fin 150) (firstIndex lastIndex : Nat)
      (postFirst postLast : State),
      DynamicFinalInit.AlignedPool commitmentAt remainingIds
        dummies commitments ∧
      run hashes (DynamicSignedChain.dataAndSignedProgram nonce commitmentAt)
        (State.mk (prior :: tail) outcomes cost) =
          some (State.mk
            (nextRawFrontN nonce prior gathered dummies commitments ++ tail')
            outcomes (cost + 63)) ∧
      run hashes FinalBonusSecond.firstBonusOps
        (State.mk
          (nextRawFrontN nonce prior gathered dummies commitments ++ tail')
          outcomes (cost + 63)) = some postFirst ∧
      run hashes FinalBonusSecond.bothBonusOps
        (State.mk
          (nextRawFrontN nonce prior gathered dummies commitments ++ tail')
          outcomes (cost + 63)) = some postLast ∧
      run hashes (ByteLayout.program.drop 850) postLast = some final ∧
      gathered.length = 7 ∧
      gathered = (trace.map (fun p => generatedDummyAt p.1)).reverse ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ remainingIds)
        (List.finRange 150) ∧
      FinalSignedChain.extractOrdered (List.finRange 7)
        (List.finRange 150) 0 tail = some trace ∧
      candidate ∉ trace.map Prod.fst ∧
      commitments[0]? = some (commitmentAt candidate) ∧
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 ∧
      postFirst.stack.head? =
        (if firstIndex < 152 then dummies[firstIndex - 9]?
          else commitments[0]?) ∧
      postLast.stack.head? =
        (if firstIndex < 152 then
          if lastIndex < 152 then
            (dummies.eraseIdx (firstIndex - 9))[lastIndex - 10]?
          else commitments[0]?
        else dummies[lastIndex - 10]?) ∧
      postLast.stack[1]? = postFirst.stack.head? ∧
      (firstIndex = 152 → postFirst.stack.head? =
        some (commitmentAt candidate)) ∧
      (firstIndex < 152 ∧ lastIndex = 152 →
        postLast.stack.head? = some (commitmentAt candidate)) ∧
      (∀ p : Nat, p ≤ 8 → postLast.stack[p + 2]? =
        (nextRawFrontN nonce prior gathered dummies commitments ++ tail')[p]?) := by
  rw [final_round_program_eq, run_append] at accepted
  cases signedRun : run hashes
      (DynamicSignedChain.dataAndSignedProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) with
  | none => simp [signedRun] at accepted
  | some afterSigned =>
      simp only [signedRun, Option.bind_some] at accepted
      unfold DynamicSignedChain.dataAndSignedProgram at signedRun
      rw [run_append] at signedRun
      cases dataRun : run hashes (DynamicFinalInit.dataOps nonce commitmentAt)
          (State.mk (prior :: tail) outcomes cost) with
      | none => simp [dataRun] at signedRun
      | some afterData =>
          have dataShape := DynamicFinalInit.accepted_data_shape hashes
            nonce commitmentAt (prior :: tail) outcomes cost afterData dataRun
          simp only [dataRun, Option.bind_some] at signedRun
          rw [dataShape] at signedRun
          obtain ⟨remainingIds, gathered, dummies, commitments, tail',
              trace, signedShape, poolShape, aligned, gatheredCount,
              traceCount, traceExtract, _remainingExtract, distinct,
              hits, permutation, gatheredTrace⟩ :=
            DynamicSignedChain.accepted_all_signed_blocks hashes
              commitmentAt nonce prior width priorWrong tail outcomes cost
              afterSigned signedRun
          rw [signedShape] at accepted
          obtain ⟨firstIndex, lastIndex, postFirst, postLast,
              firstRun, bothRun, firstLower, firstUpper,
              lastLower, lastUpper, firstSource, lastSource,
              firstCarried, shallow⟩ :=
            DynamicBonusTrace.accepted_bonus_suffix_source_trace hashes
              nonce prior gathered dummies commitments tail' poolShape
              gatheredCount outcomes (cost + 63) final accepted
          have nonempty : 0 < commitments.length := by
            rw [poolShape.commitmentCount]
            have dummyCount := poolShape.poolCount
            omega
          obtain ⟨candidate, candidateSource, unopened⟩ :=
            FinalBonusSecond.first_remaining_commitment_unopened_of_map
              commitmentAt trace remainingIds commitments
              aligned.commitmentMap permutation nonempty
          have suffixSplit : ByteLayout.program.drop 840 =
              FinalBonusSecond.bothBonusOps ++
                ByteLayout.program.drop 850 := by decide
          have tailRun : run hashes (ByteLayout.program.drop 850)
              postLast = some final := by
            rw [suffixSplit, run_append, bothRun] at accepted
            simpa using accepted
          refine ⟨trace, remainingIds, gathered, dummies, commitments, tail',
            candidate, firstIndex, lastIndex, postFirst, postLast, aligned,
            congrArg some signedShape, firstRun, bothRun, tailRun,
            gatheredCount, gatheredTrace, traceCount,
            distinct, hits, permutation, traceExtract, unopened,
            candidateSource, firstLower, firstUpper, lastLower, lastUpper,
            firstSource, lastSource, firstCarried, ?_, ?_, shallow⟩
          · intro capped
            simpa [capped, candidateSource] using firstSource
          · intro ⟨firstShallow, lastCap⟩
            simpa [firstShallow, lastCap, candidateSource] using lastSource

theorem accepted_postbonus_final_signature_origins (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (seven : gathered.length = 7)
    (postFirst postLast final : State)
    (firstCarried : postLast.stack[1]? = postFirst.stack.head?)
    (shallow : ∀ p : Nat, p ≤ 8 → postLast.stack[p + 2]? =
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[p]?)
    (suffix : run hashes (ByteLayout.program.drop 850)
      postLast = some final) :
    ∃ beforeCheck : State,
      run hashes (ByteLatePuzzle.lateOps ++ ByteFinalCounts.finalSetup)
        postLast = some beforeCheck ∧
      beforeCheck.stack[12]? = postLast.stack.head? ∧
      beforeCheck.stack[13]? = postFirst.stack.head? ∧
      (∀ j : Nat, j < 7 →
        beforeCheck.stack[j + 14]? = gathered[j]?) ∧
      beforeCheck.stack[21]? = some nonce ∧
      beforeCheck.stack[22]? = some [] := by
  obtain ⟨gatheredCells, nonceCell, dummyCell⟩ :=
    DynamicBonusSecond.signed_front_origins nonce prior gathered dummies commitments tail seven
  cases postLast with
  | mk postStack postOutcomes postCost =>
      obtain ⟨beforeCheck, prefixRun, origin⟩ :=
        ByteLatePuzzle.accepted_generated_final_witness_origins hashes
          postStack postOutcomes postCost final suffix
      refine ⟨beforeCheck, prefixRun, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.head?_eq_getElem?] using origin 0 (by omega)
      · have firstSlot : beforeCheck.stack[13]? = postStack[1]? := by
          simpa using origin 1 (by omega)
        exact firstSlot.trans firstCarried
      · intro j within
        have source := (origin (j + 2) (by omega)).trans
          ((shallow j (by omega)).trans (gatheredCells j within))
        simpa [Nat.add_assoc] using source
      · have source := (origin 9 (by omega)).trans
          ((shallow 7 (by omega)).trans nonceCell)
        simpa using source
      · have source := (origin 10 (by omega)).trans
          ((shallow 8 (by omega)).trans dummyCell)
        simpa using source

/-- A successful parameterized run reaches the final multisignature scan
with both bonus bytes in signature slots 12 and 13, followed by the seven
gathered dummy signatures, the arbitrary nonce, and the empty dummy. The
candidate is the first surviving commitment at an unopened original index.
This is an interpreter theorem; a matching cryptographic verifier is a
separate premise. -/
theorem accepted_data_signed_final_signature_origins (hashes : Hashes)
    (nonce prior : Bytes) (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes
      (DynamicFinalInit.finalRoundProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) = some final) :
    ∃ (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150))
      (gathered dummies commitments : List Bytes)
      (candidate : Fin 150) (firstIndex lastIndex : Nat)
      (beforeCheck : State),
      run hashes (finalCheckPrefix nonce commitmentAt)
        (State.mk (prior :: tail) outcomes cost) = some beforeCheck ∧
      DynamicFinalInit.AlignedPool commitmentAt remainingIds
        dummies commitments ∧
      List.Perm (trace.map Prod.fst ++ remainingIds)
        (List.finRange 150) ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      FinalSignedChain.extractOrdered (List.finRange 7)
        (List.finRange 150) 0 tail = some trace ∧
      gathered = (trace.map (fun p => generatedDummyAt p.1)).reverse ∧
      candidate ∉ trace.map Prod.fst ∧
      commitments[0]? = some (commitmentAt candidate) ∧
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 ∧
      beforeCheck.stack[12]? =
        (if firstIndex < 152 then
          if lastIndex < 152 then
            (dummies.eraseIdx (firstIndex - 9))[lastIndex - 10]?
          else commitments[0]?
        else dummies[lastIndex - 10]?) ∧
      beforeCheck.stack[13]? =
        (if firstIndex < 152 then dummies[firstIndex - 9]?
          else commitments[0]?) ∧
      (∀ j : Nat, j < 7 →
        beforeCheck.stack[j + 14]? = gathered[j]?) ∧
      beforeCheck.stack[21]? = some nonce ∧
      beforeCheck.stack[22]? = some [] ∧
      (firstIndex = 152 → beforeCheck.stack[13]? =
        some (commitmentAt candidate)) ∧
      (firstIndex < 152 ∧ lastIndex = 152 →
        beforeCheck.stack[12]? = some (commitmentAt candidate)) := by
  obtain ⟨trace, remainingIds, gathered, dummies, commitments, tail',
      candidate, firstIndex, lastIndex, postFirst, postLast,
      aligned, signedRun, _firstRun, bothRun, tailRun,
      gatheredCount, gatheredTrace, traceCount, distinct, hits,
      permutation, traceExtract, unopened, candidateSource,
      firstLower, firstUpper, lastLower, lastUpper,
      firstSource, lastSource, firstCarried, firstCap,
      lastCap, shallow⟩ :=
    accepted_data_signed_bonus_trace hashes nonce prior commitmentAt
      width priorWrong tail outcomes cost final accepted
  obtain ⟨beforeCheck, prefixRun, lastSlot, firstSlot, gatheredSlots,
      nonceSlot, dummySlot⟩ :=
    accepted_postbonus_final_signature_origins hashes nonce prior
      gathered dummies commitments tail' gatheredCount postFirst postLast
      final firstCarried shallow tailRun
  have checkRun : run hashes (finalCheckPrefix nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) = some beforeCheck := by
    unfold finalCheckPrefix
    rw [run_append, run_append, signedRun]
    simp only [Option.bind_some]
    rw [bothRun]
    simpa using prefixRun
  exact ⟨trace, remainingIds, gathered, dummies, commitments, candidate,
    firstIndex, lastIndex, beforeCheck, checkRun, aligned, permutation, traceCount,
    distinct, hits, traceExtract, gatheredTrace, unopened, candidateSource,
    firstLower, firstUpper, lastLower, lastUpper,
    lastSlot.trans lastSource, firstSlot.trans firstSource,
    gatheredSlots, nonceSlot, dummySlot,
    fun capped => firstSlot.trans (firstCap capped),
    fun capped => lastSlot.trans (lastCap capped)⟩

end QSB.DynamicBonusChain
