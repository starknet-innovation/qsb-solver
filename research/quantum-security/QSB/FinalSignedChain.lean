import QSB.FinalSignedLoop

/-!
Compose the checked final-round signed-block transition over a consecutive
sequence of generated blocks. The trace retains each original commitment
position and the opening actually consumed by HASH160/EQUALVERIFY.
-/
namespace QSB.FinalSignedChain
open ByteMachine
open FinalSignedLoop
open FinalSignedBoundary
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def orderedBlocks : Nat → List (Fin 7) → Prop
  | _, [] => True
  | start, k :: ks => k.val = start ∧ orderedBlocks (start + 1) ks

def blockProgram (ks : List (Fin 7)) : List Op :=
  ks.flatMap signedBlockOps

def allSignedBlocks : List Op := blockProgram (List.finRange 7)

theorem generated_all_signed_blocks :
    allSignedBlocks = (ByteLayout.program.drop 749).take 91 := by decide

theorem generated_blocks_ordered : orderedBlocks 0 (List.finRange 7) := by
  simp [orderedBlocks, List.finRange]

/-- Every successful consecutive sequence of locally reached signed blocks
produces one HASH160 opening for each selected original commitment. The
selected original indices plus the residual pool permute the input indices. -/
theorem accepted_ordered_blocks (hashes : Hashes) (result : Bool)
    (ks : List (Fin 7)) (start : Nat)
    (ordered : orderedBlocks start ks)
    (ids : List (Fin 150))
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : AlignedPool ids dummies commitments)
    (count : gathered.length = start)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (blockProgram ks)
      (State.mk (nextRawFront (boolBytes result)
        gathered dummies commitments ++ tail) outcomes cost) =
        some final) :
    ∃ (ids' : List (Fin 150))
      (gathered' dummies' commitments' tail' : List Bytes)
      (trace : List (Fin 150 × Bytes)),
      final = State.mk (nextRawFront (boolBytes result)
        gathered' dummies' commitments' ++ tail')
        outcomes (cost + 9 * ks.length) ∧
      PoolShape gathered' dummies' commitments' ∧
      AlignedPool ids' dummies' commitments' ∧
      gathered'.length = start + ks.length ∧
      trace.length = ks.length ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ ids') ids := by
  induction ks generalizing start ids gathered dummies commitments tail
      outcomes cost final with
  | nil =>
      simp [blockProgram, run] at accepted
      subst final
      refine ⟨ids, gathered, dummies, commitments, tail, [], ?_, shape,
        aligned, ?_, rfl, ?_, ?_⟩
      · simp
      · simpa using count
      · simp
      · simp
  | cons k rest ih =>
      obtain ⟨kEq, restOrdered⟩ := ordered
      have currentCount : gathered.length = k.val := count.trans kEq.symm
      change run hashes (signedBlockOps k ++ blockProgram rest)
        (State.mk (nextRawFront (boolBytes result)
          gathered dummies commitments ++ tail) outcomes cost) =
          some final at accepted
      rw [run_append] at accepted
      cases head : run hashes (signedBlockOps k)
          (State.mk (nextRawFront (boolBytes result)
            gathered dummies commitments ++ tail) outcomes cost) with
      | none => simp [head] at accepted
      | some middle =>
          obtain ⟨raw, opening, j, dummyWithin, commitmentWithin,
              rawSource, parsedRaw, openingSource, hashHit,
              nextShape, nextAligned, middleShape⟩ :=
            accepted_signed_block_transition hashes k result ids
              gathered dummies commitments tail shape aligned
              currentCount outcomes cost middle head
          have idWithin : j < ids.length := by
            rw [aligned.dummyMap] at dummyWithin
            simpa using dummyWithin
          let id : Fin 150 := ids[j]
          have originalHit : hashes.h160 opening =
              generatedCommitmentAt id := by
            obtain ⟨_, commitmentAt⟩ :=
              aligned_pair_at ids dummies commitments aligned j idWithin
            have selected : commitments[j]'commitmentWithin =
                generatedCommitmentAt id := by
              simpa [id, List.getElem?_eq_getElem commitmentWithin]
                using commitmentAt
            exact hashHit.trans selected
          simp only [head, Option.bind_some] at accepted
          rw [middleShape] at accepted
          obtain ⟨ids', gathered', dummies', commitments', tail',
              restTrace, finalShape, finalPool, finalAligned,
              finalCount, traceCount, traceHits, tracePerm⟩ :=
            ih (start + 1) restOrdered
              (ids.eraseIdx j) (dummies[j]'dummyWithin :: gathered)
              (dummies.eraseIdx j) (commitments.eraseIdx j)
              ((tail.eraseIdx 283).eraseIdx (291 - gathered.length))
              nextShape nextAligned (by simp [count])
              outcomes (cost + 9) final accepted
          refine ⟨ids', gathered', dummies', commitments', tail',
            (id, opening) :: restTrace, ?_, finalPool, finalAligned,
            ?_, ?_, ?_, ?_⟩
          · simpa [List.length_cons, Nat.mul_add, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using finalShape
          · simp only [List.length_cons]
            omega
          · simp [traceCount]
          · intro p hp
            rcases List.mem_cons.mp hp with rfl | later
            · exact originalHit
            · exact traceHits p later
          · have firstPerm : List.Perm (id :: ids.eraseIdx j) ids := by
              simpa [id] using List.getElem_cons_eraseIdx_perm idWithin
            simpa [List.map_cons, List.append_assoc] using
              (tracePerm.cons id).trans firstPerm

/-- Starting from the generated second-round pool, any successful execution
of all seven literal signed blocks yields seven distinct original HORS
positions, each matched to the opening consumed by its comparison. This
It starts at the block boundary; the earlier full-program prefix and the
later bonus/signature suffix are separate obligations. -/
theorem accepted_all_signed_blocks (hashes : Hashes) (result : Bool)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes allSignedBlocks
      (State.mk (FinalSignedAccepted.baseRegion (boolBytes result) tail)
        outcomes cost) = some final) :
    ∃ (ids' : List (Fin 150))
      (gathered' dummies' commitments' tail' : List Bytes)
      (trace : List (Fin 150 × Bytes)),
      final = State.mk (nextRawFront (boolBytes result)
        gathered' dummies' commitments' ++ tail')
        outcomes (cost + 63) ∧
      PoolShape gathered' dummies' commitments' ∧
      AlignedPool ids' dummies' commitments' ∧
      gathered'.length = 7 ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ ids') (List.finRange 150) := by
  have startShape : FinalSignedAccepted.baseRegion
      (boolBytes result) tail =
      nextRawFront (boolBytes result) []
        finalDummyPool finalCommitmentPool ++ tail := by
    simp [FinalSignedAccepted.baseRegion, nextRawFront,
      List.append_assoc]
  rw [startShape] at accepted
  obtain ⟨ids', gathered', dummies', commitments', tail', trace,
      finalShape, shape, aligned, gatheredCount, traceCount,
      traceHits, tracePerm⟩ :=
    accepted_ordered_blocks hashes result (List.finRange 7) 0
      generated_blocks_ordered (List.finRange 150) []
      finalDummyPool finalCommitmentPool tail
      generated_initial_pool_shape generated_initial_pool_alignment
      rfl outcomes cost final accepted
  have noDuplicates : (trace.map Prod.fst).Nodup := by
    have allNodup : (List.finRange 150).Nodup := List.nodup_finRange 150
    have combined := tracePerm.nodup_iff.mpr allNodup
    exact (List.nodup_append.mp combined).1
  refine ⟨ids', gathered', dummies', commitments', tail', trace,
    ?_, shape, aligned, ?_, ?_, noDuplicates, traceHits, tracePerm⟩
  · simpa using finalShape
  · simpa using gatheredCount
  · simpa using traceCount

theorem generated_whole_signed_boundary :
    ByteLayout.program =
      ByteLayout.program.take 446 ++
        (.checkmultisig :: (FinalSignedAccepted.finalRoundAllOps ++
          (allSignedBlocks ++ ByteLayout.program.drop 840))) := by
  decide

/-- An arbitrary successful full generated byte-model execution must consume
seven HASH160 openings against seven distinct original second-round HORS
commitment positions. It assumes only the byte model's supplied signature
outcomes; proving that the corresponding Bitcoin Core spend has the same
execution and valid signatures remains open. -/
theorem accepted_whole_program_final_signed_openings (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final) :
    ∃ trace : List (Fin 150 × Bytes),
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      ∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1 := by
  rw [generated_whole_signed_boundary, run_append] at accepted
  cases preRun : run hashes (ByteLayout.program.take 446) initial with
  | none => simp [preRun] at accepted
  | some beforeCheck =>
      simp only [preRun, Option.bind_some] at accepted
      obtain ⟨afterCheck, checkStep, _, suffix⟩ :=
        FirstAcceptedOrigin.run_cons_success hashes .checkmultisig
          (FinalSignedAccepted.finalRoundAllOps ++
            (allSignedBlocks ++ ByteLayout.program.drop 840))
          beforeCheck final accepted
      obtain ⟨result, tail, checkShape⟩ :=
        FinalSignedAccepted.successful_checkmultisig_result_shape
          hashes beforeCheck afterCheck checkStep
      cases afterCheck with
      | mk checkStack checkOutcomes checkCost =>
          change checkStack = boolBytes result :: tail at checkShape
          subst checkStack
          rw [run_append] at suffix
          cases init : run hashes FinalSignedAccepted.finalRoundAllOps
              (State.mk (boolBytes result :: tail)
                checkOutcomes checkCost) with
          | none => simp [init] at suffix
          | some afterInit =>
              have initShape :=
                FinalSignedAccepted.accepted_final_round_init_shape
                  hashes (boolBytes result :: tail) checkOutcomes
                  checkCost afterInit init
              simp only [init, Option.bind_some] at suffix
              rw [initShape] at suffix
              change run hashes (allSignedBlocks ++
                  ByteLayout.program.drop 840)
                (State.mk
                  (FinalSignedAccepted.baseRegion (boolBytes result) tail)
                  checkOutcomes checkCost) = some final at suffix
              rw [run_append] at suffix
              cases signed : run hashes allSignedBlocks
                  (State.mk
                    (FinalSignedAccepted.baseRegion (boolBytes result) tail)
                    checkOutcomes checkCost) with
              | none => simp [signed] at suffix
              | some afterSigned =>
                  obtain ⟨ids', gathered', dummies', commitments', tail',
                    trace, finalShape, shape, aligned, gatheredCount,
                    traceCount, noDuplicates, traceHits, _tracePerm⟩ :=
                    accepted_all_signed_blocks hashes result tail
                      checkOutcomes checkCost afterSigned signed
                  exact ⟨trace, traceCount, noDuplicates, traceHits⟩

/-- After seven checked signed draws, source depths nine and ten are the
first two surviving nonempty generated dummy signatures. -/
theorem seven_signed_bonus_sources_nonempty (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7) :
    ∃ nine ten : Bytes,
      nine ≠ [] ∧ ten ≠ [] ∧
      (nextRawFront prior gathered dummies commitments ++ tail)[9]? =
        some nine ∧
      (nextRawFront prior gathered dummies commitments ++ tail)[10]? =
        some ten := by
  have enough : 2 ≤ dummies.length := by
    have total := shape.poolCount
    omega
  let nine := dummies[0]'(by omega)
  let ten := dummies[1]'(by omega)
  have nineNonempty : nine ≠ [] := by
    have width := shape.dummyWidth nine (List.getElem_mem (by omega))
    intro empty
    rw [empty] at width
    simp at width
  have tenNonempty : ten ≠ [] := by
    have width := shape.dummyWidth ten (List.getElem_mem (by omega))
    intro empty
    rw [empty] at width
    simp at width
  have frontLength : (gathered ++ [finalNonce, []]).length = 9 := by
    simp [seven]
  have layout : nextRawFront prior gathered dummies commitments ++ tail =
      (gathered ++ [finalNonce, []]) ++
        (dummies ++ (commitments ++ (prior :: tail))) := by
    simp [nextRawFront, List.append_assoc]
  refine ⟨nine, ten, nineNonempty, tenNonempty, ?_, ?_⟩
  · rw [layout]
    rw [List.getElem?_append_right (by omega)]
    simp only [frontLength, Nat.sub_self]
    rw [List.getElem?_append_left (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  · rw [layout]
    rw [List.getElem?_append_right (by omega)]
    have atOne : 10 - (gathered ++ [finalNonce, []]).length = 1 := by
      omega
    rw [atOne, List.getElem?_append_left (by omega)]
    exact List.getElem?_eq_getElem (by omega)

end QSB.FinalSignedChain
