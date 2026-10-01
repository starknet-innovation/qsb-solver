import QSB.DynamicSignedTransition
import QSB.FinalSignedChain

/-!
Dynamic seven-block induction over the generated final-round suffix. Every
accepted transition consumes witness-tail indices and preserves paired pool
alignment for arbitrary twenty-byte commitments and nonce bytes.
-/
namespace QSB.DynamicSignedChain
open ByteMachine
open FinalSignedLoop
open FinalSignedChain
open DynamicSignedSource
open DynamicSignedTransition
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem accepted_ordered_blocks (hashes : Hashes)
    (commitmentAt : Fin 150 → Bytes) (nonce prior : Bytes)
    (priorWrong : prior.length ≠ 20)
    (ks : List (Fin 7)) (start : Nat)
    (ordered : orderedBlocks start ks)
    (ids : List (Fin 150))
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : DynamicFinalInit.AlignedPool commitmentAt ids dummies commitments)
    (count : gathered.length = start)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (blockProgram ks)
      (State.mk (nextRawFrontN nonce prior
        gathered dummies commitments ++ tail) outcomes cost) =
        some final) :
    ∃ (ids' : List (Fin 150))
      (gathered' dummies' commitments' tail' : List Bytes)
      (trace : List (Fin 150 × Bytes)),
      final = State.mk (nextRawFrontN nonce prior
        gathered' dummies' commitments' ++ tail')
        outcomes (cost + 9 * ks.length) ∧
      PoolShape gathered' dummies' commitments' ∧
      DynamicFinalInit.AlignedPool commitmentAt ids' dummies' commitments' ∧
      gathered'.length = start + ks.length ∧
      trace.length = ks.length ∧
      extractOrdered ks ids gathered.length tail = some trace ∧
      extractRemaining ks ids gathered.length tail = some ids' ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ ids') ids ∧
      gathered' = (trace.map (fun p => generatedDummyAt p.1)).reverse ++
        gathered := by
  induction ks generalizing start ids gathered dummies commitments tail
      outcomes cost final with
  | nil =>
      simp [blockProgram, run] at accepted
      subst final
      refine ⟨ids, gathered, dummies, commitments, tail, [], ?_, shape,
        aligned, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp
      · exact count
      · simp
      · simp
      · simp
  | cons k rest ih =>
      obtain ⟨kEq, restOrdered⟩ := ordered
      have currentCount : gathered.length = k.val := count.trans kEq.symm
      change run hashes (signedBlockOps k ++ blockProgram rest)
        (State.mk (nextRawFrontN nonce prior
          gathered dummies commitments ++ tail) outcomes cost) =
          some final at accepted
      rw [run_append] at accepted
      cases head : run hashes (signedBlockOps k)
          (State.mk (nextRawFrontN nonce prior
            gathered dummies commitments ++ tail) outcomes cost) with
      | none => simp [head] at accepted
      | some middle =>
          obtain ⟨raw, opening, j, dummyWithin, commitmentWithin,
              rawSource, parsedRaw, openingSource, hashHit,
              nextShape, nextAligned, middleShape⟩ :=
            DynamicSignedTransition.accepted_signed_block_transition hashes k commitmentAt ids nonce prior
              gathered dummies commitments tail shape aligned
              currentCount priorWrong outcomes cost middle head
          have idWithin : j < ids.length := by
            rw [aligned.dummyMap] at dummyWithin
            simpa using dummyWithin
          let id : Fin 150 := ids[j]
          have selectedDummy : dummies[j]'dummyWithin =
              generatedDummyAt id := by
            have source :=
              (DynamicSignedTransition.aligned_pair_at commitmentAt ids dummies commitments aligned j idWithin).1
            exact Option.some.inj
              ((List.getElem?_eq_getElem dummyWithin).symm.trans source)
          have originalHit : hashes.h160 opening =
              commitmentAt id := by
            obtain ⟨_, commitmentCell⟩ :=
              DynamicSignedTransition.aligned_pair_at commitmentAt ids dummies commitments aligned j idWithin
            have selected : commitments[j]'commitmentWithin =
                commitmentAt id := by
              simpa [id, List.getElem?_eq_getElem commitmentWithin]
                using commitmentCell
            exact hashHit.trans selected
          simp only [head, Option.bind_some] at accepted
          rw [middleShape] at accepted
          obtain ⟨ids', gathered', dummies', commitments', tail',
              restTrace, finalShape, finalPool, finalAligned,
              finalCount, traceCount, restExtract, restRemaining,
              traceHits, tracePerm,
              gatheredTrace⟩ :=
            ih (start + 1) restOrdered
              (ids.eraseIdx j) (dummies[j]'dummyWithin :: gathered)
              (dummies.eraseIdx j) (commitments.eraseIdx j)
              ((tail.eraseIdx 283).eraseIdx (291 - gathered.length))
              nextShape nextAligned (by simp [count])
              outcomes (cost + 9) final accepted
          refine ⟨ids', gathered', dummies', commitments', tail',
            (id, opening) :: restTrace, ?_, finalPool, finalAligned,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [List.length_cons, Nat.mul_add, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using finalShape
          · simp only [List.length_cons]
            omega
          · simp [traceCount]
          · have selectedId : ids[j]? = some id :=
              List.getElem?_eq_getElem idWithin
            have selectedOpening :
                (tail.eraseIdx 283)[291 - gathered.length]? =
                  some opening := openingSource
            have computedIndex :
                (Int.ofNat (gathered.length + 2 + j)).toNat -
                  (gathered.length + 2) = j := by
              have castBack :
                  (Int.ofNat (gathered.length + 2 + j)).toNat =
                    gathered.length + 2 + j :=
                Int.toNat_natCast (gathered.length + 2 + j)
              rw [castBack]
              omega
            have notBelow :
                ¬Int.ofNat (gathered.length + 2 + j) <
                  Int.ofNat (gathered.length + 2) := by
              simp
            have castAdd :
                (↑gathered.length : Int) + 2 + ↑j =
                  Int.ofNat (gathered.length + 2 + j) := by
              norm_cast
            have computedIndex' :
                ((↑gathered.length : Int) + 2 + ↑j).toNat -
                  (gathered.length + 2) = j := by
              rw [castAdd]
              exact computedIndex
            have restExtract' :
                extractOrdered rest (ids.eraseIdx j)
                  (gathered.length + 1)
                  ((tail.eraseIdx 283).eraseIdx
                    (291 - gathered.length)) = some restTrace := by
              simpa only [List.length_cons] using restExtract
            simp [extractOrdered, rawSource, parsedRaw, selectedOpening]
            simp only [computedIndex', selectedId,
              restExtract', Option.bind_some]
          · have selectedId : ids[j]? = some id :=
              List.getElem?_eq_getElem idWithin
            have computedIndex' :
                ((↑gathered.length : Int) + 2 + ↑j).toNat -
                  (gathered.length + 2) = j := by
              have castAdd :
                  (↑gathered.length : Int) + 2 + ↑j =
                    Int.ofNat (gathered.length + 2 + j) := by
                norm_cast
              rw [castAdd]
              have castBack :
                  (Int.ofNat (gathered.length + 2 + j)).toNat =
                    gathered.length + 2 + j :=
                Int.toNat_natCast (gathered.length + 2 + j)
              rw [castBack]
              omega
            have restRemaining' :
                extractRemaining rest (ids.eraseIdx j)
                  (gathered.length + 1)
                  ((tail.eraseIdx 283).eraseIdx
                    (291 - gathered.length)) = some ids' := by
              simpa only [List.length_cons] using restRemaining
            simp [extractRemaining, rawSource, parsedRaw,
              openingSource]
            simp only [computedIndex', selectedId,
              restRemaining', Option.bind_some]
          · intro p hp
            rcases List.mem_cons.mp hp with rfl | later
            · exact originalHit
            · exact traceHits p later
          · have firstPerm : List.Perm (id :: ids.eraseIdx j) ids := by
              simpa [id] using List.getElem_cons_eraseIdx_perm idWithin
            simpa [List.map_cons, List.append_assoc] using
              (tracePerm.cons id).trans firstPerm
          · simpa [List.map_cons, List.reverse_cons, List.append_assoc,
              selectedDummy] using gatheredTrace

theorem accepted_all_signed_blocks (hashes : Hashes)
    (commitmentAt : Fin 150 → Bytes) (nonce prior : Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes allSignedBlocks
      (State.mk ((nonce :: [] :: finalDummyPool ++
        DynamicFinalInit.commitmentPool commitmentAt ++ prior :: tail))
        outcomes cost) = some final) :
    ∃ (ids' : List (Fin 150))
      (gathered' dummies' commitments' tail' : List Bytes)
      (trace : List (Fin 150 × Bytes)),
      final = State.mk (nextRawFrontN nonce prior
        gathered' dummies' commitments' ++ tail')
        outcomes (cost + 63) ∧
      PoolShape gathered' dummies' commitments' ∧
      DynamicFinalInit.AlignedPool commitmentAt ids' dummies' commitments' ∧
      gathered'.length = 7 ∧
      trace.length = 7 ∧
      extractOrdered (List.finRange 7) (List.finRange 150) 0 tail =
        some trace ∧
      extractRemaining (List.finRange 7) (List.finRange 150) 0 tail =
        some ids' ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ ids') (List.finRange 150) ∧
      gathered' =
        (trace.map (fun p => generatedDummyAt p.1)).reverse := by
  have startShape : (nonce :: [] :: finalDummyPool ++
        DynamicFinalInit.commitmentPool commitmentAt ++ prior :: tail) =
      nextRawFrontN nonce prior []
        finalDummyPool (DynamicFinalInit.commitmentPool commitmentAt) ++
          tail := by
    simp [nextRawFrontN,
      List.append_assoc]
  rw [startShape] at accepted
  obtain ⟨ids', gathered', dummies', commitments', tail', trace,
      finalShape, shape, aligned, gatheredCount, traceCount,
      traceExtract, traceRemaining, traceHits, tracePerm,
      gatheredTrace⟩ :=
    accepted_ordered_blocks hashes commitmentAt nonce prior priorWrong (List.finRange 7) 0
      generated_blocks_ordered (List.finRange 150) []
      finalDummyPool (DynamicFinalInit.commitmentPool commitmentAt) tail
      (DynamicFinalInit.initial_pool_shape commitmentAt width)
      (DynamicFinalInit.initial_alignment commitmentAt)
      rfl outcomes cost final accepted
  have noDuplicates : (trace.map Prod.fst).Nodup := by
    have allNodup : (List.finRange 150).Nodup := List.nodup_finRange 150
    have combined := tracePerm.nodup_iff.mpr allNodup
    exact (List.nodup_append.mp combined).1
  refine ⟨ids', gathered', dummies', commitments', tail', trace,
    ?_, shape, aligned, ?_, ?_, ?_, ?_, noDuplicates, traceHits,
    tracePerm, ?_⟩
  · simpa using finalShape
  · simpa using gatheredCount
  · simpa using traceCount
  · simpa using traceExtract
  · simpa using traceRemaining
  · simpa using gatheredTrace

def dataAndSignedProgram (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  DynamicFinalInit.dataOps nonce commitmentAt ++ allSignedBlocks

theorem literal_data_and_signed_program :
    dataAndSignedProgram finalNonce generatedCommitmentAt =
      (ByteLayout.program.drop 447).take 393 := by decide

/-- The parameterized data pushes and all seven generated signed blocks,
executed from an arbitrary preceding witness tail, expose seven distinct
original commitment openings. This is a byte-model theorem: later bonus and
signature checks, the full dynamic builder correspondence, and compiled Core
acceptance are separate obligations. -/
theorem accepted_data_and_signed_openings (hashes : Hashes)
    (nonce prior : Bytes) (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (dataAndSignedProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) = some final) :
    ∃ (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150)),
      extractOrdered (List.finRange 7) (List.finRange 150) 0 tail =
        some trace ∧
      extractRemaining (List.finRange 7) (List.finRange 150) 0 tail =
        some remainingIds ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ remainingIds)
        (List.finRange 150) := by
  unfold dataAndSignedProgram at accepted
  rw [run_append] at accepted
  cases data : run hashes (DynamicFinalInit.dataOps nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) with
  | none => simp [data] at accepted
  | some afterData =>
      have dataShape := DynamicFinalInit.accepted_data_shape hashes nonce
        commitmentAt (prior :: tail) outcomes cost afterData data
      simp only [data, Option.bind_some] at accepted
      rw [dataShape] at accepted
      obtain ⟨ids', gathered', dummies', commitments', tail', trace,
          _finalShape, _shape, _aligned, _gatheredCount, traceCount,
          traceExtract, remainingExtract, noDuplicates, traceHits,
          tracePerm, _gatheredTrace⟩ :=
        accepted_all_signed_blocks hashes commitmentAt nonce prior width
          priorWrong tail outcomes cost final accepted
      exact ⟨trace, ids', traceExtract, remainingExtract, traceCount,
        noDuplicates, traceHits, tracePerm⟩

end QSB.DynamicSignedChain
