import QSB.ParameterizedFinalSubset

/-!
One source-shaped cross-pool deletion boundary: a 20-byte final nonce that
equals a second-round HORS commitment gives two original encoded pushes with
the same signature pattern. FindAndDelete removes both. A valid DER nonce of
this shape would also be a DER-shaped commitment, so the good-setup exception
in the final witness theorem is material. No real HORS preimage is constructed.
-/
namespace QSB.ParameterizedAliasDeletion
open ByteMachine ScriptCodeSelection

/-- If a second-round commitment aliases the fixed final nonce bytes, the
original parameterized wire has at least two copies of the nonce's canonical
push pattern. The source-shaped final deletion list always contains that
pattern, so its residual chunk list has none. This count is about complete
original opcode chunks, not arbitrary substrings. -/
theorem nonce_commitment_alias_removes_both
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (i : Fin 150) (same : secondCommitment i = nonce1)
    (ids : List (Fin 150)) :
    2 ≤ List.count (CorePushSerialize.pushPattern nonce1)
      (ParameterizedFindAndDelete.chunks pin nonce0 nonce1
        firstCommitment secondCommitment) ∧
    List.count (CorePushSerialize.pushPattern nonce1)
      (ParameterizedFinalSubset.residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment ids) = 0 ∧
    ParameterizedFinalSubset.deletedScript pin nonce0 nonce1
      firstCommitment secondCommitment ids =
      (ParameterizedFinalSubset.residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment ids).flatten := by
  let pattern := CorePushSerialize.pushPattern nonce1
  have commitmentMem : pattern ∈
      (DynamicFinalInit.commitmentPushes secondCommitment).map
        CorePushSerialize.pushPattern := by
    have indexMem : i ∈ List.finRange 150 := by simp
    have valueMem : secondCommitment i ∈
        (List.finRange 150).map secondCommitment :=
      List.mem_map_of_mem indexMem
    have pushMem : nonce1 ∈
        DynamicFinalInit.commitmentPushes secondCommitment := by
      rw [← same]
      simp [DynamicFinalInit.commitmentPushes,
        DynamicFinalInit.commitmentPool, valueMem]
    exact List.mem_map_of_mem pushMem
  have nonceMem : pattern ∈
      (([[], nonce1] : List Bytes).map
        CorePushSerialize.pushPattern) := by
    simp [pattern]
  have commitmentCount : 0 < List.count pattern
      ((DynamicFinalInit.commitmentPushes secondCommitment).map
        CorePushSerialize.pushPattern) := by
    by_contra notPositive
    have zero : List.count pattern
        ((DynamicFinalInit.commitmentPushes secondCommitment).map
          CorePushSerialize.pushPattern) = 0 := by omega
    exact (List.count_eq_zero.mp zero) commitmentMem
  have nonceCount : 0 < List.count pattern
      (([[], nonce1] : List Bytes).map
        CorePushSerialize.pushPattern) := by
    by_contra notPositive
    have zero : List.count pattern
        (([[], nonce1] : List Bytes).map
          CorePushSerialize.pushPattern) = 0 := by omega
    exact (List.count_eq_zero.mp zero) nonceMem
  have dataCount : 2 ≤ List.count pattern
      ((DynamicSerializedRound.dataValues nonce1 secondCommitment).map
        CorePushSerialize.pushPattern) := by
    simp only [DynamicSerializedRound.dataValues, List.map_append,
      List.count_append]
    omega
  have originalCount : 2 ≤ List.count pattern
      (ParameterizedFindAndDelete.chunks pin nonce0 nonce1
        firstCommitment secondCommitment) := by
    simp only [ParameterizedFindAndDelete.chunks,
      DynamicWireSource.fullChunks, DynamicSerializedRound.chunks,
      List.count_append]
    omega
  have selected : pattern ∈
      ParameterizedFinalSubset.selectedPatterns nonce1 ids := by
    exact List.mem_map_of_mem (by simp)
  have residualAbsent : pattern ∉
      ParameterizedFinalSubset.residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment ids := by
    intro present
    have omitted : pattern ∉
        ParameterizedFinalSubset.selectedPatterns nonce1 ids := by
      simpa only [decide_eq_true_eq] using
        (List.mem_filter.mp present).2
    exact omitted selected
  have residualCount : List.count pattern
      (ParameterizedFinalSubset.residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment ids) = 0 :=
    List.count_eq_zero.mpr residualAbsent
  refine ⟨originalCount, residualCount, ?_⟩
  change CoreFindAndDelete.runMany 880
      (DynamicFullSerialized.fullWire pin nonce0 nonce1
        firstCommitment secondCommitment)
      ((ids.map FinalSignedLoop.generatedDummyAt ++ [nonce1]).map
        CorePushSerialize.pushPattern) =
    stripEncodedChunks
      ((ids.map FinalSignedLoop.generatedDummyAt ++ [nonce1]).map
        CorePushSerialize.pushPattern)
      (ParameterizedFindAndDelete.chunks pin nonce0 nonce1
        firstCommitment secondCommitment)
  exact ParameterizedFindAndDelete.runMany_eq_chunk_filter
    pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short
    (ids.map FinalSignedLoop.generatedDummyAt ++ [nonce1])

/-- If the aliasing nonce passes the source DER predicate, this case lies in
the explicit second-round bad-setup event used by good-setup extraction. -/
theorem der_nonce_commitment_alias_is_bad_setup
    (nonce : Bytes) (secondCommitment : Fin 150 → Bytes)
    (i : Fin 150) (same : secondCommitment i = nonce)
    (valid : DERSyntax.valid nonce = true) :
    ¬(∀ id : Fin 150,
      DERSyntax.valid (secondCommitment id) = false) := by
  intro good
  have absent := good i
  rw [same, valid] at absent
  cases absent

end QSB.ParameterizedAliasDeletion
