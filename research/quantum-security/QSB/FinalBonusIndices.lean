import QSB.FinalBonusDER

/-!
Original-index accounting for two final-round bonus draws from the surviving
dummy pool. The signed trace and surviving IDs form a permutation of all 150
original HORS positions. This module is about that byte-model invariant; the
Core matching and DER premises that force both draws to be dummies are
separate obligations.
-/
namespace QSB.FinalBonusIndices
open ByteMachine
open FinalSignedLoop
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem two_bonus_ids_extend_seven
    (trace : List (Fin 150 × ByteMachine.Bytes))
    (ids : List (Fin 150))
    (traceLength : trace.length = 7)
    (permutation : List.Perm (trace.map Prod.fst ++ ids)
      (List.finRange 150))
    (first second : Nat)
    (firstWithin : first < ids.length)
    (secondWithin : second < (ids.eraseIdx first).length) :
    let a := ids[first]
    let b := (ids.eraseIdx first)[second]
    a ≠ b ∧
      a ∉ trace.map Prod.fst ∧
      b ∉ trace.map Prod.fst ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  classical
  let a := ids[first]
  let b := (ids.eraseIdx first)[second]
  have allNodup : (trace.map Prod.fst ++ ids).Nodup :=
    permutation.nodup_iff.mpr (List.nodup_finRange 150)
  obtain ⟨traceNodup, idsNodup, disjoint⟩ :=
    List.nodup_append.mp allNodup
  have erasedPerm : (a :: ids.eraseIdx first).Perm ids := by
    simpa [a] using List.getElem_cons_eraseIdx_perm firstWithin
  have aNotErased : a ∉ ids.eraseIdx first :=
    (List.nodup_cons.mp (erasedPerm.nodup_iff.mpr idsNodup)).1
  have bInErased : b ∈ ids.eraseIdx first :=
    List.getElem_mem secondWithin
  have aNeB : a ≠ b := by
    intro eq
    exact aNotErased (eq ▸ bInErased)
  have aInIds : a ∈ ids := List.getElem_mem firstWithin
  have bInIds : b ∈ ids := List.mem_of_mem_eraseIdx bInErased
  have aNotTrace : a ∉ trace.map Prod.fst := by
    intro opened
    exact disjoint a opened a aInIds rfl
  have bNotTrace : b ∉ trace.map Prod.fst := by
    intro opened
    exact disjoint b opened b bInIds rfl
  have bNotIn : b ∉ trace.map Prod.fst := bNotTrace
  have aNotIn : a ∉ b :: trace.map Prod.fst := by
    simp [aNeB, aNotTrace]
  have distinct : (a :: b :: trace.map Prod.fst).Nodup := by
    exact List.nodup_cons.mpr ⟨aNotIn,
      List.nodup_cons.mpr ⟨bNotIn, traceNodup⟩⟩
  have count : (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup distinct]
    simp [traceLength]
  exact ⟨aNeB, aNotTrace, bNotTrace, distinct, count⟩

/-- Under an explicit successful ten-pair final match and a syntax predicate
excluding the literal commitment bytes, an accepted byte-model run uses nine
distinct original HORS positions: seven signed openings and two bonus dummy
positions. This does not itself establish Core execution or hash security. -/
theorem matched_full_run_nine_positions (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool) (sigSyntax : Bytes → Prop)
    (verifySound : ∀ sig key, verify sig key = true → sigSyntax sig)
    (noCommitmentSyntax :
      ∀ id : Fin 150, ¬ sigSyntax (generatedCommitmentAt id))
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : State),
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      beforeCheck.stack[13]? = some (generatedDummyAt a) ∧
      beforeCheck.stack[12]? = some (generatedDummyAt b) ∧
      (∀ j : Nat, j < 7 → beforeCheck.stack[j + 14]? =
        (trace.map (fun p => generatedDummyAt p.1)).reverse[j]?) ∧
      beforeCheck.stack[21]? = some PoolRollInvariant.finalNonce ∧
      beforeCheck.stack[22]? = some [] ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      a ≠ b ∧ a ∉ trace.map Prod.fst ∧ b ∉ trace.map Prod.fst ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  obtain ⟨result, gathered, dummies, commitments, tail,
    outcomes, cost, trace, remainingIds, candidate, firstIndex, lastIndex,
    postFirst, postLast, beforeCheck,
    _prefixRun, _through, beforePrefix, _pool, traceCount, _distinct,
    hits, aligned, tracePerm, gatheredTrace,
    _candidateSource, _candidateUnopened,
    firstLower, firstUpper, lastLower, lastUpper,
    firstSource, lastSource, _beforeRun, lastSlot, firstSlot,
    gatheredSlots, nonceSlot, dummySlot,
    firstException, lastException⟩ :=
      FinalBonusSecond.accepted_whole_program_final_signature_origins
        hashes initial final accepted
  have enough : 22 ≤ beforeCheck.stack.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp dummySlot
    omega
  have success := matched beforeCheck beforePrefix
  have firstSyntax :=
    FinalBonusSecond.matched_final_signature_has_syntax verify
      sigSyntax verifySound beforeCheck.stack enough success 1 (by omega)
  have lastSyntax :=
    FinalBonusSecond.matched_final_signature_has_syntax verify
      sigSyntax verifySound beforeCheck.stack enough success 0 (by omega)
  have firstShallow : firstIndex < 152 := by
    by_contra h
    have atCap : firstIndex = 152 := by omega
    exact noCommitmentSyntax candidate
      (firstSyntax _ (firstException atCap))
  have lastShallow : lastIndex < 152 := by
    by_contra h
    have atCap : lastIndex = 152 := by omega
    exact noCommitmentSyntax candidate
      (lastSyntax _ (lastException ⟨firstShallow, atCap⟩))
  have idsLength : remainingIds.length = 143 := by
    have count := tracePerm.length_eq
    simp [List.length_append, traceCount] at count
    omega
  have firstWithin : firstIndex - 9 < remainingIds.length := by omega
  have erasedLength :
      (remainingIds.eraseIdx (firstIndex - 9)).length = 142 := by
    rw [List.length_eraseIdx_of_lt firstWithin, idsLength]
  have secondWithin : lastIndex - 10 <
      (remainingIds.eraseIdx (firstIndex - 9)).length := by omega
  have two := two_bonus_ids_extend_seven trace remainingIds traceCount
    tracePerm (firstIndex - 9) (lastIndex - 10)
    firstWithin secondWithin
  let a := remainingIds[firstIndex - 9]
  let b := (remainingIds.eraseIdx (firstIndex - 9))[lastIndex - 10]
  have firstAt : beforeCheck.stack[13]? = some (generatedDummyAt a) := by
    rw [firstSlot, firstSource]
    simp [firstShallow, aligned.dummyMap, a, firstWithin]
  have lastAt : beforeCheck.stack[12]? = some (generatedDummyAt b) := by
    rw [lastSlot, lastSource]
    simp [firstShallow, lastShallow, aligned.dummyMap,
      List.eraseIdx_map, b, secondWithin]
  have signedSlots : ∀ j : Nat, j < 7 →
      beforeCheck.stack[j + 14]? =
        (trace.map (fun p => generatedDummyAt p.1)).reverse[j]? := by
    intro j within
    rw [gatheredSlots j within, gatheredTrace]
  dsimp only at two
  exact ⟨trace, a, b, beforeCheck, beforePrefix, firstAt, lastAt,
    signedSlots, nonceSlot, dummySlot,
    traceCount, hits, two.1, two.2.1,
    two.2.2.1, two.2.2.2.1, two.2.2.2.2⟩

/-- The nine-position source result specialized to the literal lock's strict
DER predicate. The successful Core-shaped scan and parser-soundness premises
remain explicit; the result concerns the byte model, not actual Core spends. -/
theorem matched_full_run_nine_positions_der (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : State),
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      beforeCheck.stack[13]? = some (generatedDummyAt a) ∧
      beforeCheck.stack[12]? = some (generatedDummyAt b) ∧
      (∀ j : Nat, j < 7 → beforeCheck.stack[j + 14]? =
        (trace.map (fun p => generatedDummyAt p.1)).reverse[j]?) ∧
      beforeCheck.stack[21]? = some PoolRollInvariant.finalNonce ∧
      beforeCheck.stack[22]? = some [] ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      a ≠ b ∧ a ∉ trace.map Prod.fst ∧ b ∉ trace.map Prod.fst ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  apply matched_full_run_nine_positions hashes initial final accepted verify
    (fun sig => DERSyntax.valid sig = true) verifySound
  · intro id
    simp [FinalBonusDER.generated_final_commitments_not_der id]
  · exact matched

/-- Split the source-level Core obligation into the two facts it actually
needs: a successful ECDSA pair check has a nonempty signature, and its
encoding gate accepts that signature under `VERIFY_ALL`. Core-to-Lean
equivalence of the pair check and scan remains unproved. -/
theorem matched_full_run_nine_positions_verify_all (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool)
    (verifyNonempty : ∀ sig key, verify sig key = true → sig ≠ [])
    (verifyEncoding : ∀ sig key, verify sig key = true →
      DERSyntax.verifyAllEncoding sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : State),
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      beforeCheck.stack[13]? = some (generatedDummyAt a) ∧
      beforeCheck.stack[12]? = some (generatedDummyAt b) ∧
      (∀ j : Nat, j < 7 → beforeCheck.stack[j + 14]? =
        (trace.map (fun p => generatedDummyAt p.1)).reverse[j]?) ∧
      beforeCheck.stack[21]? = some PoolRollInvariant.finalNonce ∧
      beforeCheck.stack[22]? = some [] ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      a ≠ b ∧ a ∉ trace.map Prod.fst ∧ b ∉ trace.map Prod.fst ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  apply matched_full_run_nine_positions_der hashes initial final accepted
    verify ?_ matched
  intro sig key success
  have encoded := verifyEncoding sig key success
  rw [DERSyntax.verifyAllEncoding_nonempty sig
    (verifyNonempty sig key success)] at encoded
  exact encoded

end QSB.FinalBonusIndices
