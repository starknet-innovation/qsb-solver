import QSB.DynamicSignedSource

/-!
Parameterized list transitions for the seven final-round signed blocks.
The preceding source theorem rules out the nonce match for a *completed*
block. These lemmas recover the exact commitment/preimage/dummy erasures
needed to iterate that conclusion over arbitrary commitment bytes.
-/
namespace QSB.DynamicSignedTransition
open ByteMachine
open FinalSignedLoop
open DynamicSignedSource
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def preimageFrontN (nonce selected retained prior : Bytes)
    (gathered dummies commitments : List Bytes) (j : Nat) : List Bytes :=
  [selected] ++ signedPrefixN nonce retained gathered dummies ++
    commitments.eraseIdx j ++ [prior]

theorem aligned_pair_at (commitmentAt : Fin 150 → Bytes)
    (ids : List (Fin 150))
    (dummies commitments : List Bytes)
    (aligned : DynamicFinalInit.AlignedPool commitmentAt ids
      dummies commitments)
    (j : Nat) (within : j < ids.length) :
    dummies[j]? = some (generatedDummyAt ids[j]) ∧
    commitments[j]? = some (commitmentAt ids[j]) := by
  rcases aligned with ⟨dummyMap, commitmentMap⟩
  constructor
  · rw [dummyMap, List.getElem?_map,
      List.getElem?_eq_getElem within]
    rfl
  · rw [commitmentMap, List.getElem?_map,
      List.getElem?_eq_getElem within]
    rfl

theorem literal_preimage_front (selected retained prior : Bytes)
    (gathered dummies commitments : List Bytes) (j : Nat) :
    preimageFrontN finalNonce selected retained prior gathered dummies
      commitments j =
      preimageFront selected retained prior gathered dummies commitments j :=
  rfl

theorem commitment_roll_shape (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < commitments.length) :
    KeyRolls.rollAt (153 + j)
      (region nonce retained prior gathered dummies commitments tail) =
      some (commitments[j] ::
        signedPrefixN nonce retained gathered dummies ++
        commitments.eraseIdx j ++ prior :: tail) := by
  have moved := PoolRollInvariant.roll_from_middle
    (signedPrefixN nonce retained gathered dummies) commitments
    (prior :: tail) j within
  simpa [region, prefix_length nonce retained gathered dummies
    shape.poolCount, List.append_assoc] using moved

theorem paired_dummy_roll_shape (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (j : Nat) (within : j < dummies.length) :
    KeyRolls.rollAt (gathered.length + 2 + j)
      (gathered ++ [nonce, []] ++ dummies ++
        commitments ++ prior :: tail) =
      some (dummies[j] :: gathered ++ [nonce, []] ++
        dummies.eraseIdx j ++ commitments ++ prior :: tail) := by
  simpa [List.append_assoc] using
    (PoolRollInvariant.roll_at_pool gathered dummies
      (commitments ++ prior :: tail) nonce j within)

theorem preimage_front_length (nonce selected retained prior : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < commitments.length) :
    (preimageFrontN nonce selected retained prior gathered dummies
      commitments j).length = 304 - gathered.length := by
  have prefixLength := prefix_length nonce retained gathered dummies
    shape.poolCount
  simp only [preimageFrontN, List.length_append, List.length_cons,
    List.length_nil, List.length_eraseIdx, if_pos within]
  rw [prefixLength, shape.commitmentCount]
  have count := shape.poolCount
  have positive : 0 < dummies.length := by
    rw [shape.commitmentCount] at within
    omega
  omega

theorem accepted_preimage_pair_shape (hashes : Hashes) (k : Fin 7)
    (nonce selected retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (j : Nat) (within : j < commitments.length)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push (preimageIndex k), .roll]
      (State.mk
        (preimageFrontN nonce selected retained prior gathered dummies
          commitments j ++ tail) outcomes cost) = some after) :
    ∃ enough : 291 - gathered.length < tail.length,
      after = State.mk
        (tail[291 - gathered.length] ::
          preimageFrontN nonce selected retained prior gathered dummies
            commitments j ++ tail.eraseIdx (291 - gathered.length))
        outcomes (cost + 1) := by
  have frontLength := preimage_front_length nonce selected retained prior
    gathered dummies commitments shape j within
  have depth :
      (preimageFrontN nonce selected retained prior gathered dummies
        commitments j).length + (291 - gathered.length) =
        595 - 2 * k.val := by
    rw [frontLength, count]
    omega
  have parsed := generated_preimage_index_decodes k
  rw [← depth] at parsed
  exact accepted_push_roll_tail_shape hashes (preimageIndex k)
    (preimageFrontN nonce selected retained prior gathered dummies
      commitments j) tail outcomes cost after
    (291 - gathered.length) parsed accepted

/-- An in-range raw index addresses the same current position in the
commitment and dummy pools, independent of nonce and commitment bytes. -/
theorem inrange_paired_roll_transition (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (n : Fin 152) (low : gathered.length + 2 ≤ n.val) :
    ∃ (j : Nat) (dummyWithin : j < dummies.length)
      (commitmentWithin : j < commitments.length),
      n.val = gathered.length + 2 + j ∧
      KeyRolls.rollAt (151 - gathered.length + n.val)
        (region nonce retained prior gathered dummies commitments tail) =
        some (commitments[j]'commitmentWithin ::
          signedPrefixN nonce retained gathered dummies ++
          commitments.eraseIdx j ++ prior :: tail) ∧
      KeyRolls.rollAt n.val
        (gathered ++ [nonce, []] ++ dummies ++
          commitments.eraseIdx j ++ prior :: tail) =
        some (dummies[j]'dummyWithin :: gathered ++ [nonce, []] ++
          dummies.eraseIdx j ++ commitments.eraseIdx j ++ prior :: tail) ∧
      PoolShape (dummies[j]'dummyWithin :: gathered)
        (dummies.eraseIdx j) (commitments.eraseIdx j) := by
  let j := n.val - (gathered.length + 2)
  have within : j < dummies.length := by
    have count := shape.poolCount
    dsimp [j]
    omega
  have commitmentWithin : j < commitments.length := by
    rw [shape.commitmentCount]
    exact within
  have rawEq : n.val = gathered.length + 2 + j := by
    dsimp [j]
    omega
  have signedEq : 151 - gathered.length + n.val = 153 + j := by
    have count := shape.poolCount
    dsimp [j]
    omega
  refine ⟨j, within, commitmentWithin, rawEq, ?_, ?_,
    paired_draw_preserves_pool_shape gathered dummies commitments
      shape j within⟩
  · rw [signedEq]
    exact commitment_roll_shape nonce retained prior gathered dummies
      commitments tail shape j commitmentWithin
  · rw [rawEq]
    exact paired_dummy_roll_shape nonce prior gathered dummies
      (commitments.eraseIdx j) tail j within

theorem accepted_inrange_signed_suffix_shape (hashes : Hashes)
    (k : Fin 7) (nonce retained offset prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (n : Fin 152) (low : gathered.length + 2 ≤ n.val)
    (parsedOffset : ByteIndex.parseScriptNum offset =
      some (Int.ofNat (151 - gathered.length + n.val)))
    (parsedRetained : ByteIndex.parseScriptNum retained =
      some (Int.ofNat n.val))
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedSuffixOps k)
      (State.mk
        (offset :: region nonce retained prior gathered dummies commitments tail) outcomes cost) = some final) :
    ∃ (j : Nat) (dummyWithin : j < dummies.length)
      (commitmentWithin : j < commitments.length) (opening : Bytes),
      n.val = gathered.length + 2 + j ∧
      tail[291 - gathered.length]? = some opening ∧
      hashes.h160 opening = commitments[j]'commitmentWithin ∧
      PoolShape (dummies[j]'dummyWithin :: gathered)
        (dummies.eraseIdx j) (commitments.eraseIdx j) ∧
      final = State.mk
        (nextRawFrontN nonce prior (dummies[j]'dummyWithin :: gathered)
          (dummies.eraseIdx j) (commitments.eraseIdx j) ++
          tail.eraseIdx (291 - gathered.length))
        outcomes (cost + 5) := by
  obtain ⟨j, dummyWithin, commitmentWithin, rawEq,
      commitmentRoll, _dummyRoll, nextShape⟩ :=
    inrange_paired_roll_transition nonce retained prior gathered dummies
      commitments tail shape n low
  rw [generated_signed_suffix_ops] at accepted
  obtain ⟨afterCommit, commitStep, _, remaining⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll
      [.push (preimageIndex k), .roll, .hash160, .equalverify, .roll]
      (State.mk (offset :: region nonce retained prior gathered dummies commitments tail) outcomes cost) final accepted
  have offsetParsed : ByteIndex.parseScriptNum offset =
      some (Int.ofNat (151 - gathered.length + n.val)) := parsedOffset
  have afterCommitShape := accepted_roll_step_shape hashes offset
    (region nonce retained prior gathered dummies commitments tail)
    (commitments[j] :: signedPrefixN nonce retained gathered dummies ++
      commitments.eraseIdx j ++ prior :: tail)
    outcomes cost (151 - gathered.length + n.val) afterCommit
    offsetParsed (by
      rw [show 151 - gathered.length + n.val = 151 - gathered.length + n.val
        from rfl]
      exact commitmentRoll) commitStep
  rw [afterCommitShape] at remaining
  have frontEq :
      commitments[j] :: signedPrefixN nonce retained gathered dummies ++
        commitments.eraseIdx j ++ prior :: tail =
      preimageFrontN nonce commitments[j] retained prior gathered dummies commitments j ++ tail := by
    simp [preimageFrontN, List.append_assoc]
  rw [frontEq] at remaining
  have split :
      ([.push (preimageIndex k), .roll, .hash160,
        .equalverify, .roll] : List Op) =
      [.push (preimageIndex k), .roll] ++
        ([.hash160, .equalverify] ++ [.roll]) := rfl
  rw [split, run_append] at remaining
  cases preimage : run hashes [.push (preimageIndex k), .roll]
      (State.mk
        (preimageFrontN nonce commitments[j] retained prior gathered dummies commitments j ++ tail) outcomes (cost + 1)) with
  | none => simp [preimage] at remaining
  | some afterPreimage =>
      obtain ⟨enough, preimageShape⟩ :=
        accepted_preimage_pair_shape hashes k nonce commitments[j] retained
          prior gathered dummies commitments tail shape count j
          commitmentWithin outcomes (cost + 1) afterPreimage preimage
      simp only [preimage, Option.bind_some] at remaining
      rw [preimageShape] at remaining
      rw [run_append] at remaining
      let opening := tail[291 - gathered.length]
      let tailAfter := tail.eraseIdx (291 - gathered.length)
      let lower := signedPrefixN nonce retained gathered dummies ++
        commitments.eraseIdx j ++ prior :: tailAfter
      have hashInput :
          opening :: preimageFrontN nonce commitments[j] retained prior gathered dummies commitments j ++ tailAfter =
          opening :: commitments[j] :: lower := by
        simp [opening, lower, preimageFrontN, List.append_assoc]
      rw [hashInput] at remaining
      cases hashRun : run hashes [.hash160, .equalverify]
          (State.mk (opening :: commitments[j] :: lower)
            outcomes (cost + 2)) with
      | none => simp [hashRun] at remaining
      | some afterHash =>
          obtain ⟨hit, hashShape⟩ := accepted_hash_pair_shape hashes
            opening commitments[j] lower outcomes (cost + 2) afterHash
            hashRun
          simp only [hashRun, Option.bind_some] at remaining
          rw [hashShape] at remaining
          have lowerEq : lower = retained ::
              (gathered ++ [nonce, []] ++ dummies ++
                commitments.eraseIdx j ++ prior :: tailAfter) := by
            simp [lower, signedPrefixN, List.append_assoc]
          rw [lowerEq] at remaining
          obtain ⟨afterDummy, dummyStep, _, finished⟩ :=
            FirstAcceptedOrigin.run_cons_success hashes .roll []
              (State.mk (retained ::
                (gathered ++ [nonce, []] ++ dummies ++
                  commitments.eraseIdx j ++ prior :: tailAfter))
                outcomes (cost + 4)) final remaining
          have dummyRoll := paired_dummy_roll_shape nonce prior gathered dummies
            (commitments.eraseIdx j) tailAfter j dummyWithin
          have afterDummyShape := accepted_roll_step_shape hashes retained
            (gathered ++ [nonce, []] ++ dummies ++
              commitments.eraseIdx j ++ prior :: tailAfter)
            (dummies[j] :: gathered ++ [nonce, []] ++
              dummies.eraseIdx j ++ commitments.eraseIdx j ++
              prior :: tailAfter)
            outcomes (cost + 4) n.val afterDummy parsedRetained
            (by rw [rawEq]; exact dummyRoll) dummyStep
          rw [afterDummyShape] at finished
          simp [run] at finished
          cases finished
          have source : tail[291 - gathered.length]? = some opening :=
            List.getElem?_eq_getElem enough
          refine ⟨j, dummyWithin, commitmentWithin, opening,
            rawEq, source, hit, nextShape, ?_⟩
          simp [nextRawFrontN, tailAfter, List.append_assoc]

theorem accepted_signed_round_transition (hashes : Hashes) (k : Fin 7)
    (nonce prior : Bytes) (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (priorWrong : prior.length ≠ 20)
    (raw : Bytes) (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedRoundOps k)
      (State.mk (raw ::
        (nextRawFrontN nonce prior
          gathered dummies commitments ++ tail))
        outcomes cost) = some final) :
    ∃ (j : Nat) (dummyWithin : j < dummies.length)
      (commitmentWithin : j < commitments.length) (opening : Bytes),
      ByteIndex.parseScriptNum raw =
        some (Int.ofNat (gathered.length + 2 + j)) ∧
      tail[291 - gathered.length]? = some opening ∧
      hashes.h160 opening = commitments[j]'commitmentWithin ∧
      PoolShape (dummies[j]'dummyWithin :: gathered)
        (dummies.eraseIdx j) (commitments.eraseIdx j) ∧
      final = State.mk
        (nextRawFrontN nonce prior
          (dummies[j]'dummyWithin :: gathered)
          (dummies.eraseIdx j) (commitments.eraseIdx j) ++
          tail.eraseIdx (291 - gathered.length))
        outcomes (cost + 8) := by
  rw [signed_round_splits k, run_append] at accepted
  cases cap : run hashes (signedCapAddOps k)
      (State.mk (raw ::
        (nextRawFrontN nonce prior
          gathered dummies commitments ++ tail))
        outcomes cost) with
  | none => simp [cap] at accepted
  | some middle =>
      obtain ⟨source, operand, retained, offset, rawParsed,
          retainedEncoded, retainedParsed, offsetEncoded, middleShape⟩ :=
        accepted_signed_cap_add_shape hashes k raw
          (nextRawFrontN nonce prior
            gathered dummies commitments ++ tail)
          outcomes cost middle cap
      simp only [cap, Option.bind_some] at accepted
      rw [middleShape] at accepted
      have baseEq : retained ::
          (nextRawFrontN nonce prior
            gathered dummies commitments ++ tail) =
          region nonce retained prior gathered dummies commitments tail := by
        simp [region, signedPrefixN, nextRawFrontN, List.append_assoc]
      rw [baseEq] at accepted
      have suffix : run hashes (signedSuffixOps k)
          (State.mk (offset :: region nonce retained prior gathered dummies commitments tail)
            outcomes (cost + 3)) = some final := accepted
      rw [generated_signed_suffix_ops] at suffix
      obtain ⟨afterFirstRoll, firstRollStep, _, _rest⟩ :=
        FirstAcceptedOrigin.run_cons_success hashes .roll
          [.push (preimageIndex k), .roll, .hash160,
            .equalverify, .roll]
          (State.mk (offset :: region nonce retained prior gathered dummies commitments tail)
            outcomes (cost + 3)) final suffix
      obtain ⟨index, parsedOffset, nonnegative⟩ :=
        FinalSignedAccepted.accepted_roll_parses_nonnegative hashes offset
          (region nonce retained prior gathered dummies commitments tail)
          outcomes (cost + 3) afterFirstRoll firstRollStep
      have boundInt := signed_cap_add_index_bound k retained offset
        source operand index retainedEncoded retainedParsed offsetEncoded
        parsedOffset
      have indexEq : index = Int.ofNat index.toNat :=
        Int.eq_natCast_toNat.mpr nonnegative
      have indexBound : index.toNat ≤ 303 - gathered.length := by
        rw [count]
        rw [indexEq] at boundInt
        exact Int.ofNat_le.mp boundInt
      have parsedNat : ByteIndex.parseScriptNum offset =
          some (Int.ofNat index.toNat) := by
        rw [← indexEq]
        exact parsedOffset
      have suffixAccepted : run hashes (signedSuffixOps k)
          (State.mk (offset :: region nonce retained prior gathered
            dummies commitments tail) outcomes (cost + 3)) = some final := by
        rw [generated_signed_suffix_ops]
        exact suffix
      obtain ⟨j, opening, commitmentWithin, indexSource,
          commitmentHit⟩ :=
        accepted_full_suffix_is_commitment hashes k nonce retained prior
          offset gathered dummies commitments tail shape count priorWrong
          source operand index.toNat retainedEncoded retainedParsed
          offsetEncoded parsedNat outcomes (cost + 3) final suffixAccepted
      have indexValue : index = Int.ofNat (153 + j) := by
        rw [indexEq, indexSource]
      have deep : (153 : Int) ≤ index := by
        rw [indexValue]
        exact Int.ofNat_le.mpr
          (show (153 : Nat) ≤ 153 + j by omega)
      have belowCap : index < Int.ofNat (303 - k.val) := by
        have poolCount := shape.poolCount
        have commitmentCount := shape.commitmentCount
        have natural : 153 + j < 303 - k.val := by omega
        rw [indexValue]
        exact Int.ofNat_lt.mpr natural
      obtain ⟨n, sourceEq, low, operandEq, signedEq⟩ :=
        signed_commitment_depth_extract_raw k retained offset source
          operand index retainedEncoded retainedParsed offsetEncoded
          parsedOffset deep belowCap
      have parsedRetained : ByteIndex.parseScriptNum retained =
          some (Int.ofNat n.val) := by
        rw [operandEq, sourceEq] at retainedParsed
        exact retainedParsed
      have parsedSigned : ByteIndex.parseScriptNum offset =
          some (Int.ofNat (151 - gathered.length + n.val)) := by
        rw [signedEq, ← count] at parsedOffset
        exact parsedOffset
      obtain ⟨selected, dummyWithin, selectedWithin, actualOpening,
          rawIndex, openingSource, actualHit, nextShape, finalShape⟩ :=
        accepted_inrange_signed_suffix_shape hashes k nonce retained offset
          prior gathered dummies commitments
          tail shape count n (by rw [count]; exact low)
          parsedSigned parsedRetained outcomes (cost + 3) final accepted
      have rawValue : ByteIndex.parseScriptNum raw =
          some (Int.ofNat (gathered.length + 2 + selected)) := by
        rw [sourceEq] at rawParsed
        rw [rawIndex] at rawParsed
        exact rawParsed
      refine ⟨selected, dummyWithin, selectedWithin, actualOpening,
        rawValue, openingSource, actualHit, nextShape, ?_⟩
      simpa only [Nat.add_assoc] using finalShape

theorem accepted_signed_block_transition (hashes : Hashes) (k : Fin 7)
    (commitmentAt : Fin 150 → Bytes)
    (ids : List (Fin 150)) (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : DynamicFinalInit.AlignedPool commitmentAt ids
      dummies commitments)
    (count : gathered.length = k.val)
    (priorWrong : prior.length ≠ 20)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedBlockOps k)
      (State.mk (nextRawFrontN nonce prior
        gathered dummies commitments ++ tail) outcomes cost) =
        some final) :
    ∃ (raw opening : Bytes) (j : Nat)
      (dummyWithin : j < dummies.length)
      (commitmentWithin : j < commitments.length),
      tail[283]? = some raw ∧
      ByteIndex.parseScriptNum raw =
        some (Int.ofNat (gathered.length + 2 + j)) ∧
      (tail.eraseIdx 283)[291 - gathered.length]? = some opening ∧
      hashes.h160 opening = commitments[j]'commitmentWithin ∧
      PoolShape (dummies[j]'dummyWithin :: gathered)
        (dummies.eraseIdx j) (commitments.eraseIdx j) ∧
      DynamicFinalInit.AlignedPool commitmentAt (ids.eraseIdx j)
        (dummies.eraseIdx j) (commitments.eraseIdx j) ∧
      final = State.mk
        (nextRawFrontN nonce prior
          (dummies[j]'dummyWithin :: gathered)
          (dummies.eraseIdx j) (commitments.eraseIdx j) ++
          (tail.eraseIdx 283).eraseIdx (291 - gathered.length))
        outcomes (cost + 9) := by
  rw [generated_signed_block_ops k, run_append] at accepted
  cases fixed : run hashes [.push (fixedRawIndex k), .roll]
      (State.mk (nextRawFrontN nonce prior
        gathered dummies commitments ++ tail) outcomes cost) with
  | none => simp [fixed] at accepted
  | some afterFixed =>
      obtain ⟨enough, fixedShape⟩ :=
        accepted_fixed_raw_pair_dynamic hashes k nonce prior
          gathered dummies commitments tail shape count outcomes cost
          afterFixed fixed
      simp only [fixed, Option.bind_some] at accepted
      rw [fixedShape] at accepted
      obtain ⟨j, dummyWithin, commitmentWithin, opening,
          parsedRaw, preimageSource, hit, nextShape, roundShape⟩ :=
        accepted_signed_round_transition hashes k nonce prior gathered
          dummies commitments (tail.eraseIdx 283) shape count priorWrong
          tail[283] outcomes (cost + 1) final accepted
      refine ⟨tail[283], opening, j, dummyWithin, commitmentWithin,
        List.getElem?_eq_getElem enough, parsedRaw, preimageSource,
        hit, nextShape,
        DynamicFinalInit.paired_erasure_preserves_alignment commitmentAt ids dummies commitments
          aligned j, ?_⟩
      simpa only [Nat.add_assoc] using roundShape

end QSB.DynamicSignedTransition
