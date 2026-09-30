import QSB.FinalSignedAccepted

/-!
Structural invariant for the seven generated final-round signed selections.
The first selection's accepted-run origin is established in
`FinalSignedAccepted`; this module identifies the shared stack geometry that
must be preserved when lifting the remaining six selections.
-/
namespace QSB.FinalSignedLoop
open ByteMachine
open PoolRollInvariant
open FinalSignedBoundary
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def signedRoundOps (k : Fin 7) : List Op :=
  ByteLayout.program.drop (751 + 13 * k.val) |>.take 11

def signedGap (k : Fin 7) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (151 - k.val))).getD []

def preimageIndex (k : Fin 7) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (595 - 2 * k.val))).getD []

/-- All seven literal signed-selection blocks share the same MIN/ADD,
commitment-roll, preimage-roll, comparison, and dummy-roll pattern. -/
theorem generated_signed_round_ops :
    ∀ k : Fin 7, signedRoundOps k =
      [.push [0x98, 0x00], .min, .dup, .push (signedGap k), .add,
       .roll, .push (preimageIndex k), .roll, .hash160,
       .equalverify, .roll] := by decide

def signedCapAddOps (k : Fin 7) : List Op :=
  (signedRoundOps k).take 5

theorem generated_signed_cap_add_ops :
    ∀ k : Fin 7, signedCapAddOps k =
      [.push [0x98, 0x00], .min, .dup,
        .push (signedGap k), .add] := by decide

def signedSuffixOps (k : Fin 7) : List Op :=
  (signedRoundOps k).drop 5

theorem generated_signed_suffix_ops :
    ∀ k : Fin 7, signedSuffixOps k =
      [.roll, .push (preimageIndex k), .roll,
        .hash160, .equalverify, .roll] := by decide

theorem signed_round_splits :
    ∀ k : Fin 7,
      signedRoundOps k = signedCapAddOps k ++ signedSuffixOps k := by decide

def signedComparisonOps (k : Fin 7) : List Op :=
  (signedSuffixOps k).take 5

theorem generated_signed_comparison_ops :
    ∀ k : Fin 7, signedComparisonOps k =
      [.roll, .push (preimageIndex k), .roll,
        .hash160, .equalverify] := by decide

theorem signed_suffix_splits :
    ∀ k : Fin 7,
      signedSuffixOps k = signedComparisonOps k ++ [.roll] := by decide

def fixedRawIndex (k : Fin 7) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (586 - k.val))).getD []

theorem generated_fixed_raw_index_pairs :
    ∀ k : Fin 7,
      (ByteLayout.program.drop (749 + 13 * k.val)).take 2 =
        [.push (fixedRawIndex k), .roll] := by decide

theorem generated_fixed_raw_index_decodes :
    ∀ k : Fin 7,
      ByteIndex.parseScriptNum (fixedRawIndex k) =
        some (Int.ofNat (586 - k.val)) := by decide

def signedBlockOps (k : Fin 7) : List Op :=
  ByteLayout.program.drop (749 + 13 * k.val) |>.take 13

theorem generated_signed_block_ops :
    ∀ k : Fin 7,
      signedBlockOps k =
        [.push (fixedRawIndex k), .roll] ++ signedRoundOps k := by decide

theorem generated_signed_gap_decodes :
    ∀ k : Fin 7,
      ByteIndex.parseScriptNum (signedGap k) =
        some (Int.ofNat (151 - k.val)) := by decide

theorem generated_preimage_index_decodes :
    ∀ k : Fin 7,
      ByteIndex.parseScriptNum (preimageIndex k) =
        some (Int.ofNat (595 - 2 * k.val)) := by decide

theorem scriptnum_roundtrip_to_303 :
    ∀ n : Fin 304,
      (ByteIndex.encodeScriptNum (Int.ofNat n.val)).bind
        ByteIndex.parseScriptNum = some (Int.ofNat n.val) := by decide

theorem encoded_nonnegative_reparse_exact
    (source parsedValue : Int) (bytes : Bytes)
    (nonnegative : 0 ≤ source) (bounded : source ≤ 303)
    (encoded : ByteIndex.encodeScriptNum source = some bytes)
    (parsed : ByteIndex.parseScriptNum bytes = some parsedValue) :
    parsedValue = source := by
  let n : Fin 304 := ⟨source.toNat, by omega⟩
  have sourceEq : source = Int.ofNat n.val := by
    dsimp [n]
    exact Int.eq_natCast_toNat.mpr nonnegative
  have roundtrip := scriptnum_roundtrip_to_303 n
  rw [← sourceEq, encoded] at roundtrip
  simp [parsed] at roundtrip
  exact roundtrip

/-- Within the generated signed-round arithmetic range, a successfully
reparsed ScriptNum encoding cannot exceed its pre-encoding upper bound.
Negative encodings may fail to reparse, but any that do remain nonpositive. -/
theorem encoded_reparse_preserves_upper_bound
    (source parsedValue limit : Int) (bytes : Bytes)
    (bounded : source ≤ limit) (limitNonnegative : 0 ≤ limit)
    (limitSmall : limit ≤ 303)
    (encoded : ByteIndex.encodeScriptNum source = some bytes)
    (parsed : ByteIndex.parseScriptNum bytes = some parsedValue) :
    parsedValue ≤ limit := by
  by_cases negative : source < 0
  · have nonpositive :=
      ByteIndexSign.negative_encoding_never_parses_positive
        source bytes negative encoded parsedValue parsed
    omega
  · let n : Fin 304 := ⟨source.toNat, by omega⟩
    have sourceEq : source = Int.ofNat n.val := by
      dsimp [n]
      exact Int.eq_natCast_toNat.mpr (by omega)
    have roundtrip := scriptnum_roundtrip_to_303 n
    rw [← sourceEq, encoded] at roundtrip
    simp [parsed] at roundtrip
    omega

/-- The seven generated MIN/ADD gaps cannot produce a successfully parsed
signed-roll depth beyond the cap source, even if intermediate ScriptNums are
nonminimal or negative. -/
theorem signed_cap_add_index_bound (k : Fin 7)
    (retained offset : Bytes) (source operand index : Int)
    (retainedEncoded :
      ByteIndex.encodeScriptNum (min (152 : Int) source) = some retained)
    (retainedParsed : ByteIndex.parseScriptNum retained = some operand)
    (offsetEncoded : ByteIndex.encodeScriptNum
      (Int.ofNat (151 - k.val) + operand) = some offset)
    (offsetParsed : ByteIndex.parseScriptNum offset = some index) :
    index ≤ Int.ofNat (303 - k.val) := by
  have minBound : min (152 : Int) source ≤ 152 := min_le_left _ _
  have operandBound := encoded_reparse_preserves_upper_bound
    (min (152 : Int) source) operand 152 retained minBound
    (by omega) (by omega) retainedEncoded retainedParsed
  have sumBound : Int.ofNat (151 - k.val) + operand ≤
      Int.ofNat (303 - k.val) := by
    have small := k.isLt
    simp only [Int.ofNat_eq_natCast]
    rw [Nat.cast_sub (by omega : k.val ≤ 151),
      Nat.cast_sub (by omega : k.val ≤ 303)]
    omega
  exact encoded_reparse_preserves_upper_bound
    (Int.ofNat (151 - k.val) + operand) index
    (Int.ofNat (303 - k.val)) offset sumBound
    (by simpa only [Int.ofNat_eq_natCast] using
      (Int.natCast_nonneg (303 - k.val)))
    (by show Int.ofNat (303 - k.val) ≤ Int.ofNat 303
        exact Int.ofNat_le.mpr (by omega))
    offsetEncoded offsetParsed

/-- A successful comparison in the commitment-depth window forces the raw
index into the corresponding nonnegative in-range window. This excludes
negative raw values and the MIN-capped value without assuming minimal raw
encoding. -/
theorem signed_commitment_depth_extract_raw (k : Fin 7)
    (retained offset : Bytes) (source operand index : Int)
    (retainedEncoded :
      ByteIndex.encodeScriptNum (min (152 : Int) source) = some retained)
    (retainedParsed : ByteIndex.parseScriptNum retained = some operand)
    (offsetEncoded : ByteIndex.encodeScriptNum
      (Int.ofNat (151 - k.val) + operand) = some offset)
    (offsetParsed : ByteIndex.parseScriptNum offset = some index)
    (deep : 153 ≤ index)
    (belowCap : index < Int.ofNat (303 - k.val)) :
    ∃ n : Fin 152,
      source = Int.ofNat n.val ∧
      k.val + 2 ≤ n.val ∧
      operand = source ∧
      index = Int.ofNat (151 - k.val + n.val) := by
  have gapNonnegative : 0 ≤ Int.ofNat (151 - k.val) :=
    Int.natCast_nonneg _
  have gapSmall : Int.ofNat (151 - k.val) ≤ 303 := by
    show Int.ofNat (151 - k.val) ≤ Int.ofNat 303
    exact Int.ofNat_le.mpr (by omega)
  by_cases negative : source < 0
  · have retainedSource : ByteIndex.encodeScriptNum source =
        some retained := by
      have capped : min (152 : Int) source = source :=
        min_eq_right (by omega)
      simpa [capped] using retainedEncoded
    have nonpositive :=
      ByteIndexSign.negative_encoding_never_parses_positive
        source retained negative retainedSource operand retainedParsed
    have offsetBound := encoded_reparse_preserves_upper_bound
      (Int.ofNat (151 - k.val) + operand) index
      (Int.ofNat (151 - k.val)) offset (by omega)
      gapNonnegative gapSmall offsetEncoded offsetParsed
    have gapBelow : Int.ofNat (151 - k.val) < 153 := by
      show Int.ofNat (151 - k.val) < Int.ofNat 153
      exact Int.ofNat_lt.mpr (by omega)
    omega
  by_cases cappedRaw : 152 ≤ source
  · have retained152 : ByteIndex.encodeScriptNum (152 : Int) =
        some retained := by
      have capped : min (152 : Int) source = 152 :=
        min_eq_left (by omega)
      simpa [capped] using retainedEncoded
    have operandEq : operand = 152 :=
      encoded_nonnegative_reparse_exact 152 operand retained
        (by omega) (by omega) retained152 retainedParsed
    have sumNonnegative : 0 ≤ Int.ofNat (151 - k.val) + operand := by
      omega
    have sumSmall : Int.ofNat (151 - k.val) + operand ≤ 303 := by
      have gapBound : Int.ofNat (151 - k.val) ≤ 151 := by
        show Int.ofNat (151 - k.val) ≤ Int.ofNat 151
        exact Int.ofNat_le.mpr (by omega)
      omega
    have indexEq := encoded_nonnegative_reparse_exact
      (Int.ofNat (151 - k.val) + operand) index offset
      sumNonnegative sumSmall offsetEncoded offsetParsed
    have capEq : Int.ofNat (151 - k.val) + 152 =
        Int.ofNat (303 - k.val) := by
      have small := k.isLt
      simp only [Int.ofNat_eq_natCast]
      rw [Nat.cast_sub (by omega : k.val ≤ 151),
        Nat.cast_sub (by omega : k.val ≤ 303)]
      omega
    rw [operandEq, capEq] at indexEq
    omega
  · have inrange : 0 ≤ source ∧ source < 152 := by omega
    have retainedSource : ByteIndex.encodeScriptNum source =
        some retained := by
      have capped : min (152 : Int) source = source :=
        min_eq_right (by omega)
      simpa [capped] using retainedEncoded
    have operandEq : operand = source :=
      encoded_nonnegative_reparse_exact source operand retained
        inrange.1 (by omega) retainedSource retainedParsed
    have sumNonnegative : 0 ≤ Int.ofNat (151 - k.val) + operand := by
      omega
    have sumSmall : Int.ofNat (151 - k.val) + operand ≤ 303 := by
      have gapBound : Int.ofNat (151 - k.val) ≤ 151 := by
        show Int.ofNat (151 - k.val) ≤ Int.ofNat 151
        exact Int.ofNat_le.mpr (by omega)
      omega
    have indexEq := encoded_nonnegative_reparse_exact
      (Int.ofNat (151 - k.val) + operand) index offset
      sumNonnegative sumSmall offsetEncoded offsetParsed
    let n : Fin 152 := ⟨source.toNat, by omega⟩
    have sourceEq : source = Int.ofNat n.val := by
      dsimp [n]
      exact Int.eq_natCast_toNat.mpr inrange.1
    have gapEq : Int.ofNat (151 - k.val) =
        (151 : Int) - Int.ofNat k.val := by
      have small := k.isLt
      simp only [Int.ofNat_eq_natCast]
      exact Nat.cast_sub (by omega : k.val ≤ 151)
    have lower : k.val + 2 ≤ n.val := by
      rw [operandEq, gapEq, sourceEq] at indexEq
      simp only [Int.ofNat_eq_natCast] at indexEq deep
      have small := k.isLt
      dsimp [n] at indexEq ⊢
      omega
    have finalIndex : index = Int.ofNat (151 - k.val + n.val) := by
      rw [operandEq, sourceEq] at indexEq
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using indexEq
    exact ⟨n, sourceEq, lower, operandEq, finalIndex⟩

/-- Invert any successful generated MIN/ADD prefix. Its retained and offset
bytes arise from the actual ScriptNum serializer, even if the raw input is
nonminimal or the serializer subsequently fails to round-trip exactly. -/
theorem accepted_signed_cap_add_shape (hashes : Hashes) (k : Fin 7)
    (raw : Bytes) (base : List Bytes)
    (outcomes : List Bool) (cost : Nat) (middle : State)
    (accepted : run hashes (signedCapAddOps k)
      (State.mk (raw :: base) outcomes cost) = some middle) :
    ∃ (source operand : Int) (retained offset : Bytes),
      ByteIndex.parseScriptNum raw = some source ∧
      ByteIndex.encodeScriptNum (min (152 : Int) source) = some retained ∧
      ByteIndex.parseScriptNum retained = some operand ∧
      ByteIndex.encodeScriptNum
        (Int.ofNat (151 - k.val) + operand) = some offset ∧
      middle = State.mk (offset :: retained :: base)
        outcomes (cost + 3) := by
  rw [generated_signed_cap_add_ops] at accepted
  obtain ⟨afterPush, pushed, _, afterPushRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push [0x98, 0x00])
      [.min, .dup, .push (signedGap k), .add]
      (State.mk (raw :: base) outcomes cost) middle accepted
  have pushShape := ByteFinalCounts.push_success_shape hashes
    [0x98, 0x00] (raw :: base) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨afterMin, minStep, _, afterMinRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .min
      [.dup, .push (signedGap k), .add]
      (State.mk ([0x98, 0x00] :: raw :: base) outcomes cost)
      middle afterPushRun
  have minBudget : cost + 1 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 1 > 201 := by omega
    unfold step at minStep
    simp [tooHigh] at minStep
  unfold step at minStep
  simp [show ¬cost + 1 > 201 by omega,
    ByteIndex.positive_152] at minStep
  cases parsedRaw : ByteIndex.parseScriptNum raw with
  | none => simp [parsedRaw] at minStep
  | some source =>
      simp [parsedRaw] at minStep
      cases encodedRetained :
          ByteIndex.encodeScriptNum (min (152 : Int) source) with
      | none => simp [encodedRetained] at minStep
      | some retained =>
          simp [encodedRetained] at minStep
          cases minStep
          obtain ⟨afterDup, dupStep, _, afterDupRun⟩ :=
            FirstAcceptedOrigin.run_cons_success hashes .dup
              [.push (signedGap k), .add]
              (State.mk (retained :: base) outcomes (cost + 1))
              middle afterMinRun
          have dupBudget : cost + 2 ≤ 201 := by
            by_contra exceeded
            have tooHigh : cost + 2 > 201 := by omega
            unfold step at dupStep
            simp [tooHigh] at dupStep
          have dupExact : step hashes .dup
              (State.mk (retained :: base) outcomes (cost + 1)) =
              some (State.mk (retained :: retained :: base)
                outcomes (cost + 2)) := by
            unfold step
            simp [show ¬cost + 2 > 201 by omega]
          rw [dupExact] at dupStep
          cases dupStep
          obtain ⟨afterGap, gapStep, _, afterGapRun⟩ :=
            FirstAcceptedOrigin.run_cons_success hashes
              (.push (signedGap k)) [.add]
              (State.mk (retained :: retained :: base)
                outcomes (cost + 2)) middle afterDupRun
          have gapShape := ByteFinalCounts.push_success_shape hashes
            (signedGap k) (retained :: retained :: base)
            outcomes (cost + 2) afterGap gapStep
          subst afterGap
          obtain ⟨afterAdd, addStep, _, finished⟩ :=
            FirstAcceptedOrigin.run_cons_success hashes .add []
              (State.mk (signedGap k :: retained :: retained :: base)
                outcomes (cost + 2)) middle afterGapRun
          have addBudget : cost + 3 ≤ 201 := by
            by_contra exceeded
            have tooHigh : cost + 3 > 201 := by omega
            unfold step at addStep
            simp [tooHigh] at addStep
          unfold step at addStep
          simp [show ¬cost + 3 > 201 by omega,
            generated_signed_gap_decodes k] at addStep
          cases parsedRetained : ByteIndex.parseScriptNum retained with
          | none => simp [parsedRetained] at addStep
          | some operand =>
              simp [parsedRetained] at addStep
              cases encodedOffset : ByteIndex.encodeScriptNum
                  (((151 - k.val : Nat) : Int) + operand) with
              | none => simp [encodedOffset] at addStep
              | some offset =>
                  simp [encodedOffset] at addStep
                  cases addStep
                  simp [run] at finished
                  cases finished
                  exact ⟨source, operand, retained, offset, rfl,
                    encodedRetained, parsedRetained,
                    (by simpa only [Int.ofNat_eq_natCast] using encodedOffset),
                    rfl⟩

structure PoolShape (gathered dummies commitments : List Bytes) : Prop where
  poolCount : gathered.length + dummies.length = 150
  commitmentCount : commitments.length = dummies.length
  gatheredWidth : ∀ x ∈ gathered, x.length = 9
  dummyWidth : ∀ x ∈ dummies, x.length = 9
  commitmentWidth : ∀ x ∈ commitments, x.length = 20

def generatedDummyAt (i : Fin 150) : Bytes :=
  finalDummyPool[i.val]'(by
    rw [generated_dummy_pool_length]
    exact i.isLt)

/-- The literal generated lock uses distinct dummy-signature byte strings at
all 150 original positions. This is a fixture fact, independent of HASH160
commitment collisions; other generated setups need their own proof. -/
theorem generated_dummy_pool_nodup : finalDummyPool.Nodup := by decide

theorem generatedDummyAt_injective : Function.Injective generatedDummyAt := by
  intro i j same
  apply Fin.ext
  exact (generated_dummy_pool_nodup.getElem_inj_iff).mp same

def generatedCommitmentAt (i : Fin 150) : Bytes :=
  finalCommitmentPool[i.val]'(by
    rw [generated_commitment_pool_length]
    exact i.isLt)

/-- A common surviving original-position list records that the dummy and
commitment pools have undergone exactly the same prior erasures. -/
structure AlignedPool (ids : List (Fin 150))
    (dummies commitments : List Bytes) : Prop where
  dummyMap : dummies = ids.map generatedDummyAt
  commitmentMap : commitments = ids.map generatedCommitmentAt

theorem generated_initial_pool_alignment :
    AlignedPool (List.finRange 150) finalDummyPool finalCommitmentPool := by
  constructor <;> decide

theorem paired_erasure_preserves_alignment
    (ids : List (Fin 150)) (dummies commitments : List Bytes)
    (aligned : AlignedPool ids dummies commitments) (j : Nat) :
    AlignedPool (ids.eraseIdx j)
      (dummies.eraseIdx j) (commitments.eraseIdx j) := by
  rcases aligned with ⟨dummyMap, commitmentMap⟩
  constructor
  · rw [dummyMap, List.eraseIdx_map]
  · rw [commitmentMap, List.eraseIdx_map]

theorem aligned_pair_at (ids : List (Fin 150))
    (dummies commitments : List Bytes)
    (aligned : AlignedPool ids dummies commitments)
    (j : Nat) (within : j < ids.length) :
    dummies[j]? = some (generatedDummyAt ids[j]) ∧
    commitments[j]? = some (generatedCommitmentAt ids[j]) := by
  rcases aligned with ⟨dummyMap, commitmentMap⟩
  constructor
  · rw [dummyMap, List.getElem?_map,
      List.getElem?_eq_getElem within]
    rfl
  · rw [commitmentMap, List.getElem?_map,
      List.getElem?_eq_getElem within]
    rfl

theorem generated_initial_pool_shape :
    PoolShape [] finalDummyPool finalCommitmentPool := by
  refine ⟨?_, ?_, ?_, generated_dummy_pool_width,
    generated_commitment_pool_width⟩
  · simpa using generated_dummy_pool_length
  · rw [generated_commitment_pool_length, generated_dummy_pool_length]
  · simp

/-- A paired commitment and dummy draw at the same current pool position
preserves the widths and count equation for the next signed selection. -/
theorem paired_draw_preserves_pool_shape
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < dummies.length) :
    PoolShape (dummies[j] :: gathered)
      (dummies.eraseIdx j) (commitments.eraseIdx j) := by
  have commitmentWithin : j < commitments.length := by
    rw [shape.commitmentCount]
    exact within
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_eraseIdx, if_pos within]
    have count := shape.poolCount
    omega
  · simp only [List.length_eraseIdx, if_pos within,
      if_pos commitmentWithin]
    rw [shape.commitmentCount]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | old
    · exact shape.dummyWidth dummies[j] (List.getElem_mem within)
    · exact shape.gatheredWidth x old
  · intro x hx
    exact shape.dummyWidth x (List.mem_of_mem_eraseIdx hx)
  · intro x hx
    exact shape.commitmentWidth x (List.mem_of_mem_eraseIdx hx)

def signedPrefix (retained : Bytes) (gathered dummies : List Bytes) :
    List Bytes :=
  [retained] ++ gathered ++ [finalNonce, []] ++ dummies

def signedRegion (retained : Bytes) (gathered dummies commitments : List Bytes)
    (prior : Bytes) (tail : List Bytes) : List Bytes :=
  signedPrefix retained gathered dummies ++ (commitments ++ prior :: tail)

def preimageFront (selected retained prior : Bytes)
    (gathered dummies commitments : List Bytes) (j : Nat) : List Bytes :=
  [selected] ++ signedPrefix retained gathered dummies ++
    commitments.eraseIdx j ++ [prior]

def nextRawFront (prior : Bytes)
    (gathered dummies commitments : List Bytes) : List Bytes :=
  gathered ++ [finalNonce, []] ++ dummies ++ commitments ++ [prior]

/-- A successful roll at the first position of an appended tail necessarily
finds a tail element; its exact stack update removes that same element. -/
theorem successful_roll_from_tail {α : Type*}
    (front tail rolled : List α) (j : Nat)
    (success : KeyRolls.rollAt (front.length + j) (front ++ tail) =
      some rolled) :
    ∃ within : j < tail.length,
      rolled = tail[j] :: front ++ tail.eraseIdx j := by
  have selected : (front ++ tail)[front.length + j]? = tail[j]? := by
    rw [List.getElem?_append_right (by omega)]
    simp
  have available : (front ++ tail)[front.length + j]?.isSome := by
    unfold KeyRolls.rollAt at success
    cases cell : (front ++ tail)[front.length + j]? with
    | none => simp [cell] at success
    | some x => simp
  have within : j < tail.length := by
    rw [selected] at available
    by_contra short
    have beyond : tail.length ≤ j := by omega
    rw [List.getElem?_eq_none beyond] at available
    simp at available
  have moved := PoolRollInvariant.roll_from_middle front tail [] j within
  have exactRoll : KeyRolls.rollAt (front.length + j) (front ++ tail) =
      some (tail[j] :: front ++ tail.eraseIdx j) := by
    simpa [List.append_assoc] using moved
  exact ⟨within, Option.some.inj (success.symm.trans exactRoll)⟩

/-- Invert a successful push/ROLL pair that reaches an appended tail. The
actual selected bytes and erasure follow from the decoded index and success,
without assuming a canonical raw index encoding or fixed opcode budget. -/
theorem accepted_push_roll_tail_shape (hashes : Hashes)
    (raw : Bytes) (front tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (j : Nat)
    (parsed : ByteIndex.parseScriptNum raw =
      some (Int.ofNat (front.length + j)))
    (accepted : run hashes [.push raw, .roll]
      (State.mk (front ++ tail) outcomes cost) = some after) :
    ∃ within : j < tail.length,
      after = State.mk (tail[j] :: front ++ tail.eraseIdx j)
        outcomes (cost + 1) := by
  obtain ⟨afterPush, pushed, _, afterPushRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push raw) [.roll]
      (State.mk (front ++ tail) outcomes cost) after accepted
  have pushShape := ByteFinalCounts.push_success_shape hashes raw
    (front ++ tail) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨afterRoll, rollStep, _, finished⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll []
      (State.mk (raw :: (front ++ tail)) outcomes cost) after
      afterPushRun
  have budget := ByteFinalCounts.roll_success_budget hashes raw
    (front ++ tail) outcomes cost afterRoll rollStep
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes raw
    (front.length + j) (front ++ tail) outcomes cost parsed budget]
    at rollStep
  cases rolled : KeyRolls.rollAt (front.length + j) (front ++ tail) with
  | none => simp [rolled] at rollStep
  | some nextStack =>
      obtain ⟨within, shape⟩ := successful_roll_from_tail front tail
        nextStack j rolled
      subst nextStack
      simp [rolled] at rollStep
      cases rollStep
      simp [run] at finished
      cases finished
      exact ⟨within, rfl⟩

/-- A successful HASH160/EQUALVERIFY pair consumes the opening and target,
preserves the lower stack and outcomes, and supplies the exact hash equation. -/
theorem accepted_hash_pair_shape (hashes : Hashes)
    (opening target : Bytes) (rest : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.hash160, .equalverify]
      (State.mk (opening :: target :: rest) outcomes cost) = some after) :
    hashes.h160 opening = target ∧
      after = State.mk rest outcomes (cost + 2) := by
  have hit := ByteMachine.successful_hash_comparison hashes
    opening target rest outcomes cost []
    (by rw [accepted]; rfl)
  obtain ⟨afterHash, hashStep, _, afterHashRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .hash160 [.equalverify]
      (State.mk (opening :: target :: rest) outcomes cost)
      after accepted
  have hashBudget : cost + 1 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 1 > 201 := by omega
    unfold step at hashStep
    simp [tooHigh] at hashStep
  have hashExact : step hashes .hash160
      (State.mk (opening :: target :: rest) outcomes cost) =
      some (State.mk (hashes.h160 opening :: target :: rest)
        outcomes (cost + 1)) := by
    unfold step
    simp [show ¬cost + 1 > 201 by omega]
  rw [hashExact] at hashStep
  cases hashStep
  obtain ⟨afterEq, eqStep, _, finished⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .equalverify []
      (State.mk (hashes.h160 opening :: target :: rest)
        outcomes (cost + 1)) after afterHashRun
  have eqBudget : cost + 2 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 2 > 201 := by omega
    unfold step at eqStep
    simp [tooHigh] at eqStep
  have eqExact : step hashes .equalverify
      (State.mk (hashes.h160 opening :: target :: rest)
        outcomes (cost + 1)) =
      some (State.mk rest outcomes (cost + 2)) := by
    unfold step
    simp [show ¬cost + 2 > 201 by omega, hit]
  rw [eqExact] at eqStep
  cases eqStep
  simp [run] at finished
  cases finished
  exact ⟨hit, rfl⟩

theorem successful_target_matches_hash160_at (hashes : Hashes)
    (raw : Bytes) (depth : Nat)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat depth))
    (positive : 0 < depth)
    (target : Bytes) (rest : List Bytes) (outcomes : List Bool)
    (cost : Nat) (final : State)
    (accepted : run hashes
      [.push raw, .roll, .hash160, .equalverify]
      (State.mk (target :: rest) outcomes cost) = some final) :
    ∃ opening : Bytes, hashes.h160 opening = target := by
  have split : ([.push raw, .roll, .hash160,
      .equalverify] : List Op) =
      [.push raw, .roll] ++ [.hash160, .equalverify] := rfl
  rw [split, run_append] at accepted
  cases first : run hashes [.push raw, .roll]
      (State.mk (target :: rest) outcomes cost) with
  | none => simp [first] at accepted
  | some middle =>
      have preserved := ByteFinalCounts.accepted_pair_preserves_shallower_option
        hashes raw depth 0 (target :: rest) outcomes cost middle
        parsed positive first
      simp only [first, Option.bind_some] at accepted
      cases middle with
      | mk middleStack middleOutcomes middleCost =>
          cases middleStack with
          | nil => simp at preserved
          | cons opening below =>
              cases below with
              | nil => simp at preserved
              | cons compared tail =>
                  have same : compared = target := by
                    simpa using preserved
                  subst compared
                  exact ⟨opening, ByteMachine.successful_hash_comparison
                    hashes opening target tail middleOutcomes middleCost []
                    (by rw [accepted]; rfl)⟩

theorem accepted_roll_step_shape (hashes : Hashes)
    (raw : Bytes) (stack nextStack : List Bytes)
    (outcomes : List Bool) (cost n : Nat) (after : State)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n))
    (rolled : KeyRolls.rollAt n stack = some nextStack)
    (success : step hashes .roll
      (State.mk (raw :: stack) outcomes cost) = some after) :
    after = State.mk nextStack outcomes (cost + 1) := by
  have budget := ByteFinalCounts.roll_success_budget hashes raw stack
    outcomes cost after success
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes raw n stack
    outcomes cost parsed budget, rolled] at success
  cases success
  rfl

/-- Once each prior signed selection has removed one dummy, the commitment
pool always begins at absolute depth 153 after the newly retained index. -/
theorem signed_prefix_length (retained : Bytes)
    (gathered dummies : List Bytes)
    (poolLength : gathered.length + dummies.length = 150) :
    (signedPrefix retained gathered dummies).length = 153 := by
  simp [signedPrefix]
  omega

theorem signed_prefix_wrong_width (retained : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4) :
    ∀ x ∈ signedPrefix retained gathered dummies, x.length ≠ 20 := by
  intro x hx
  simp only [signedPrefix, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with hfront | dummyHit
  · rcases hfront with hbefore | hnonceOrZero
    · rcases hbefore with hretained | gatheredHit
      · subst x
        omega
      · have width := shape.gatheredWidth x gatheredHit
        omega
    · rcases hnonceOrZero with hnonce | hzero
      · subst x
        decide
      · subst x
        decide
  · have width := shape.dummyWidth x dummyHit
    omega

/-- Every source before the commitment window has non-HASH160 width,
including any previously gathered nine-byte dummy signatures. -/
theorem shallow_signed_source_wrong_width (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (n : Nat) (shallow : n < 153) :
    ∃ chosen : Bytes,
      (signedRegion retained gathered dummies commitments prior tail)[n]? =
        some chosen ∧ chosen.length ≠ 20 := by
  have prefixLength := signed_prefix_length retained gathered dummies
    shape.poolCount
  have within : n < (signedPrefix retained gathered dummies).length := by
    rw [prefixLength]
    exact shallow
  let chosen := (signedPrefix retained gathered dummies)[n]
  have source :
      (signedRegion retained gathered dummies commitments prior tail)[n]? =
        some chosen := by
    unfold signedRegion
    rw [List.getElem?_append_left within]
    exact List.getElem?_eq_getElem within
  exact ⟨chosen, source,
    signed_prefix_wrong_width retained gathered dummies commitments
      shape retainedSmall chosen (List.getElem_mem within)⟩

theorem signed_commitment_source (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (poolLength : gathered.length + dummies.length = 150)
    (j : Nat) (within : j < commitments.length) :
    (signedRegion retained gathered dummies commitments prior tail)[153 + j]? =
      commitments[j]? := by
  unfold signedRegion
  rw [List.getElem?_append_right (by
    rw [signed_prefix_length retained gathered dummies poolLength]
    omega)]
  have index : 153 + j -
      (signedPrefix retained gathered dummies).length = j := by
    rw [signed_prefix_length retained gathered dummies poolLength]
    omega
  rw [index]
  exact List.getElem?_append_left within

/-- Clamping a signed index to 152 selects the previous round's Boolean
result at the end of the current commitment pool. -/
theorem capped_signed_source_is_prior (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments) :
    (signedRegion retained gathered dummies commitments prior tail)[303 -
      gathered.length]? = some prior := by
  have prefixLength := signed_prefix_length retained gathered dummies
    shape.poolCount
  have frontLength :
      (signedPrefix retained gathered dummies ++ commitments).length =
        303 - gathered.length := by
    simp only [List.length_append]
    rw [prefixLength, shape.commitmentCount]
    have count := shape.poolCount
    omega
  unfold signedRegion
  rw [← List.append_assoc]
  rw [List.getElem?_append_right (by rw [frontLength])]
  rw [frontLength]
  simp

/-- The commitment roll removes precisely one current commitment while
preserving the gathered signatures, nonce, zero dummy, and remaining dummies. -/
theorem commitment_roll_shape (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (poolLength : gathered.length + dummies.length = 150)
    (j : Nat) (within : j < commitments.length) :
    KeyRolls.rollAt (153 + j)
      (signedRegion retained gathered dummies commitments prior tail) =
      some (commitments[j] ::
        signedPrefix retained gathered dummies ++
        commitments.eraseIdx j ++ prior :: tail) := by
  have moved := PoolRollInvariant.roll_from_middle
    (signedPrefix retained gathered dummies) commitments
    (prior :: tail) j within
  simpa [signedRegion,
    signed_prefix_length retained gathered dummies poolLength,
    List.append_assoc] using moved

/-- The following raw-index roll uses the same current pool position `j` to
move its nine-byte dummy signature above the previously gathered signatures.
This is the exact paired-roll transition needed by the seven-round invariant. -/
theorem paired_dummy_roll_shape (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (j : Nat) (within : j < dummies.length) :
    KeyRolls.rollAt (gathered.length + 2 + j)
      (gathered ++ [finalNonce, []] ++ dummies ++
        commitments ++ prior :: tail) =
      some (dummies[j] :: gathered ++ [finalNonce, []] ++
        dummies.eraseIdx j ++ commitments ++ prior :: tail) := by
  simpa [List.append_assoc] using
    (PoolRollInvariant.roll_at_pool gathered dummies
      (commitments ++ prior :: tail) finalNonce j within)

theorem preimage_front_length (selected retained prior : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < commitments.length) :
    (preimageFront selected retained prior gathered dummies commitments j).length =
      304 - gathered.length := by
  have prefixLength := signed_prefix_length retained gathered dummies
    shape.poolCount
  simp only [preimageFront, List.length_append, List.length_cons,
    List.length_nil, List.length_eraseIdx, if_pos within]
  rw [prefixLength, shape.commitmentCount]
  have count := shape.poolCount
  have positive : 0 < dummies.length := by
    rw [shape.commitmentCount] at within
    omega
  omega

/-- In each pool-shaped round, the generated deep preimage roll reaches the
earlier tail at offset `291-k`, with `k` already gathered signatures. -/
theorem preimage_roll_tail_source (selected retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < commitments.length)
    (enough : 291 - gathered.length < tail.length) :
    KeyRolls.rollAt (595 - 2 * gathered.length)
      (preimageFront selected retained prior gathered dummies commitments j ++
        tail) =
      some (tail[291 - gathered.length] ::
        preimageFront selected retained prior gathered dummies commitments j ++
        tail.eraseIdx (291 - gathered.length)) := by
  have frontLength := preimage_front_length selected retained prior
    gathered dummies commitments shape j within
  have depth :
      (preimageFront selected retained prior gathered dummies commitments j).length +
        (291 - gathered.length) = 595 - 2 * gathered.length := by
    rw [frontLength]
    have count := shape.poolCount
    omega
  have moved := PoolRollInvariant.roll_from_middle
    (preimageFront selected retained prior gathered dummies commitments j)
    tail [] (291 - gathered.length) enough
  simpa [depth] using moved

/-- A successful generated preimage push/ROLL pair has the exact tail-source
shape predicted by the pool invariant. Success itself supplies the needed
tail length and opcode-budget premises. -/
theorem accepted_preimage_pair_shape (hashes : Hashes) (k : Fin 7)
    (selected retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (j : Nat) (within : j < commitments.length)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push (preimageIndex k), .roll]
      (State.mk
        (preimageFront selected retained prior gathered dummies
          commitments j ++ tail) outcomes cost) = some after) :
    ∃ enough : 291 - gathered.length < tail.length,
      after = State.mk
        (tail[291 - gathered.length] ::
          preimageFront selected retained prior gathered dummies
            commitments j ++ tail.eraseIdx (291 - gathered.length))
        outcomes (cost + 1) := by
  have frontLength := preimage_front_length selected retained prior
    gathered dummies commitments shape j within
  have depth :
      (preimageFront selected retained prior gathered dummies commitments j).length +
        (291 - gathered.length) = 595 - 2 * k.val := by
    rw [frontLength, count]
    omega
  have parsed := generated_preimage_index_decodes k
  rw [← depth] at parsed
  exact accepted_push_roll_tail_shape hashes (preimageIndex k)
    (preimageFront selected retained prior gathered dummies commitments j)
    tail outcomes cost after (291 - gathered.length) parsed accepted

theorem next_raw_front_length (prior : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments) :
    (nextRawFront prior gathered dummies commitments).length =
      303 - gathered.length := by
  simp only [nextRawFront, List.length_append, List.length_cons,
    List.length_nil]
  rw [shape.commitmentCount]
  have count := shape.poolCount
  omega

/-- Every generated fixed raw-index roll after a pool-shaped draw fetches
tail cell 283, despite the changing encoded roll depth. -/
theorem fixed_raw_roll_tail_source (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (enough : 283 < tail.length) :
    KeyRolls.rollAt (586 - gathered.length)
      (nextRawFront prior gathered dummies commitments ++ tail) =
      some (tail[283] ::
        nextRawFront prior gathered dummies commitments ++
        tail.eraseIdx 283) := by
  have frontLength := next_raw_front_length prior gathered dummies
    commitments shape
  have depth :
      (nextRawFront prior gathered dummies commitments).length + 283 =
        586 - gathered.length := by
    rw [frontLength]
    have count := shape.poolCount
    omega
  have moved := PoolRollInvariant.roll_from_middle
    (nextRawFront prior gathered dummies commitments) tail [] 283 enough
  simpa [depth] using moved

/-- The generated fixed pair for any of the seven signed selections, when
reached in a pool-shaped state, fetches exactly tail cell 283. -/
theorem accepted_fixed_raw_pair_shape (hashes : Hashes) (k : Fin 7)
    (prior : Bytes) (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push (fixedRawIndex k), .roll]
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) = some after) :
    ∃ enough : 283 < tail.length,
      after = State.mk
        (tail[283] :: nextRawFront prior gathered dummies commitments ++
          tail.eraseIdx 283) outcomes (cost + 1) := by
  have frontLength := next_raw_front_length prior gathered dummies
    commitments shape
  have depth :
      (nextRawFront prior gathered dummies commitments).length + 283 =
        586 - k.val := by
    rw [frontLength, count]
    omega
  have parsed := generated_fixed_raw_index_decodes k
  rw [← depth] at parsed
  exact accepted_push_roll_tail_shape hashes (fixedRawIndex k)
    (nextRawFront prior gathered dummies commitments) tail
    outcomes cost after 283 parsed accepted

/-- For any in-range raw index above the current shallow boundary, the
generated signed offset reaches commitment `j`; the later raw-index roll
reaches dummy `j`. Their paired removals preserve the pool invariant. -/
theorem inrange_paired_roll_transition (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (n : Fin 152) (low : gathered.length + 2 ≤ n.val) :
    ∃ (j : Nat) (dummyWithin : j < dummies.length)
      (commitmentWithin : j < commitments.length),
      n.val = gathered.length + 2 + j ∧
      KeyRolls.rollAt (151 - gathered.length + n.val)
        (signedRegion retained gathered dummies commitments prior tail) =
        some (commitments[j]'commitmentWithin ::
          signedPrefix retained gathered dummies ++
          commitments.eraseIdx j ++ prior :: tail) ∧
      KeyRolls.rollAt n.val
        (gathered ++ [finalNonce, []] ++ dummies ++
          commitments.eraseIdx j ++ prior :: tail) =
        some (dummies[j]'dummyWithin :: gathered ++ [finalNonce, []] ++
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
    exact commitment_roll_shape retained prior gathered dummies
      commitments tail shape.poolCount j commitmentWithin
  · rw [rawEq]
    exact paired_dummy_roll_shape prior gathered dummies
      (commitments.eraseIdx j) tail j within

/-- Under the capped post-ADD depth bound, any successful generated signed
comparison must select one current commitment. This does not assume the raw
index was canonically encoded or already in range. -/
theorem accepted_postadd_commitment_source (hashes : Hashes)
    (k : Fin 7) (offset retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (priorSmall : prior.length ≤ 1)
    (index : Nat)
    (parsed : ByteIndex.parseScriptNum offset = some (Int.ofNat index))
    (capped : index ≤ 303 - gathered.length)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedComparisonOps k)
      (State.mk (offset :: signedRegion retained gathered dummies
        commitments prior tail) outcomes cost) = some final) :
    ∃ j : Nat, ∃ opening : Bytes,
      index = 153 + j ∧
      commitments[j]? = some (hashes.h160 opening) := by
  rw [generated_signed_comparison_ops] at accepted
  obtain ⟨afterRoll, rolled, _, suffix⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll
      [.push (preimageIndex k), .roll, .hash160, .equalverify]
      (State.mk (offset :: signedRegion retained gathered dummies
        commitments prior tail) outcomes cost) final accepted
  have budget := ByteFinalCounts.roll_success_budget hashes offset
    (signedRegion retained gathered dummies commitments prior tail)
    outcomes cost afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes offset index
    (signedRegion retained gathered dummies commitments prior tail)
    outcomes cost parsed budget] at rolled
  unfold KeyRolls.rollAt at rolled
  cases source : (signedRegion retained gathered dummies commitments
      prior tail)[index]? with
  | none => simp [source] at rolled
  | some selected =>
      simp [source] at rolled
      rw [← rolled] at suffix
      have preimageParsed := generated_preimage_index_decodes k
      obtain ⟨opening, hit⟩ :=
        successful_target_matches_hash160_at hashes (preimageIndex k)
          (595 - 2 * k.val) preimageParsed (by omega)
          selected ((signedRegion retained gathered dummies commitments
            prior tail).eraseIdx index) outcomes (cost + 1) final suffix
      have deep : 153 ≤ index := by
        by_contra shallowIndex
        have shallow : index < 153 := by omega
        obtain ⟨chosen, cell, wrongWidth⟩ :=
          shallow_signed_source_wrong_width retained prior gathered
            dummies commitments tail shape retainedSmall index shallow
        rw [source] at cell
        have same : selected = chosen := Option.some.inj cell
        rw [same] at hit
        have width := hashes.h160_width opening
        rw [hit] at width
        exact wrongWidth width
      have belowCap : index < 303 - gathered.length := by
        by_contra notBelow
        have capEq : index = 303 - gathered.length := by omega
        have cell := capped_signed_source_is_prior retained prior
          gathered dummies commitments tail shape
        rw [← capEq, source] at cell
        have same : selected = prior := Option.some.inj cell
        rw [same] at hit
        have width := hashes.h160_width opening
        rw [hit] at width
        omega
      let j := index - 153
      have within : j < commitments.length := by
        have count := shape.poolCount
        have sameLen := shape.commitmentCount
        dsimp [j]
        omega
      have indexEq : index = 153 + j := by
        dsimp [j]
        omega
      have commitmentCell := signed_commitment_source retained prior
        gathered dummies commitments tail shape.poolCount j within
      rw [← indexEq, source, List.getElem?_eq_getElem within]
        at commitmentCell
      have chosenEq : selected = commitments[j] :=
        Option.some.inj commitmentCell
      refine ⟨j, opening, indexEq, ?_⟩
      rw [List.getElem?_eq_getElem within]
      exact congrArg some (chosenEq.symm.trans hit.symm)

/-- Execute one reached signed suffix from the post-ADD state. Successful
execution forces a matching commitment/opening equation and advances the
paired pools to the exact stack expected by the next fixed raw-index pair.
This theorem does not yet derive its in-range index premise from arbitrary
successful earlier rounds. -/
theorem accepted_inrange_signed_suffix_shape (hashes : Hashes)
    (k : Fin 7) (retained offset prior : Bytes)
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
        (offset :: signedRegion retained gathered dummies commitments
          prior tail) outcomes cost) = some final) :
    ∃ (j : Nat) (dummyWithin : j < dummies.length)
      (commitmentWithin : j < commitments.length) (opening : Bytes),
      n.val = gathered.length + 2 + j ∧
      tail[291 - gathered.length]? = some opening ∧
      hashes.h160 opening = commitments[j]'commitmentWithin ∧
      PoolShape (dummies[j]'dummyWithin :: gathered)
        (dummies.eraseIdx j) (commitments.eraseIdx j) ∧
      final = State.mk
        (nextRawFront prior (dummies[j]'dummyWithin :: gathered)
          (dummies.eraseIdx j) (commitments.eraseIdx j) ++
          tail.eraseIdx (291 - gathered.length))
        outcomes (cost + 5) := by
  obtain ⟨j, dummyWithin, commitmentWithin, rawEq,
      commitmentRoll, _dummyRoll, nextShape⟩ :=
    inrange_paired_roll_transition retained prior gathered dummies
      commitments tail shape n low
  rw [generated_signed_suffix_ops] at accepted
  obtain ⟨afterCommit, commitStep, _, remaining⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll
      [.push (preimageIndex k), .roll, .hash160, .equalverify, .roll]
      (State.mk (offset :: signedRegion retained gathered dummies
        commitments prior tail) outcomes cost) final accepted
  have offsetParsed : ByteIndex.parseScriptNum offset =
      some (Int.ofNat (151 - gathered.length + n.val)) := parsedOffset
  have afterCommitShape := accepted_roll_step_shape hashes offset
    (signedRegion retained gathered dummies commitments prior tail)
    (commitments[j] :: signedPrefix retained gathered dummies ++
      commitments.eraseIdx j ++ prior :: tail)
    outcomes cost (151 - gathered.length + n.val) afterCommit
    offsetParsed (by
      rw [show 151 - gathered.length + n.val = 151 - gathered.length + n.val
        from rfl]
      exact commitmentRoll) commitStep
  rw [afterCommitShape] at remaining
  have frontEq :
      commitments[j] :: signedPrefix retained gathered dummies ++
        commitments.eraseIdx j ++ prior :: tail =
      preimageFront commitments[j] retained prior gathered dummies
        commitments j ++ tail := by
    simp [preimageFront, List.append_assoc]
  rw [frontEq] at remaining
  have split :
      ([.push (preimageIndex k), .roll, .hash160,
        .equalverify, .roll] : List Op) =
      [.push (preimageIndex k), .roll] ++
        ([.hash160, .equalverify] ++ [.roll]) := rfl
  rw [split, run_append] at remaining
  cases preimage : run hashes [.push (preimageIndex k), .roll]
      (State.mk
        (preimageFront commitments[j] retained prior gathered dummies
          commitments j ++ tail) outcomes (cost + 1)) with
  | none => simp [preimage] at remaining
  | some afterPreimage =>
      obtain ⟨enough, preimageShape⟩ :=
        accepted_preimage_pair_shape hashes k commitments[j] retained
          prior gathered dummies commitments tail shape count j
          commitmentWithin outcomes (cost + 1) afterPreimage preimage
      simp only [preimage, Option.bind_some] at remaining
      rw [preimageShape] at remaining
      rw [run_append] at remaining
      let opening := tail[291 - gathered.length]
      let tailAfter := tail.eraseIdx (291 - gathered.length)
      let lower := signedPrefix retained gathered dummies ++
        commitments.eraseIdx j ++ prior :: tailAfter
      have hashInput :
          opening :: preimageFront commitments[j] retained prior
            gathered dummies commitments j ++ tailAfter =
          opening :: commitments[j] :: lower := by
        simp [opening, lower, preimageFront, List.append_assoc]
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
              (gathered ++ [finalNonce, []] ++ dummies ++
                commitments.eraseIdx j ++ prior :: tailAfter) := by
            simp [lower, signedPrefix, List.append_assoc]
          rw [lowerEq] at remaining
          obtain ⟨afterDummy, dummyStep, _, finished⟩ :=
            FirstAcceptedOrigin.run_cons_success hashes .roll []
              (State.mk (retained ::
                (gathered ++ [finalNonce, []] ++ dummies ++
                  commitments.eraseIdx j ++ prior :: tailAfter))
                outcomes (cost + 4)) final remaining
          have dummyRoll := paired_dummy_roll_shape prior gathered dummies
            (commitments.eraseIdx j) tailAfter j dummyWithin
          have afterDummyShape := accepted_roll_step_shape hashes retained
            (gathered ++ [finalNonce, []] ++ dummies ++
              commitments.eraseIdx j ++ prior :: tailAfter)
            (dummies[j] :: gathered ++ [finalNonce, []] ++
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
          simp [nextRawFront, tailAfter, List.append_assoc]

/-- Every successful reached signed block on a pool-shaped stack is forced
to draw a commitment and its aligned dummy at one current pool position.
This includes arbitrary raw ScriptNum encodings, negative and capped values,
and the exact earlier-tail source for the preimage. The theorem is local to
one reached block; the seven-block whole-run induction remains separate. -/
theorem accepted_signed_round_transition (hashes : Hashes) (k : Fin 7)
    (result : Bool) (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (raw : Bytes) (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedRoundOps k)
      (State.mk (raw ::
        (nextRawFront (ByteMachine.boolBytes result)
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
        (nextRawFront (ByteMachine.boolBytes result)
          (dummies[j]'dummyWithin :: gathered)
          (dummies.eraseIdx j) (commitments.eraseIdx j) ++
          tail.eraseIdx (291 - gathered.length))
        outcomes (cost + 8) := by
  rw [signed_round_splits k, run_append] at accepted
  cases cap : run hashes (signedCapAddOps k)
      (State.mk (raw ::
        (nextRawFront (ByteMachine.boolBytes result)
          gathered dummies commitments ++ tail))
        outcomes cost) with
  | none => simp [cap] at accepted
  | some middle =>
      obtain ⟨source, operand, retained, offset, rawParsed,
          retainedEncoded, retainedParsed, offsetEncoded, middleShape⟩ :=
        accepted_signed_cap_add_shape hashes k raw
          (nextRawFront (ByteMachine.boolBytes result)
            gathered dummies commitments ++ tail)
          outcomes cost middle cap
      simp only [cap, Option.bind_some] at accepted
      rw [middleShape] at accepted
      have baseEq : retained ::
          (nextRawFront (ByteMachine.boolBytes result)
            gathered dummies commitments ++ tail) =
          signedRegion retained gathered dummies commitments
            (ByteMachine.boolBytes result) tail := by
        simp [signedRegion, signedPrefix, nextRawFront, List.append_assoc]
      rw [baseEq] at accepted
      have suffix : run hashes (signedSuffixOps k)
          (State.mk (offset :: signedRegion retained gathered dummies
            commitments (ByteMachine.boolBytes result) tail)
            outcomes (cost + 3)) = some final := accepted
      have comparisonRun : ∃ middle,
          run hashes (signedComparisonOps k)
            (State.mk (offset :: signedRegion retained gathered dummies
              commitments (ByteMachine.boolBytes result) tail)
              outcomes (cost + 3)) = some middle := by
        apply FirstAcceptedOrigin.successful_prefix hashes
          (signedComparisonOps k) [.roll]
        rw [← signed_suffix_splits k]
        exact suffix
      rw [generated_signed_suffix_ops] at suffix
      obtain ⟨afterFirstRoll, firstRollStep, _, _rest⟩ :=
        FirstAcceptedOrigin.run_cons_success hashes .roll
          [.push (preimageIndex k), .roll, .hash160,
            .equalverify, .roll]
          (State.mk (offset :: signedRegion retained gathered dummies
            commitments (ByteMachine.boolBytes result) tail)
            outcomes (cost + 3)) final suffix
      obtain ⟨index, parsedOffset, nonnegative⟩ :=
        FinalSignedAccepted.accepted_roll_parses_nonnegative hashes offset
          (signedRegion retained gathered dummies commitments
            (ByteMachine.boolBytes result) tail)
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
      obtain ⟨comparisonMiddle, comparisonAccepted⟩ := comparisonRun
      obtain ⟨j, opening, indexSource, commitmentHit⟩ :=
        accepted_postadd_commitment_source hashes k offset retained
          (ByteMachine.boolBytes result) gathered dummies commitments
          tail shape
          (ByteIndexSign.parsed_bytes_are_short retained operand
            retainedParsed)
          (by cases result <;> decide)
          index.toNat parsedNat indexBound outcomes (cost + 3)
          comparisonMiddle comparisonAccepted
      have commitmentWithin : j < commitments.length :=
        (List.getElem?_eq_some_iff.mp commitmentHit).1
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
        accepted_inrange_signed_suffix_shape hashes k retained offset
          (ByteMachine.boolBytes result) gathered dummies commitments
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

/-- A complete generated 13-opcode signed block fetches its raw index from
earlier tail cell 283, proves the paired commitment/dummy transition, and
preserves both pool shape and original-position alignment. -/
theorem accepted_signed_block_transition (hashes : Hashes) (k : Fin 7)
    (result : Bool) (ids : List (Fin 150))
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : AlignedPool ids dummies commitments)
    (count : gathered.length = k.val)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedBlockOps k)
      (State.mk (nextRawFront (ByteMachine.boolBytes result)
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
      AlignedPool (ids.eraseIdx j)
        (dummies.eraseIdx j) (commitments.eraseIdx j) ∧
      final = State.mk
        (nextRawFront (ByteMachine.boolBytes result)
          (dummies[j]'dummyWithin :: gathered)
          (dummies.eraseIdx j) (commitments.eraseIdx j) ++
          (tail.eraseIdx 283).eraseIdx (291 - gathered.length))
        outcomes (cost + 9) := by
  rw [generated_signed_block_ops k, run_append] at accepted
  cases fixed : run hashes [.push (fixedRawIndex k), .roll]
      (State.mk (nextRawFront (ByteMachine.boolBytes result)
        gathered dummies commitments ++ tail) outcomes cost) with
  | none => simp [fixed] at accepted
  | some afterFixed =>
      obtain ⟨enough, fixedShape⟩ :=
        accepted_fixed_raw_pair_shape hashes k (ByteMachine.boolBytes result)
          gathered dummies commitments tail shape count outcomes cost
          afterFixed fixed
      simp only [fixed, Option.bind_some] at accepted
      rw [fixedShape] at accepted
      obtain ⟨j, dummyWithin, commitmentWithin, opening,
          parsedRaw, preimageSource, hit, nextShape, roundShape⟩ :=
        accepted_signed_round_transition hashes k result gathered
          dummies commitments (tail.eraseIdx 283) shape count
          tail[283] outcomes (cost + 1) final accepted
      refine ⟨tail[283], opening, j, dummyWithin, commitmentWithin,
        List.getElem?_eq_getElem enough, parsedRaw, preimageSource,
        hit, nextShape,
        paired_erasure_preserves_alignment ids dummies commitments
          aligned j, ?_⟩
      simpa only [Nat.add_assoc] using roundShape

end QSB.FinalSignedLoop
