import QSB.ByteIndexSign

/-!
Generic negative first-index analysis for the local byte machine. This
avoids assuming exact serializer round trips for unbounded negative values:
parseable re-encodings preserve nonpositivity, which suffices to bound the
eventual signed-roll depth.
-/
namespace QSB.FirstNegativeAll
open ByteMachine
open FirstOvershoot
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem negative_min_output (hashes : Hashes)
    (raw retained : Bytes) (source : Int) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (parsed : ByteIndex.parseScriptNum raw = some source)
    (negative : source < 0) (budget : cost + 1 ≤ 201)
    (result : step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: stack) outcomes cost) =
      some (State.mk (retained :: stack) outcomes (cost + 1))) :
    ByteIndex.encodeScriptNum source = some retained := by
  unfold step at result
  have within : ¬ (cost + 1 > 201) := by omega
  have capped : min (152 : Int) source = source :=
    min_eq_right (by omega)
  simp [within, ByteIndex.positive_152, parsed, capped] at result
  cases encoded : ByteIndex.encodeScriptNum source with
  | none => simp [encoded] at result
  | some value =>
      simp [encoded] at result
      cases result
      rfl

theorem add_output (hashes : Hashes)
    (retained offset : Bytes) (value : Int) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (parsed : ByteIndex.parseScriptNum retained = some value)
    (budget : cost + 1 ≤ 201)
    (result : step hashes .add
      (State.mk ([0x97, 0x00] :: retained :: stack) outcomes cost) =
      some (State.mk (offset :: stack) outcomes (cost + 1))) :
    ByteIndex.encodeScriptNum ((151 : Int) + value) = some offset := by
  unfold step at result
  have within : ¬ (cost + 1 > 201) := by omega
  simp [within, parse_151, parsed] at result
  cases encoded : ByteIndex.encodeScriptNum ((151 : Int) + value) with
  | none => simp [encoded] at result
  | some bytes =>
      simp [encoded] at result
      cases result
      rfl

theorem add_success_parses_operand (hashes : Hashes)
    (retained offset : Bytes) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (result : step hashes .add
      (State.mk ([0x97, 0x00] :: retained :: stack) outcomes cost) =
      some (State.mk (offset :: stack) outcomes (cost + 1))) :
    ∃ value : Int, ByteIndex.parseScriptNum retained = some value := by
  unfold step at result
  by_cases exceeded : cost + 1 > 201
  · simp [exceeded] at result
  · simp [exceeded, parse_151] at result
    cases parsed : ByteIndex.parseScriptNum retained with
    | none => simp [parsed] at result
    | some value => exact ⟨value, rfl⟩

theorem roll_success_parses_index (hashes : Hashes)
    (offset : Bytes) (stack rest : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (result : step hashes .roll
      (State.mk (offset :: stack) outcomes cost) =
      some (State.mk rest outcomes (cost + 1))) :
    ∃ value : Int, ByteIndex.parseScriptNum offset = some value := by
  unfold step at result
  by_cases exceeded : cost + 1 > 201
  · simp [exceeded] at result
  · simp [exceeded] at result
    cases parsed : ByteIndex.parseScriptNum offset with
    | none => simp [parsed] at result
    | some value => exact ⟨value, rfl⟩

theorem rolled_hash_has_source (hashes : Hashes)
    (opening offset retained : Bytes) (tail rest : List Bytes)
    (index : Int) (outcomes : List Bool) (cost : Nat)
    (parsed : ByteIndex.parseScriptNum offset = some index)
    (budget : cost + 1 ≤ 201)
    (rolled : step hashes .roll
      (State.mk (offset :: (retained :: (fixedRegion ++ tail)))
        outcomes cost) =
      some (State.mk (hashes.h160 opening :: rest) outcomes (cost + 1))) :
    0 ≤ index ∧
      (retained :: (fixedRegion ++ tail))[index.toNat]? =
        some (hashes.h160 opening) := by
  have nonnegative : 0 ≤ index := by
    by_contra negative
    have below : index < 0 := by omega
    unfold step at rolled
    have within : ¬ (cost + 1 > 201) := by omega
    simp [within, parsed, below] at rolled
  have index_eq : index = Int.ofNat index.toNat :=
    Int.eq_natCast_toNat.mpr nonnegative
  have parsedNat : ByteIndex.parseScriptNum offset =
      some (Int.ofNat index.toNat) := by
    rw [← index_eq]
    exact parsed
  rw [byte_roll_matches_list_roll hashes offset index.toNat
    (retained :: (fixedRegion ++ tail)) outcomes cost parsedNat budget] at rolled
  unfold KeyRolls.rollAt at rolled
  cases selected : (retained :: (fixedRegion ++ tail))[index.toNat]? with
  | none => simp [selected] at rolled
  | some cell =>
      simp [selected] at rolled
      constructor
      · exact nonnegative
      · exact congrArg some rolled.1

/-- Every negative raw first index is ruled out as the source of a successful
first HASH160 comparison, whenever the generated local MIN, ADD and ROLL
steps execute. This also covers magnitudes too large to reparse: those paths
cannot satisfy the successful-step premises. -/
theorem negative_first_roll_cannot_yield_hash (hashes : Hashes)
    (raw retained offset opening : Bytes) (tail rest : List Bytes)
    (source : Int) (outcomes : List Bool)
    (parsedRaw : ByteIndex.parseScriptNum raw = some source)
    (negative : source < 0)
    (minResult : step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: (fixedRegion ++ tail)) outcomes 6) =
      some (State.mk (retained :: (fixedRegion ++ tail)) outcomes 7))
    (addResult : step hashes .add
      (State.mk
        ([0x97, 0x00] :: retained :: retained :: (fixedRegion ++ tail))
        outcomes 8) =
      some (State.mk (offset :: retained :: (fixedRegion ++ tail)) outcomes 9))
    (rollResult : step hashes .roll
      (State.mk (offset :: retained :: (fixedRegion ++ tail)) outcomes 9) =
      some (State.mk (hashes.h160 opening :: rest) outcomes 10)) :
    False := by
  have encodedRetained := negative_min_output hashes raw retained source
    (fixedRegion ++ tail) outcomes 6 parsedRaw negative (by omega) minResult
  obtain ⟨operand, parsedRetained⟩ :=
    add_success_parses_operand hashes retained offset
      (retained :: (fixedRegion ++ tail)) outcomes 8 addResult
  have operandNonpositive : operand ≤ 0 :=
    ByteIndexSign.negative_encoding_never_parses_positive source retained
      negative encodedRetained operand parsedRetained
  have encodedOffset := add_output hashes retained offset operand
    (retained :: (fixedRegion ++ tail)) outcomes 8 parsedRetained
    (by omega) addResult
  obtain ⟨index, parsedOffset⟩ :=
    roll_success_parses_index hashes offset
      (retained :: (fixedRegion ++ tail))
      (hashes.h160 opening :: rest) outcomes 9 rollResult
  have indexBound : index ≤ 151 :=
    ByteIndexSign.encoded_below_152_parses_below_152
      ((151 : Int) + operand) index offset (by omega)
      encodedOffset parsedOffset
  obtain ⟨nonnegative, hit⟩ :=
    rolled_hash_has_source hashes opening offset retained tail rest index
      outcomes 9 parsedOffset (by omega) rollResult
  have indexEq : index = Int.ofNat index.toNat :=
    Int.eq_natCast_toNat.mpr nonnegative
  have smallIndex : index.toNat ≤ 151 := by
    have castBound : Int.ofNat index.toNat ≤ 151 := by
      simpa only [← indexEq] using indexBound
    exact Int.ofNat_le.mp castBound
  obtain ⟨i, deep, _cell⟩ :=
    FirstIndexMap.fixed_region_hash_hit_has_commitment_origin hashes
      opening retained tail index.toNat
      (ByteIndexSign.parsed_bytes_are_short retained operand parsedRetained)
      (by omega) hit
  omega

/-- Local first-selection extraction for every parsed index below the cap.
Negative values cannot match; nonnegative values must identify one of the
150 fixed commitments. The premises are the three reached byte-machine
steps, not an assertion about arbitrary scriptSig execution. -/
theorem below_cap_first_roll_has_commitment_origin (hashes : Hashes)
    (raw retained offset opening : Bytes) (tail rest : List Bytes)
    (source : Int) (outcomes : List Bool)
    (parsedRaw : ByteIndex.parseScriptNum raw = some source)
    (below : source < 152)
    (minResult : step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: (fixedRegion ++ tail)) outcomes 6) =
      some (State.mk (retained :: (fixedRegion ++ tail)) outcomes 7))
    (addResult : step hashes .add
      (State.mk
        ([0x97, 0x00] :: retained :: retained :: (fixedRegion ++ tail))
        outcomes 8) =
      some (State.mk (offset :: retained :: (fixedRegion ++ tail)) outcomes 9))
    (rollResult : step hashes .roll
      (State.mk (offset :: retained :: (fixedRegion ++ tail)) outcomes 9) =
      some (State.mk (hashes.h160 opening :: rest) outcomes 10)) :
    ∃ i : Fin 150,
      source = Int.ofNat (2 + i.val) ∧
      fixedRegion[152 + i.val]? = some (hashes.h160 opening) := by
  by_cases negative : source < 0
  · exact (negative_first_roll_cannot_yield_hash hashes raw retained offset
      opening tail rest source outcomes parsedRaw negative
      minResult addResult rollResult).elim
  · let n : Fin 152 := ⟨source.toNat, by omega⟩
    have sourceEq : source = Int.ofNat n.val := by
      dsimp [n]
      exact Int.eq_natCast_toNat.mpr (by omega)
    have parsedN : ByteIndex.parseScriptNum raw = some (Int.ofNat n.val) := by
      rw [← sourceEq]
      exact parsedRaw
    obtain ⟨i, index, cell⟩ :=
      FirstNumericRange.inrange_first_roll_has_commitment_origin hashes
        raw retained offset opening tail rest n outcomes parsedN
        minResult addResult rollResult
    refine ⟨i, ?_, cell⟩
    rw [sourceEq]
    exact congrArg Int.ofNat index

end QSB.FirstNegativeAll
