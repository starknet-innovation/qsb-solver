import QSB.FirstIndexMap

/-!
Finite ScriptNum arithmetic for the first signed selection's in-range
nonnegative indices. This checks the actual source-shaped serializer and
parser over all 152 values below the first `OP_MIN` cap. Negative values
require a separate arithmetic argument.
-/
namespace QSB.FirstNumericRange
open ByteMachine
open FirstOvershoot
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem canonical_index_roundtrip :
    ∀ n : Fin 152,
      (ByteIndex.encodeScriptNum (Int.ofNat n.val)).bind
        ByteIndex.parseScriptNum = some (Int.ofNat n.val) := by decide

theorem signed_offset_roundtrip :
    ∀ n : Fin 152,
      (ByteIndex.encodeScriptNum (Int.ofNat (151 + n.val))).bind
        ByteIndex.parseScriptNum = some (Int.ofNat (151 + n.val)) := by decide

def canonicalIndex (n : Fin 152) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat n.val)).getD []

def signedOffset (n : Fin 152) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (151 + n.val))).getD []

theorem encode_canonical_index (n : Fin 152) :
    ByteIndex.encodeScriptNum (Int.ofNat n.val) =
      some (canonicalIndex n) := by
  have checked : ∀ i : Fin 152,
      ByteIndex.encodeScriptNum (Int.ofNat i.val) =
        some (canonicalIndex i) := by decide
  exact checked n

theorem parse_canonical_index (n : Fin 152) :
    ByteIndex.parseScriptNum (canonicalIndex n) =
      some (Int.ofNat n.val) := by
  have checked : ∀ i : Fin 152,
      ByteIndex.parseScriptNum (canonicalIndex i) =
        some (Int.ofNat i.val) := by decide
  exact checked n

theorem encode_signed_offset (n : Fin 152) :
    ByteIndex.encodeScriptNum (Int.ofNat (151 + n.val)) =
      some (signedOffset n) := by
  have checked : ∀ i : Fin 152,
      ByteIndex.encodeScriptNum (Int.ofNat (151 + i.val)) =
        some (signedOffset i) := by decide
  exact checked n

theorem parse_signed_offset (n : Fin 152) :
    ByteIndex.parseScriptNum (signedOffset n) =
      some (Int.ofNat (151 + n.val)) := by
  have checked : ∀ i : Fin 152,
      ByteIndex.parseScriptNum (signedOffset i) =
        some (Int.ofNat (151 + i.val)) := by decide
  exact checked n

theorem canonical_index_small :
    ∀ n : Fin 152, (canonicalIndex n).length ≤ 4 := by decide

/-- An in-range first signed roll can match a HASH160 output only at one of
the lock's 150 HORS commitment cells. The values 0 and 1 select shallower
non-20-byte data and therefore cannot match. -/
theorem inrange_hash_hit_has_commitment_origin (hashes : Hashes)
    (opening : Bytes) (tail : List Bytes) (n : Fin 152)
    (hit : (canonicalIndex n :: (fixedRegion ++ tail))[151 + n.val]? =
      some (hashes.h160 opening)) :
    ∃ i : Fin 150,
      n.val = 2 + i.val ∧
      fixedRegion[152 + i.val]? = some (hashes.h160 opening) := by
  have within : 151 + n.val ≤ 302 := by
    have bound := n.isLt
    omega
  obtain ⟨i, index, cell⟩ :=
    FirstIndexMap.fixed_region_hash_hit_has_commitment_origin hashes
      opening (canonicalIndex n) tail (151 + n.val)
      (canonical_index_small n) within hit
  refine ⟨i, ?_, cell⟩
  omega

theorem inrange_index_min_step (hashes : Hashes)
    (raw : Bytes) (n : Fin 152) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n.val))
    (budget : cost + 1 ≤ 201) :
    step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: stack) outcomes cost) =
      some (State.mk (canonicalIndex n :: stack) outcomes (cost + 1)) := by
  unfold step
  have within : ¬ (cost + 1 > 201) := by omega
  simp [within, ByteIndex.positive_152, parsed]
  change ((ByteIndex.encodeScriptNum (Int.ofNat n.val)).bind fun value =>
    some (State.mk (value :: stack) outcomes (cost + 1))) =
    some (State.mk (canonicalIndex n :: stack) outcomes (cost + 1))
  rw [encode_canonical_index]
  simp

theorem inrange_index_add_step (hashes : Hashes)
    (n : Fin 152) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (budget : cost + 1 ≤ 201) :
    step hashes .add
      (State.mk ([0x97, 0x00] :: canonicalIndex n :: stack)
        outcomes cost) =
      some (State.mk (signedOffset n :: stack) outcomes (cost + 1)) := by
  unfold step
  have within : ¬ (cost + 1 > 201) := by omega
  have total : (151 : Int) + Int.ofNat n.val =
      Int.ofNat (151 + n.val) := by norm_cast
  simp [within, parse_151, parse_canonical_index]
  change ((ByteIndex.encodeScriptNum ((151 : Int) + Int.ofNat n.val)).bind
    fun value => some (State.mk (value :: stack) outcomes (cost + 1))) =
    some (State.mk (signedOffset n :: stack) outcomes (cost + 1))
  rw [total, encode_signed_offset]
  simp

theorem inrange_index_roll_step (hashes : Hashes)
    (n : Fin 152) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (budget : cost + 1 ≤ 201) :
    step hashes .roll
      (State.mk (signedOffset n :: stack) outcomes cost) =
      (KeyRolls.rollAt (151 + n.val) stack).map
        (fun next => State.mk next outcomes (cost + 1)) := by
  apply byte_roll_matches_list_roll hashes (signedOffset n)
    (151 + n.val) stack outcomes cost
  · exact parse_signed_offset n
  · exact budget

theorem inrange_first_index_prefix (hashes : Hashes)
    (raw : Bytes) (n : Fin 152) (tail : List Bytes)
    (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n.val))
    (small : tail.length ≤ 696) :
    run hashes firstIndexPrefix
      (State.mk (fixedRegion ++ raw :: tail) outcomes 5) =
      some (State.mk (canonicalIndex n :: (fixedRegion ++ tail))
        outcomes 7) := by
  rw [first_index_prefix_opcodes]
  unfold run step
  simp
  constructor
  · rw [fixed_region_length]
    omega
  · unfold run
    rw [byte_roll_matches_list_roll hashes [0x2e, 0x01] 302
      (fixedRegion ++ raw :: tail) outcomes 5 (by decide) (by omega)]
    rw [first_index_roll_any_tail]
    simp
    constructor
    · rw [fixed_region_length]
      omega
    · unfold run
      unfold step
      simp
      constructor
      · rw [fixed_region_length]
        omega
      · unfold run
        rw [inrange_index_min_step hashes raw n (fixedRegion ++ tail)
          outcomes 6 parsed (by omega)]
        simp
        rw [fixed_region_length]
        constructor
        · omega
        · rfl

/-- The actual byte-machine roll, when it puts a HASH160-sized opening hash
on top, has selected one of the 150 lock commitments. -/
theorem inrange_roll_hash_hit_has_commitment_origin (hashes : Hashes)
    (opening : Bytes) (tail rest : List Bytes) (n : Fin 152)
    (outcomes : List Bool) (cost : Nat)
    (budget : cost + 1 ≤ 201)
    (rolled : step hashes .roll
      (State.mk (signedOffset n :: (canonicalIndex n :: (fixedRegion ++ tail)))
        outcomes cost) =
      some (State.mk (hashes.h160 opening :: rest) outcomes (cost + 1))) :
    ∃ i : Fin 150,
      n.val = 2 + i.val ∧
      fixedRegion[152 + i.val]? = some (hashes.h160 opening) := by
  rw [inrange_index_roll_step hashes n
    (canonicalIndex n :: (fixedRegion ++ tail)) outcomes cost budget] at rolled
  unfold KeyRolls.rollAt at rolled
  cases selected : (canonicalIndex n :: (fixedRegion ++ tail))[151 + n.val]? with
  | none => simp [selected] at rolled
  | some cell =>
      simp [selected] at rolled
      have hit : (canonicalIndex n :: (fixedRegion ++ tail))[151 + n.val]? =
          some (hashes.h160 opening) := by
        rw [selected]
        congr 1
        exact rolled.1
      exact inrange_hash_hit_has_commitment_origin hashes opening tail n hit

/-- Explicit local-step extraction for any raw encoding of an in-range
nonnegative first index. The retained bytes and computed offset need not be
assumed canonical: the successful MIN and ADD steps determine them. -/
theorem inrange_first_roll_has_commitment_origin (hashes : Hashes)
    (raw retained offset opening : Bytes) (tail rest : List Bytes)
    (n : Fin 152) (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n.val))
    (minResult : step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: (fixedRegion ++ tail)) outcomes 6) =
      some (State.mk (retained :: (fixedRegion ++ tail)) outcomes 7))
    (addResult : step hashes .add
      (State.mk ([0x97, 0x00] :: retained :: retained :: (fixedRegion ++ tail))
        outcomes 8) =
      some (State.mk (offset :: retained :: (fixedRegion ++ tail)) outcomes 9))
    (rollResult : step hashes .roll
      (State.mk (offset :: retained :: (fixedRegion ++ tail)) outcomes 9) =
      some (State.mk (hashes.h160 opening :: rest) outcomes 10)) :
    ∃ i : Fin 150,
      n.val = 2 + i.val ∧
      fixedRegion[152 + i.val]? = some (hashes.h160 opening) := by
  have minExact := inrange_index_min_step hashes raw n
    (fixedRegion ++ tail) outcomes 6 parsed (by omega)
  rw [minExact] at minResult
  have retainedEq : retained = canonicalIndex n := by
    simpa using minResult.symm
  subst retained
  have addExact := inrange_index_add_step hashes n
    (canonicalIndex n :: (fixedRegion ++ tail)) outcomes 8 (by omega)
  rw [addExact] at addResult
  have offsetEq : offset = signedOffset n := by
    simpa using addResult.symm
  subst offset
  exact inrange_roll_hash_hit_has_commitment_origin hashes opening tail rest
    n outcomes 9 (by omega) rollResult

end QSB.FirstNumericRange
