import QSB.FirstNumericRange

/-!
The first signed selection for negative ScriptNum values -1 through -151.
These are the only negative values whose subsequent addition of 151 can
produce a nonnegative OP_ROLL depth. All statements here concern the local
byte machine; the remaining more-negative range and Core refinement are
separate obligations.
-/
namespace QSB.FirstNegativeRange
open ByteMachine
open FirstOvershoot
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def negativeValue (n : Fin 151) : Int := -Int.ofNat (n.val + 1)

def canonicalNegative (n : Fin 151) : Bytes :=
  (ByteIndex.encodeScriptNum (negativeValue n)).getD []

def negativeRollDepth (n : Fin 151) : Nat := 150 - n.val

def encodedRollDepth (n : Fin 151) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (negativeRollDepth n))).getD []

theorem negative_roundtrip :
    ∀ n : Fin 151,
      ByteIndex.parseScriptNum (canonicalNegative n) =
        some (negativeValue n) := by decide

theorem negative_encode :
    ∀ n : Fin 151,
      ByteIndex.encodeScriptNum (negativeValue n) =
        some (canonicalNegative n) := by decide

theorem depth_roundtrip :
    ∀ n : Fin 151,
      ByteIndex.parseScriptNum (encodedRollDepth n) =
        some (Int.ofNat (negativeRollDepth n)) := by decide

theorem depth_encode :
    ∀ n : Fin 151,
      ByteIndex.encodeScriptNum (Int.ofNat (negativeRollDepth n)) =
        some (encodedRollDepth n) := by decide

theorem negative_arithmetic :
    ∀ n : Fin 151,
      min (152 : Int) (negativeValue n) = negativeValue n ∧
      (151 : Int) + negativeValue n =
        Int.ofNat (negativeRollDepth n) := by decide

theorem negative_canonical_small :
    ∀ n : Fin 151, (canonicalNegative n).length ≤ 4 := by decide

theorem negative_index_min_step (hashes : Hashes)
    (raw : Bytes) (n : Fin 151) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (parsed : ByteIndex.parseScriptNum raw = some (negativeValue n))
    (budget : cost + 1 ≤ 201) :
    step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: stack) outcomes cost) =
      some (State.mk (canonicalNegative n :: stack) outcomes (cost + 1)) := by
  unfold step
  have within : ¬ (cost + 1 > 201) := by omega
  simp [within, ByteIndex.positive_152, parsed,
    (negative_arithmetic n).1]
  change ((ByteIndex.encodeScriptNum (negativeValue n)).bind fun value =>
    some (State.mk (value :: stack) outcomes (cost + 1))) =
    some (State.mk (canonicalNegative n :: stack) outcomes (cost + 1))
  rw [negative_encode n]
  simp

theorem negative_index_add_step (hashes : Hashes)
    (n : Fin 151) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (budget : cost + 1 ≤ 201) :
    step hashes .add
      (State.mk ([0x97, 0x00] :: canonicalNegative n :: stack)
        outcomes cost) =
      some (State.mk (encodedRollDepth n :: stack) outcomes (cost + 1)) := by
  unfold step
  have within : ¬ (cost + 1 > 201) := by omega
  simp [within, parse_151, negative_roundtrip n]
  change ((ByteIndex.encodeScriptNum ((151 : Int) + negativeValue n)).bind
    fun value => some (State.mk (value :: stack) outcomes (cost + 1))) =
    some (State.mk (encodedRollDepth n :: stack) outcomes (cost + 1))
  rw [(negative_arithmetic n).2, depth_encode n]
  simp

theorem negative_index_roll_step (hashes : Hashes)
    (n : Fin 151) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (budget : cost + 1 ≤ 201) :
    step hashes .roll
      (State.mk (encodedRollDepth n :: stack) outcomes cost) =
      (KeyRolls.rollAt (negativeRollDepth n) stack).map
        (fun next => State.mk next outcomes (cost + 1)) := by
  apply byte_roll_matches_list_roll hashes (encodedRollDepth n)
    (negativeRollDepth n) stack outcomes cost
  · exact depth_roundtrip n
  · exact budget

theorem negative_first_index_prefix (hashes : Hashes)
    (raw : Bytes) (n : Fin 151) (tail : List Bytes)
    (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some (negativeValue n))
    (small : tail.length ≤ 696) :
    run hashes firstIndexPrefix
      (State.mk (fixedRegion ++ raw :: tail) outcomes 5) =
      some (State.mk (canonicalNegative n :: (fixedRegion ++ tail))
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
        rw [negative_index_min_step hashes raw n (fixedRegion ++ tail)
          outcomes 6 parsed (by omega)]
        simp
        rw [fixed_region_length]
        constructor
        · omega
        · rfl

theorem negative_roll_cannot_hash_match (hashes : Hashes)
    (opening : Bytes) (tail : List Bytes) (n : Fin 151) :
    (canonicalNegative n :: (fixedRegion ++ tail))[negativeRollDepth n]? ≠
      some (hashes.h160 opening) := by
  intro hit
  have within : negativeRollDepth n ≤ 302 := by
    simp [negativeRollDepth]
    omega
  obtain ⟨i, index, _cell⟩ :=
    FirstIndexMap.fixed_region_hash_hit_has_commitment_origin hashes
      opening (canonicalNegative n) tail (negativeRollDepth n)
      (negative_canonical_small n) within hit
  have bound := n.isLt
  simp [negativeRollDepth] at index
  omega

theorem negative_roll_step_cannot_yield_hash (hashes : Hashes)
    (opening : Bytes) (tail rest : List Bytes) (n : Fin 151)
    (outcomes : List Bool) (cost : Nat)
    (budget : cost + 1 ≤ 201) :
    step hashes .roll
      (State.mk
        (encodedRollDepth n :: (canonicalNegative n :: (fixedRegion ++ tail)))
        outcomes cost) ≠
      some (State.mk (hashes.h160 opening :: rest) outcomes (cost + 1)) := by
  intro rolled
  rw [negative_index_roll_step hashes n
    (canonicalNegative n :: (fixedRegion ++ tail)) outcomes cost budget] at rolled
  unfold KeyRolls.rollAt at rolled
  cases selected :
      (canonicalNegative n :: (fixedRegion ++ tail))[negativeRollDepth n]? with
  | none => simp [selected] at rolled
  | some cell =>
      simp [selected] at rolled
      have hit :
          (canonicalNegative n :: (fixedRegion ++ tail))[negativeRollDepth n]? =
            some (hashes.h160 opening) := by
        rw [selected]
        congr 1
        exact rolled.1
      exact (negative_roll_cannot_hash_match hashes opening tail n) hit

end QSB.FirstNegativeRange
