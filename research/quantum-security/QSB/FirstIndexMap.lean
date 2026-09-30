import QSB.FirstOvershoot

/-!
Literal-byte origin facts for the first signed selection's lock-pushed region.
These lemmas identify which positions are 20-byte HORS commitments and which
are other lock data. They do not assert that every accepted Script execution
uses a valid pool index; ScriptNum and later global stack behavior remain
separate obligations.
-/
namespace QSB.FirstIndexMap
open ByteMachine
open FirstOvershoot
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem shallow_cells_are_not_twenty_bytes :
    ∀ i : Fin 152,
      (fixedRegion[i.val]?).map List.length ≠ some 20 := by decide

theorem commitment_cells_are_twenty_bytes :
    ∀ i : Fin 150,
      (fixedRegion[152 + i.val]?).map List.length = some 20 := by decide

theorem first_pool_window_covers_region :
    152 + 150 = fixedRegion.length := by
  rw [fixed_region_length]

/-- After the retained index is placed above the lock-pushed region, the
first signed roll at offset `153 + i` reads exactly commitment cell `152 + i`.
The arbitrary lower stack is not consulted. -/
theorem signed_window_lookup (retained : Bytes) (tail : List Bytes)
    (i : Fin 150) :
    (retained :: (fixedRegion ++ tail))[153 + i.val]? =
      fixedRegion[152 + i.val]? := by
  have within : 152 + i.val < fixedRegion.length := by
    rw [fixed_region_length]
    omega
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (List.getElem?_append_left (l₁ := fixedRegion) (l₂ := tail) within)

theorem signed_window_cell_is_twenty_bytes (retained : Bytes)
    (tail : List Bytes) (i : Fin 150) :
    ((retained :: (fixedRegion ++ tail))[153 + i.val]?).map List.length =
      some 20 := by
  rw [signed_window_lookup]
  exact commitment_cells_are_twenty_bytes i

/-- Every shallower lock cell has a non-20-byte encoding in this generated
fixture, so it cannot equal the 20-byte output of HASH160. -/
theorem shallow_window_cell_not_twenty_bytes (retained : Bytes)
    (tail : List Bytes) (i : Fin 152) :
    ((retained :: (fixedRegion ++ tail))[1 + i.val]?).map List.length ≠
      some 20 := by
  have within : i.val < fixedRegion.length := by
    rw [fixed_region_length]
    omega
  have lookup :
      (retained :: (fixedRegion ++ tail))[1 + i.val]? =
        fixedRegion[i.val]? := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (List.getElem?_append_left (l₁ := fixedRegion) (l₂ := tail) within)
  rw [lookup]
  exact shallow_cells_are_not_twenty_bytes i

theorem signed_window_roll_has_lock_origin (retained : Bytes)
    (tail : List Bytes) (i : Fin 150) :
    ∃ cell rest,
      KeyRolls.rollAt (153 + i.val) (retained :: (fixedRegion ++ tail)) =
        some (cell :: rest) ∧
      fixedRegion[152 + i.val]? = some cell ∧ cell.length = 20 := by
  have within : 152 + i.val < fixedRegion.length := by
    rw [fixed_region_length]
    omega
  let cell := fixedRegion[152 + i.val]
  have source : fixedRegion[152 + i.val]? = some cell := by
    exact List.getElem?_eq_getElem within
  have size : cell.length = 20 := by
    have h := commitment_cells_are_twenty_bytes i
    simpa [source] using h
  refine ⟨cell, (retained :: (fixedRegion ++ tail)).eraseIdx (153 + i.val), ?_, source, size⟩
  unfold KeyRolls.rollAt
  rw [signed_window_lookup, source]
  rfl

theorem shallow_window_cannot_match_hash160 (hashes : Hashes)
    (opening retained : Bytes) (tail : List Bytes) (i : Fin 152) :
    (retained :: (fixedRegion ++ tail))[1 + i.val]? ≠
      some (hashes.h160 opening) := by
  intro hmatch
  have wrongSize := shallow_window_cell_not_twenty_bytes retained tail i
  apply wrongSize
  rw [hmatch]
  simp [hashes.h160_width]

end QSB.FirstIndexMap
