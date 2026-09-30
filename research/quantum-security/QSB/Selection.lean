import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

/-!
Local stack-selection lemmas. These expose the invariant needed by the QSB
selection loop: the allowed index range ends at the commitment pool, and every
earlier item has a length different from HASH160's 20-byte result. The production
loop invariant and arbitrary initial scriptSig stack are not yet formalized.
-/
namespace QSB

/-- OP_MIN clamps large positive indices; it does not reject them. A following
successful OP_ROLL also supplies a nonnegative-index requirement. -/
theorem min_roll_bounds (raw cap : Int) (accepted : 0 ≤ min raw cap) :
    0 ≤ raw ∧ 0 ≤ cap ∧ min raw cap ≤ cap := by
  exact ⟨(Int.le_min.mp accepted).1, (Int.le_min.mp accepted).2,
    Int.min_le_right raw cap⟩

/-- If a successful hash comparison selects an item within prefix+pool, and no
prefix item is 20 bytes, the compared item belongs to the pool. The suffix may
contain arbitrary attacker-controlled values, including 20-byte ones. -/
theorem comparison_selects_pool {Item : Type*}
    (width : Item → Nat) (before pool suffix : List Item) (index : Nat) (x : Item)
    (bounded : index < (before ++ pool).length)
    (selected : ((before ++ pool) ++ suffix)[index]? = some x)
    (hashWidth : width x = 20)
    (prefixWidths : ∀ y ∈ before, width y ≠ 20) : x ∈ pool := by
  have h : (before ++ pool)[index]? = some x := by
    exact (List.getElem?_append_left (l₂ := suffix) bounded).symm.trans selected
  have member := List.mem_of_getElem? h
  rcases List.mem_append.mp member with outside | inside
  · exact False.elim (prefixWidths x outside hashWidth)
  · exact inside

/-- Removing a commitment from a pool of distinct tagged positions preserves
distinctness of the remaining positions. Tags are positions, not hash values:
commitment collisions must not be silently excluded by this invariant. -/
theorem distinct_positions_after_roll {Index : Type*} (pool : List Index)
    (index : Nat) (distinct : pool.Nodup) : (pool.eraseIdx index).Nodup := by
  exact List.Nodup.eraseIdx index distinct

/-- Abstract only the part of successive `OP_ROLL` selections that removes a
tagged pool position. It does not assert that the production Script always
selects from this pool. -/
def chooseMany {Index : Type*} : List Nat → List Index → Option (List Index × List Index)
  | [], pool => some ([], pool)
  | k :: ks, pool => do
      let x ← pool[k]?
      let (chosen, remaining) ← chooseMany ks (pool.eraseIdx k)
      pure (x :: chosen, remaining)

theorem selected_not_in_erased {Index : Type*} {pool : List Index}
    (distinct : pool.Nodup) {k : Nat} {x : Index}
    (selected : pool[k]? = some x) : x ∉ pool.eraseIdx k := by
  intro h
  obtain ⟨j, different, other⟩ := List.mem_eraseIdx_iff_getElem?.mp h
  have inRange : k < pool.length := (List.getElem?_eq_some_iff.mp selected).1
  have equal : k = j := (List.getElem?_inj inRange distinct).mp (selected.trans other.symm)
  exact different equal.symm

theorem chooseMany_values_in_pool {Index : Type*}
    {indices : List Nat} {pool chosen remaining : List Index}
    (run : chooseMany indices pool = some (chosen, remaining)) :
    (∀ x ∈ chosen, x ∈ pool) ∧ (∀ x ∈ remaining, x ∈ pool) := by
  induction indices generalizing pool chosen remaining with
  | nil =>
      simp [chooseMany] at run
      rcases run with ⟨rfl, rfl⟩
      simp
  | cons k ks ih =>
      simp only [chooseMany] at run
      cases hget : pool[k]? with
      | none => simp [hget] at run
      | some x =>
          simp only [hget] at run
          cases htail : chooseMany ks (pool.eraseIdx k) with
          | none => simp [htail] at run
          | some result =>
              rcases result with ⟨tail, rest⟩
              simp only [htail] at run
              cases run
              obtain ⟨tailIn, restIn⟩ := ih htail
              constructor
              · intro y hy
                rcases List.mem_cons.mp hy with rfl | hy
                · exact List.mem_of_getElem? hget
                · exact List.eraseIdx_subset (tailIn y hy)
              · intro y hy
                exact List.eraseIdx_subset (restIn y hy)

theorem chooseMany_distinct {Index : Type*}
    {indices : List Nat} {pool chosen remaining : List Index}
    (distinct : pool.Nodup)
    (run : chooseMany indices pool = some (chosen, remaining)) :
    chosen.Nodup := by
  induction indices generalizing pool chosen remaining with
  | nil =>
      simp [chooseMany] at run
      rcases run with ⟨rfl, rfl⟩
      simp
  | cons k ks ih =>
      simp only [chooseMany] at run
      cases hget : pool[k]? with
      | none => simp [hget] at run
      | some x =>
          simp only [hget] at run
          cases htail : chooseMany ks (pool.eraseIdx k) with
          | none => simp [htail] at run
          | some result =>
              rcases result with ⟨tail, rest⟩
              simp only [htail] at run
              cases run
              apply List.nodup_cons.mpr
              constructor
              · intro member
                have inside := (chooseMany_values_in_pool htail).1 x member
                exact selected_not_in_erased distinct hget inside
              · exact ih (List.Nodup.eraseIdx k distinct) htail

/-- Successful selection yields exactly one tag per index consumed, independent
of the values of those indices. Combined with `chooseMany_distinct`, this gives
the abstract nine-distinct-position obligation for a nine-step pool traversal. -/
theorem chooseMany_length {Index : Type*}
    {indices : List Nat} {pool chosen remaining : List Index}
    (run : chooseMany indices pool = some (chosen, remaining)) :
    chosen.length = indices.length := by
  induction indices generalizing pool chosen remaining with
  | nil =>
      simp [chooseMany] at run
      rcases run with ⟨rfl, rfl⟩
      rfl
  | cons k ks ih =>
      simp only [chooseMany] at run
      cases hget : pool[k]? with
      | none => simp [hget] at run
      | some x =>
          simp only [hget] at run
          cases htail : chooseMany ks (pool.eraseIdx k) with
          | none => simp [htail] at run
          | some result =>
              rcases result with ⟨tail, rest⟩
              simp only [htail] at run
              cases run
              simp [ih htail]

/-- Under the abstract pool traversal, partitioning nine selections after the
seventh yields exactly the Config A final-round cardinalities and disjointness.
The Script-to-`chooseMany` refinement is not established here. -/
theorem nine_selected_partition {Index : Type*} [DecidableEq Index]
    {indices : List Nat} {pool chosen remaining : List Index}
    (distinct : pool.Nodup) (nine : indices.length = 9)
    (run : chooseMany indices pool = some (chosen, remaining)) :
    (chosen.take 7).toFinset.card = 7 ∧
    (chosen.drop 7).toFinset.card = 2 ∧
    Disjoint (chosen.take 7).toFinset (chosen.drop 7).toFinset := by
  have hnodup := chooseMany_distinct distinct run
  have hlength : chosen.length = 9 := (chooseMany_length run).trans nine
  constructor
  · rw [List.toFinset_card_of_nodup ((List.take_sublist 7 chosen).nodup hnodup),
      List.length_take, hlength]
    decide
  constructor
  · rw [List.toFinset_card_of_nodup ((List.drop_sublist 7 chosen).nodup hnodup),
      List.length_drop, hlength]
  · exact List.disjoint_toFinset_iff_disjoint.mpr
      (List.disjoint_take_drop hnodup (Nat.le_refl 7))

end QSB
