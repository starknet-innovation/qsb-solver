import QSB.TaggedLocalResponses

/-!
Finite combinatorial recognition of a newly created projected collision after
one parallel batch of queried inputs. A partial database maps an input to an
optional recorded response. If a collision-free database changes only at the
queried inputs and gains a collision, then the collision either joins two
distinct queried inputs or joins one queried input to an old outside entry.
In the second case, the new response belongs to the local response union
whose size is bounded by `TaggedLocalResponses`.

This is the classical strong-local-recognizability step of the collision
example in Chung–Fehr–Huang–Liao. It does not define compressed-oracle
database states, bound a quantum transition capacity, or charge coherent
queries. The supplied list must cover the populated old entries outside the
queried batch; no oracle-independent algorithm is constructed here.
-/
namespace QSB.TaggedCollisionTransition
open QSB.TaggedLocalResponses
open QSB.TaggedOracle (Bits projectedH projectedR)

/-- A populated collision at two distinct input coordinates. -/
def HasCollision {I Resp T : Type*} (f : I → Resp → T)
    (database : I → Option Resp) : Prop :=
  ∃ a b : I, a ≠ b ∧ ∃ ya yb : Resp,
    database a = some ya ∧ database b = some yb ∧ f a ya = f b yb

section General

variable {I Resp T : Type*} [Fintype Resp] [DecidableEq I]
  [DecidableEq Resp] [DecidableEq T] {k : Nat}

/-- A new collision is recognized by at most two queried inputs, or by one
queried response and a populated old database entry outside the batch.
The changed-response witness is explicit in both alternatives. -/
theorem new_collision_local
    (f : I → Resp → T) (before after : I → Option Resp)
    (queries : Fin k → I) (db : List (I × Resp))
    (sameOutside : ∀ z, z ∉ Set.range queries → after z = before z)
    (outsideCovered : ∀ z yz, z ∉ Set.range queries →
      before z = some yz → (z, yz) ∈ db)
    (beforeClean : ¬ HasCollision f before)
    (afterCollision : HasCollision f after) :
    (∃ i j : Fin k, queries i ≠ queries j ∧
      after (queries i) ≠ before (queries i) ∧
      ∃ yi yj : Resp,
        after (queries i) = some yi ∧ after (queries j) = some yj ∧
        f (queries i) yi = f (queries j) yj ∧
        yi ∈ pairResponses f (queries i) (queries j) yj) ∨
    (∃ i : Fin k, ∃ z : I, ∃ yi yz : Resp,
      z ∉ Set.range queries ∧ queries i ≠ z ∧
      before z = some yz ∧ after (queries i) = some yi ∧
      f (queries i) yi = f z yz ∧
      after (queries i) ≠ before (queries i) ∧
      (z, yz) ∈ db ∧
      yi ∈ databaseResponses f (queries i) db) := by
  classical
  rcases afterCollision with ⟨a, b, distinct, ya, yb, afterA, afterB, same⟩
  have changed : after a ≠ before a ∨ after b ≠ before b := by
    by_contra notChanged
    have sameA : after a = before a := by
      by_contra neq
      exact notChanged (Or.inl neq)
    have sameB : after b = before b := by
      by_contra neq
      exact notChanged (Or.inr neq)
    apply beforeClean
    refine ⟨a, b, distinct, ya, yb, ?_, ?_, same⟩
    · rw [← sameA]
      exact afterA
    · rw [← sameB]
      exact afterB
  by_cases aInside : a ∈ Set.range queries
  · rcases aInside with ⟨i, hi⟩
    by_cases bInside : b ∈ Set.range queries
    · rcases bInside with ⟨j, hj⟩
      left
      rcases changed with changedA | changedB
      · refine ⟨i, j, ?_, ?_, ya, yb, ?_, ?_, ?_, ?_⟩
        · simpa [hi, hj] using distinct
        · simpa [hi] using changedA
        · simpa [hi] using afterA
        · simpa [hj] using afterB
        · simpa [hi, hj] using same
        · exact (mem_pairResponses f (queries i) (queries j) yb ya).2
            (by simpa [hi, hj] using same)
      · refine ⟨j, i, ?_, ?_, yb, ya, ?_, ?_, ?_, ?_⟩
        · simpa [hi, hj] using distinct.symm
        · simpa [hj] using changedB
        · simpa [hj] using afterB
        · simpa [hi] using afterA
        · simpa [hi, hj] using same.symm
        · exact (mem_pairResponses f (queries j) (queries i) ya yb).2
            (by simpa [hi, hj] using same.symm)
    · right
      have oldB : before b = some yb := by
        rw [← sameOutside b bInside]
        exact afterB
      have changedA : after a ≠ before a := by
        rcases changed with h | h
        · exact h
        · exact False.elim (h (sameOutside b bInside))
      have recorded := outsideCovered b yb bInside oldB
      refine ⟨i, b, ya, yb, bInside, ?_, oldB, ?_, ?_, ?_, recorded, ?_⟩
      · simpa [hi] using distinct
      · simpa [hi] using afterA
      · simpa [hi] using same
      · simpa [hi] using changedA
      · exact collision_mem_databaseResponses f (queries i) db ya
          (b, yb) recorded (by simpa [hi] using same)
  · by_cases bInside : b ∈ Set.range queries
    · rcases bInside with ⟨i, hi⟩
      right
      have oldA : before a = some ya := by
        rw [← sameOutside a aInside]
        exact afterA
      have changedB : after b ≠ before b := by
        rcases changed with h | h
        · exact False.elim (h (sameOutside a aInside))
        · exact h
      have recorded := outsideCovered a ya aInside oldA
      refine ⟨i, a, yb, ya, aInside, ?_, oldA, ?_, ?_, ?_, recorded, ?_⟩
      · simpa [hi] using distinct.symm
      · simpa [hi] using afterB
      · simpa [hi] using same.symm
      · simpa [hi] using changedB
      · exact collision_mem_databaseResponses f (queries i) db yb
          (a, ya) recorded (by simpa [hi] using same.symm)
    · exact False.elim (changed.elim
        (fun h => h (sameOutside a aInside))
        (fun h => h (sameOutside b bInside)))

end General

section Projected

variable {X : Type*} [DecidableEq X] {k : Nat}

/-- The transition recognition theorem for the tagged first-coordinate
projection, whose local pair fibers have size `2^160`. -/
theorem projectedH_new_collision_local
    (before after : Sum X X → Option (Bits 256 × Bits 160))
    (queries : Fin k → Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160)))
    (sameOutside : ∀ z, z ∉ Set.range queries → after z = before z)
    (outsideCovered : ∀ z yz, z ∉ Set.range queries →
      before z = some yz → (z, yz) ∈ db)
    (beforeClean : ¬ HasCollision (projectedH (X := X)) before)
    (afterCollision : HasCollision (projectedH (X := X)) after) :
    (∃ i j : Fin k, queries i ≠ queries j ∧
      after (queries i) ≠ before (queries i) ∧
      ∃ yi yj : Bits 256 × Bits 160,
        after (queries i) = some yi ∧ after (queries j) = some yj ∧
        projectedH (queries i) yi = projectedH (queries j) yj ∧
        yi ∈ pairResponses (projectedH (X := X))
          (queries i) (queries j) yj) ∨
    (∃ i : Fin k, ∃ z : Sum X X,
      ∃ yi yz : Bits 256 × Bits 160,
      z ∉ Set.range queries ∧ queries i ≠ z ∧
      before z = some yz ∧ after (queries i) = some yi ∧
      projectedH (queries i) yi = projectedH z yz ∧
      after (queries i) ≠ before (queries i) ∧
      (z, yz) ∈ db ∧
      yi ∈ databaseResponses (projectedH (X := X)) (queries i) db) :=
  new_collision_local (projectedH (X := X)) before after queries db
    sameOutside outsideCovered beforeClean afterCollision

/-- The corresponding transition recognition theorem for the tagged
second-coordinate projection, whose local pair fibers have size `2^256`. -/
theorem projectedR_new_collision_local
    (before after : Sum X X → Option (Bits 256 × Bits 160))
    (queries : Fin k → Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160)))
    (sameOutside : ∀ z, z ∉ Set.range queries → after z = before z)
    (outsideCovered : ∀ z yz, z ∉ Set.range queries →
      before z = some yz → (z, yz) ∈ db)
    (beforeClean : ¬ HasCollision (projectedR (X := X)) before)
    (afterCollision : HasCollision (projectedR (X := X)) after) :
    (∃ i j : Fin k, queries i ≠ queries j ∧
      after (queries i) ≠ before (queries i) ∧
      ∃ yi yj : Bits 256 × Bits 160,
        after (queries i) = some yi ∧ after (queries j) = some yj ∧
        projectedR (queries i) yi = projectedR (queries j) yj ∧
        yi ∈ pairResponses (projectedR (X := X))
          (queries i) (queries j) yj) ∨
    (∃ i : Fin k, ∃ z : Sum X X,
      ∃ yi yz : Bits 256 × Bits 160,
      z ∉ Set.range queries ∧ queries i ≠ z ∧
      before z = some yz ∧ after (queries i) = some yi ∧
      projectedR (queries i) yi = projectedR z yz ∧
      after (queries i) ≠ before (queries i) ∧
      (z, yz) ∈ db ∧
      yi ∈ databaseResponses (projectedR (X := X)) (queries i) db) :=
  new_collision_local (projectedR (X := X)) before after queries db
    sameOutside outsideCovered beforeClean afterCollision

end Projected

end QSB.TaggedCollisionTransition
