import QSB.TaggedCollisionTransition
import QSB.ParallelLocalResponses

/-!
Compose finite parallel collision-transition recognition with the batch local
response sets. For replies taken from the after database, a newly created
distinct-input collision forces one *changed* queried response to belong to
the local set for that same queried position. The outside-entry coverage
premise remains explicit.

This is a classical membership result. The peer replies are fixed parameters
to the local set; no independence, compressed-oracle transition capacity,
coherent query charge, or QSB success bound follows.
-/
namespace QSB.TaggedCollisionBatchLocal
open QSB.TaggedLocalResponses
open QSB.TaggedCollisionTransition
open QSB.ParallelLocalResponses
open QSB.TaggedOracle (Bits projectedH projectedR)

section General

variable {I Resp T : Type*} [Fintype Resp] [DecidableEq I]
  [DecidableEq Resp] [DecidableEq T] {k : Nat}

/-- Some changed queried response lies in its own parallel-batch local set.
The local set is formed using the actual after-state replies at every queried
position and the supplied covering list of old outside entries. -/
theorem new_collision_hits_batchResponses
    (f : I → Resp → T) (before after : I → Option Resp)
    (queries : Fin k → I) (db : List (I × Resp))
    (sameOutside : ∀ z, z ∉ Set.range queries → after z = before z)
    (outsideCovered : ∀ z yz, z ∉ Set.range queries →
      before z = some yz → (z, yz) ∈ db)
    (beforeClean : ¬ HasCollision f before)
    (afterCollision : HasCollision f after) :
    ∃ i : Fin k, ∃ yi : Resp,
      after (queries i) = some yi ∧
      after (queries i) ≠ before (queries i) ∧
      yi ∈ batchResponses f queries
        (fun j => after (queries j)) db i := by
  classical
  rcases new_collision_local f before after queries db sameOutside
      outsideCovered beforeClean afterCollision with
    pair | old
  · rcases pair with
      ⟨i, j, distinct, changed, yi, yj, afterI, afterJ, _, member⟩
    have indicesDifferent : j ≠ i := by
      intro sameIndex
      subst j
      exact distinct rfl
    have peer : yi ∈ peerResponses f queries
        (fun h => after (queries h)) i := by
      apply Finset.mem_biUnion.mpr
      refine ⟨j, ?_, ?_⟩
      · simp [indicesDifferent]
      · simpa [afterJ] using member
    refine ⟨i, yi, afterI, changed, ?_⟩
    exact Finset.mem_union.mpr (Or.inr peer)
  · rcases old with
      ⟨i, z, yi, yz, _, _, _, afterI, _, changed, _, member⟩
    refine ⟨i, yi, afterI, changed, ?_⟩
    exact Finset.mem_union.mpr (Or.inl member)

end General

section Tagged

variable {X : Type*} [DecidableEq X] {k : Nat}

/-- The changed H-projection response lies in a batch local set of at most
`(old list length + k−1)·2^160` full tagged responses. -/
theorem projectedH_new_collision_hits_batchResponses
    (before after : Sum X X → Option (Bits 256 × Bits 160))
    (queries : Fin k → Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160)))
    (sameOutside : ∀ z, z ∉ Set.range queries → after z = before z)
    (outsideCovered : ∀ z yz, z ∉ Set.range queries →
      before z = some yz → (z, yz) ∈ db)
    (beforeClean : ¬ HasCollision (projectedH (X := X)) before)
    (afterCollision : HasCollision (projectedH (X := X)) after) :
    ∃ i : Fin k, ∃ yi : Bits 256 × Bits 160,
      after (queries i) = some yi ∧
      after (queries i) ≠ before (queries i) ∧
      yi ∈ batchResponses (projectedH (X := X)) queries
        (fun j => after (queries j)) db i ∧
      (batchResponses (projectedH (X := X)) queries
        (fun j => after (queries j)) db i).card ≤
          (db.length + (k - 1)) * 2 ^ 160 := by
  obtain ⟨i, yi, afterI, changed, member⟩ :=
    new_collision_hits_batchResponses (projectedH (X := X))
      before after queries db sameOutside outsideCovered
      beforeClean afterCollision
  exact ⟨i, yi, afterI, changed, member,
    projectedH_batchResponses_card_le queries
      (fun j => after (queries j)) db i⟩

/-- The changed R-projection response lies in a batch local set of at most
`(old list length + k−1)·2^256` full tagged responses. -/
theorem projectedR_new_collision_hits_batchResponses
    (before after : Sum X X → Option (Bits 256 × Bits 160))
    (queries : Fin k → Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160)))
    (sameOutside : ∀ z, z ∉ Set.range queries → after z = before z)
    (outsideCovered : ∀ z yz, z ∉ Set.range queries →
      before z = some yz → (z, yz) ∈ db)
    (beforeClean : ¬ HasCollision (projectedR (X := X)) before)
    (afterCollision : HasCollision (projectedR (X := X)) after) :
    ∃ i : Fin k, ∃ yi : Bits 256 × Bits 160,
      after (queries i) = some yi ∧
      after (queries i) ≠ before (queries i) ∧
      yi ∈ batchResponses (projectedR (X := X)) queries
        (fun j => after (queries j)) db i ∧
      (batchResponses (projectedR (X := X)) queries
        (fun j => after (queries j)) db i).card ≤
          (db.length + (k - 1)) * 2 ^ 256 := by
  obtain ⟨i, yi, afterI, changed, member⟩ :=
    new_collision_hits_batchResponses (projectedR (X := X))
      before after queries db sameOutside outsideCovered
      beforeClean afterCollision
  exact ⟨i, yi, afterI, changed, member,
    projectedR_batchResponses_card_le queries
      (fun j => after (queries j)) db i⟩

end Tagged

end QSB.TaggedCollisionBatchLocal
