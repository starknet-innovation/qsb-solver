import QSB.TaggedLocalResponses

/-!
Finite local response sets for one coordinate of a parallel query batch.
Given other returned responses, a candidate at coordinate `i` can match a
previous database entry or a distinct queried coordinate. The union has at
most `(old entries + other queried coordinates) * Γ` responses when every
pair fiber has size at most `Γ`.

These are classical set-cardinality facts. They do not bound amplitudes of a
compressed-oracle transition, choose a reported QSB relation, or charge
coherent quantum queries.
-/
namespace QSB.ParallelLocalResponses
open QSB.TaggedLocalResponses
open QSB.TaggedOracle (Bits projectedH projectedR)

section General

variable {I Resp T : Type*} [Fintype Resp] [DecidableEq I]
  [DecidableEq Resp] [DecidableEq T] {k : Nat}

/-- Responses at queried position `i` that collide with the supplied
response at another distinct queried position. -/
def peerResponses (f : I → Resp → T) (queries : Fin k → I)
    (replies : Fin k → Option Resp) (i : Fin k) : Finset Resp :=
  (Finset.univ.erase i).biUnion fun j =>
    match replies j with
    | none => ∅
    | some yj => pairResponses f (queries i) (queries j) yj

/-- The local set for position `i` combines old-database and peer-batch
collision possibilities. The peer replies are parameters, not independent
random variables in this definition. -/
def batchResponses (f : I → Resp → T) (queries : Fin k → I)
    (replies : Fin k → Option Resp) (db : List (I × Resp))
    (i : Fin k) : Finset Resp :=
  databaseResponses f (queries i) db ∪ peerResponses f queries replies i

omit [DecidableEq I] in
theorem peerResponses_card_le (f : I → Resp → T) (Γ : Nat)
    (bound : FiberBound f Γ) (queries : Fin k → I)
    (replies : Fin k → Option Resp) (i : Fin k) :
    (peerResponses f queries replies i).card ≤ (k - 1) * Γ := by
  classical
  calc
    (peerResponses f queries replies i).card ≤
        ∑ j ∈ Finset.univ.erase i,
          (match replies j with
           | none => (∅ : Finset Resp)
           | some yj => pairResponses f (queries i) (queries j) yj).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.univ.erase i, Γ := by
      apply Finset.sum_le_sum
      intro j _
      cases h : replies j with
      | none => simp
      | some yj => simpa [h] using bound (queries i) (queries j) yj
    _ = (k - 1) * Γ := by
      simp

theorem batchResponses_card_le (f : I → Resp → T) (Γ : Nat)
    (bound : FiberBound f Γ) (queries : Fin k → I)
    (replies : Fin k → Option Resp) (db : List (I × Resp))
    (i : Fin k) :
    (batchResponses f queries replies db i).card ≤
      (db.length + (k - 1)) * Γ := by
  calc
    (batchResponses f queries replies db i).card ≤
        (databaseResponses f (queries i) db).card +
          (peerResponses f queries replies i).card :=
            Finset.card_union_le _ _
    _ ≤ db.length * Γ + (k - 1) * Γ := by
      exact Nat.add_le_add
        (databaseResponses_card_le f Γ bound (queries i) db)
        (peerResponses_card_le f Γ bound queries replies i)
    _ = (db.length + (k - 1)) * Γ := by
      rw [Nat.add_mul]

end General

section Tagged

variable {X : Type*} [DecidableEq X] {k : Nat}

theorem projectedH_batchResponses_card_le
    (queries : Fin k → Sum X X)
    (replies : Fin k → Option (Bits 256 × Bits 160))
    (db : List (Sum X X × (Bits 256 × Bits 160))) (i : Fin k) :
    (batchResponses (projectedH (X := X)) queries replies db i).card ≤
      (db.length + (k - 1)) * 2 ^ 160 :=
  batchResponses_card_le _ _ projectedH_fiberBound queries replies db i

theorem projectedR_batchResponses_card_le
    (queries : Fin k → Sum X X)
    (replies : Fin k → Option (Bits 256 × Bits 160))
    (db : List (Sum X X × (Bits 256 × Bits 160))) (i : Fin k) :
    (batchResponses (projectedR (X := X)) queries replies db i).card ≤
      (db.length + (k - 1)) * 2 ^ 256 :=
  batchResponses_card_le _ _ projectedR_fiberBound queries replies db i

end Tagged

end QSB.ParallelLocalResponses
