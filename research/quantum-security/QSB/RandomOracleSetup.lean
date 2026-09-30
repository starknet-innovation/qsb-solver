import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
A finite random-function fact for the setup exception. Sampling a full
function `R : X → Y` uniformly makes `R x` uniform for each input `x`, even
when `x` is chosen by independent setup material (e.g. a SHA-256 oracle and
an honest HORS secret). It does not claim independence between commitments
that may address the same `R` input, nor model quantum queries after setup.
-/
namespace QSB.RandomOracleSetup

def splitAt {X Y : Type*} [DecidableEq X] (x : X) :
    (X → Y) ≃ Y × ({z : X // z ≠ x} → Y) where
  toFun f := (f x, fun z => f z.val)
  invFun p := fun z => if h : z = x then p.1 else p.2 ⟨z, h⟩
  left_inv f := by
    funext z
    by_cases h : z = x
    · subst z
      simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext z
      simp [z.property]

/-- An exact cardinality identity for a uniform random function evaluated
at a fixed input. This is counting, not a QROM query-success theorem. -/
theorem fixed_input_hit_count {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (x : X) (target : Finset Y) :
    ((Finset.univ.filter fun f : X → Y => f x ∈ target).card) *
        Fintype.card Y =
      Fintype.card (X → Y) * target.card := by
  classical
  let hit := {f : X → Y // f x ∈ target}
  let targetType := {y : Y // y ∈ target}
  letI : Fintype {z : X // z ≠ x} := Fintype.ofFinite _
  letI : Fintype hit := Fintype.ofFinite hit
  letI : Fintype targetType := Fintype.ofFinite targetType
  let hitEquiv : hit ≃ targetType × ({z : X // z ≠ x} → Y) := {
    toFun f := (⟨f.val x, f.property⟩,
      fun z => f.val z.val)
    invFun p := ⟨(splitAt x).symm (p.1.val, p.2), by
      simp [splitAt]⟩
    left_inv f := by
      apply Subtype.ext
      exact (splitAt x).left_inv f.val
    right_inv p := by
      apply Prod.ext
      · apply Subtype.ext
        simp [splitAt]
      · funext z
        simp [splitAt, z.property]
  }
  have hitCard : Fintype.card hit =
      target.card * Fintype.card ({z : X // z ≠ x} → Y) := by
    rw [Fintype.card_congr hitEquiv]
    simp [targetType, Fintype.card_subtype]
  have allCard : Fintype.card (X → Y) =
      Fintype.card Y * Fintype.card ({z : X // z ≠ x} → Y) := by
    rw [Fintype.card_congr (splitAt x)]
    simp
  rw [← Fintype.card_subtype (fun f : X → Y => f x ∈ target)]
  rw [hitCard, allCard]
  ac_rfl

/-- Let all randomness used to choose the input be represented by `Ξ`. If
the entire random function is sampled independently and uniformly, evaluating
it at `source ξ` has exactly the target density, even when different `ξ` lead
to colliding inputs. This is a classical setup marginal, not an adaptive or
quantum query bound. -/
theorem independent_source_hit_count {Ξ X Y : Type*}
    [Fintype Ξ] [DecidableEq Ξ] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (source : Ξ → X) (target : Finset Y) :
    ((Finset.univ.filter fun p : Ξ × (X → Y) =>
      p.2 (source p.1) ∈ target).card) * Fintype.card Y =
      Fintype.card (Ξ × (X → Y)) * target.card := by
  classical
  let fiber (ξ : Ξ) := {f : X → Y // f (source ξ) ∈ target}
  let hit := {p : Ξ × (X → Y) // p.2 (source p.1) ∈ target}
  letI : Fintype hit := Fintype.ofFinite hit
  letI : ∀ ξ : Ξ, Fintype (fiber ξ) := fun ξ => Fintype.ofFinite (fiber ξ)
  let hitEquiv : hit ≃ (Σ ξ : Ξ, fiber ξ) := {
    toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
    invFun p := ⟨(p.1, p.2.val), p.2.property⟩
    left_inv p := by cases p; rfl
    right_inv p := by cases p; rfl
  }
  have each (ξ : Ξ) : Fintype.card (fiber ξ) * Fintype.card Y =
      Fintype.card (X → Y) * target.card := by
    simpa [fiber, Fintype.card_subtype] using
      fixed_input_hit_count (source ξ) target
  rw [← Fintype.card_subtype
    (fun p : Ξ × (X → Y) => p.2 (source p.1) ∈ target)]
  rw [Fintype.card_congr hitEquiv, Fintype.card_sigma,
    Finset.sum_mul]
  simp_rw [each]
  simp [Fintype.card_prod, Finset.sum_const]
  ac_rfl

/-- A finite collection of setup-dependent inputs may all address the same
random function. The union bound needs no independence between their outputs;
the only independence is between the setup material and the sampled function.
The inequality is written in integer counts to avoid a probability-space
normalization premise. -/
theorem shared_function_union_hit_count {I Ξ X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ξ] [DecidableEq Ξ]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (source : I → Ξ → X) (target : Finset Y) :
    ((Finset.univ.filter fun p : Ξ × (X → Y) =>
      ∃ i : I, p.2 (source i p.1) ∈ target).card) * Fintype.card Y ≤
      Fintype.card I * (Fintype.card (Ξ × (X → Y)) * target.card) := by
  classical
  let hit (i : I) : Finset (Ξ × (X → Y)) :=
    Finset.univ.filter fun p => p.2 (source i p.1) ∈ target
  have subset : (Finset.univ.filter fun p : Ξ × (X → Y) =>
      ∃ i : I, p.2 (source i p.1) ∈ target) ⊆
      Finset.univ.biUnion hit := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨i, hi⟩ := hp
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  calc
    _ ≤ ((∑ i : I, (hit i).card) * Fintype.card Y) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_le_card subset).trans Finset.card_biUnion_le
    _ = ∑ i : I, ((hit i).card * Fintype.card Y) := by
      rw [Finset.sum_mul]
    _ = ∑ _i : I, (Fintype.card (Ξ × (X → Y)) * target.card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact independent_source_hit_count (source i) target
    _ = _ := by simp

end QSB.RandomOracleSetup
