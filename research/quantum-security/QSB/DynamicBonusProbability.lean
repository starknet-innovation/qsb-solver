import QSB.DynamicBonusSetup
import Mathlib.Probability.UniformOn

/-!
Convert the finite setup count into a probability statement for the uniform
measure on a nonempty finite setup space. This is solely the DER-shaped
commitment setup exception; no quantum adversary or unauthorized-spend event
is bounded here.
-/
namespace QSB.DynamicBonusProbability
open MeasureTheory
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

theorem uniform_bad_der_probability {Ξ X : Type*}
    [Fintype Ξ] [DecidableEq Ξ] [Fintype X] [DecidableEq X]
    [MeasurableSpace (Ξ × (X → (Fin 20 → UInt8)))]
    [MeasurableSingletonClass (Ξ × (X → (Fin 20 → UInt8)))]
    [Nonempty (Ξ × (X → (Fin 20 → UInt8)))]
    (source : Fin 150 → Ξ → X) :
    ProbabilityTheory.uniformOn
      (Set.univ : Set (Ξ × (X → (Fin 20 → UInt8))))
      {p | DynamicBonusSetup.BadDERSetup source p} ≤
        (150 : ENNReal) * 12 / 256 ^ 6 := by
  classical
  let bad : Finset (Ξ × (X → (Fin 20 → UInt8))) :=
    Finset.univ.filter (DynamicBonusSetup.BadDERSetup source)
  have countBound := DynamicBonusSetup.bad_der_setup_count source
  change bad.card * Fintype.card (Fin 20 → UInt8) ≤
    150 * (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) *
      (12 * 256 ^ 14)) at countBound
  rw [DERHeaderBound.output_space_card] at countBound
  have scaled :
      (bad.card * 256 ^ 6) * 256 ^ 14 ≤
        (150 * (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) * 12)) *
          256 ^ 14 := by
    calc
      _ = bad.card * 256 ^ 20 := by ring
      _ ≤ 150 * (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) *
        (12 * 256 ^ 14)) := countBound
      _ = _ := by ring
  have natBound : bad.card * 256 ^ 6 ≤
      150 * (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) * 12) :=
    Nat.le_of_mul_le_mul_right scaled (by norm_num)
  have ennBound : (bad.card : ENNReal) * 256 ^ 6 ≤
      ((150 : ENNReal) * 12) *
        (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) : ENNReal) := by
    have castBound : (bad.card : ENNReal) * 256 ^ 6 ≤
        (150 : ENNReal) *
          ((Fintype.card (Ξ × (X → (Fin 20 → UInt8))) : ENNReal) * 12) := by
      exact_mod_cast natBound
    simpa [mul_assoc, mul_comm, mul_left_comm] using castBound
  have badSet : (↑bad : Set (Ξ × (X → (Fin 20 → UInt8)))) =
      {p | DynamicBonusSetup.BadDERSetup source p} := by
    ext p
    simp [bad]
  rw [← badSet, ProbabilityTheory.uniformOn_univ,
    Measure.count_apply_finset]
  have cardPos : 0 < Fintype.card (Ξ × (X → (Fin 20 → UInt8))) :=
    Fintype.card_pos
  have cardNonzero :
      (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt cardPos)
  have cardFinite :
      (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) : ENNReal) ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have denNonzero : (256 : ENNReal) ^ 6 ≠ 0 := by norm_num
  have denFinite : (256 : ENNReal) ^ 6 ≠ ⊤ := by norm_num
  apply (ENNReal.div_le_iff cardNonzero cardFinite).2
  have rearrange :
      ((150 : ENNReal) * 12 / 256 ^ 6) *
          (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) : ENNReal) =
        (((150 : ENNReal) * 12) *
          (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) : ENNReal)) /
          256 ^ 6 := by
    simp [div_eq_mul_inv]
    ac_rfl
  rw [rearrange]
  exact (ENNReal.le_div_iff_mul_le (Or.inl denNonzero)
    (Or.inl denFinite)).2 ennBound

end QSB.DynamicBonusProbability
