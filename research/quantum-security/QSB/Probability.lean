import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import QSB.Extraction

/-!
Exact union bound on any terminal distribution, including distributions with
irrational probabilities. No finite/rational restriction and no independence
assumption. This module DOES NOT supply quantum query bounds or prove a Script
extraction theorem. Its premises expose those remaining obligations.
-/
namespace QSB
open MeasureTheory

theorem event_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad fresh puzzle : Set Ω)
    (extract : bad ⊆ fresh ∪ puzzle)
    (εfresh εpuzzle : ENNReal)
    (freshBound : μ fresh ≤ εfresh)
    (puzzleBound : μ puzzle ≤ εpuzzle) :
    μ bad ≤ εfresh + εpuzzle := by
  exact (measure_mono extract).trans
    ((measure_union_le fresh puzzle).trans (add_le_add freshBound puzzleBound))

/-- A third explicitly separated implementation/model mismatch event. -/
theorem event_bound_with_gap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad fresh puzzle gap : Set Ω)
    (extract : bad ⊆ (fresh ∪ puzzle) ∪ gap)
    (εfresh εpuzzle εgap : ENNReal)
    (freshBound : μ fresh ≤ εfresh) (puzzleBound : μ puzzle ≤ εpuzzle)
    (gapBound : μ gap ≤ εgap) :
    μ bad ≤ (εfresh + εpuzzle) + εgap := by
  apply event_bound μ bad (fresh ∪ puzzle) gap extract
  · exact (measure_union_le fresh puzzle).trans (add_le_add freshBound puzzleBound)
  · exact gapBound

/-- Separates the distinct-input target from the same-input target. A
two-distinct-input QROM theorem can only be used for `distinct`; the `same`
event needs its own quantitative argument. -/
theorem event_bound_with_key_cases {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad fresh distinct same gap : Set Ω)
    (cover : bad ⊆ (fresh ∪ (distinct ∪ same)) ∪ gap)
    (εfresh εdistinct εsame εgap : ENNReal)
    (freshBound : μ fresh ≤ εfresh)
    (distinctBound : μ distinct ≤ εdistinct)
    (sameBound : μ same ≤ εsame)
    (gapBound : μ gap ≤ εgap) :
    μ bad ≤ (εfresh + (εdistinct + εsame)) + εgap := by
  apply event_bound_with_gap μ bad fresh (distinct ∪ same) gap cover
    εfresh (εdistinct + εsame) εgap freshBound
  · exact (measure_union_le distinct same).trans
      (add_le_add distinctBound sameBound)
  · exact gapBound

/-- Finite multi-vault accounting with no independence premise. Each per-vault
bound must already charge the adversary's *global* shared-oracle query budget;
splitting that budget for free would invalidate the inputs to this theorem. -/
theorem finite_target_union_bound {Ω Vault : Type*}
    [MeasurableSpace Ω] [DecidableEq Vault]
    (μ : Measure Ω) (vaults : Finset Vault) (bad : Set Ω)
    (failure : Vault → Set Ω) (ε : Vault → ENNReal)
    (cover : bad ⊆ ⋃ v ∈ vaults, failure v)
    (perVault : ∀ v ∈ vaults, μ (failure v) ≤ ε v) :
    μ bad ≤ ∑ v ∈ vaults, ε v := by
  exact (measure_mono cover).trans
    ((measure_biUnion_finset_le vaults failure).trans
      (Finset.sum_le_sum fun v hv => perVault v hv))

/-- A concrete setup-syntax union bound for 300 HORS commitments. `der20`
must mean the actual parser property on the real commitment bytes; the
marginal premise is NOT supplied by this theorem. No independence is needed.
This event alone does not characterize the source-extraction gap. -/
theorem der20_setup_union_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (der20 : Ω → Fin 300 → Prop)
    (marginal : ∀ i : Fin 300,
      μ {ω | der20 ω i} ≤ (390405 : ENNReal) / 2 ^ 65) :
    μ {ω | ∃ i : Fin 300, der20 ω i} ≤
      (300 : ENNReal) * ((390405 : ENNReal) / 2 ^ 65) := by
  have cover : {ω | ∃ i : Fin 300, der20 ω i} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin 300)), {ω | der20 ω i} := by
    intro ω h
    obtain ⟨i, hi⟩ := h
    simpa using (show ∃ j : Fin 300, der20 ω j from ⟨i, hi⟩)
  have h := finite_target_union_bound μ (Finset.univ : Finset (Fin 300))
    {ω | ∃ i : Fin 300, der20 ω i}
    (fun i => {ω | der20 ω i})
    (fun _ => (390405 : ENNReal) / 2 ^ 65) cover
    (by intro i _; exact marginal i)
  simpa [Finset.sum_const, Finset.card_univ] using h

end QSB
