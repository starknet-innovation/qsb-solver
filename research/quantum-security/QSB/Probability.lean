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

end QSB
