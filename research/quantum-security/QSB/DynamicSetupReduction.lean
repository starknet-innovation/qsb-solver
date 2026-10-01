import QSB.Reduction
import QSB.DynamicBonusProbability

/-!
Conditional game composition with the checked uniform DER-setup exception.
Fresh-opening and puzzle-search bounds are explicit quantum assumptions, and
extraction on good setups is an explicit builder/Core/transaction premise.
None is inferred from a byte-model run or from the setup count.
-/
namespace QSB.DynamicSetupReduction
open MeasureTheory
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem uniform_setup_bad_event_bound
    {Ω Ξ X : Type*}
    [MeasurableSpace Ω]
    [Fintype Ξ] [DecidableEq Ξ] [Fintype X] [DecidableEq X]
    [MeasurableSpace (Ξ × (X → (Fin 20 → UInt8)))]
    [MeasurableSingletonClass (Ξ × (X → (Fin 20 → UInt8)))]
    [Nonempty (Ξ × (X → (Fin 20 → UInt8)))]
    (source : Fin 150 → Ξ → X)
    (μ : Measure Ω)
    (setup : Ω → Ξ × (X → (Fin 20 → UInt8)))
    (setupMeasurable : Measurable setup)
    (setupUniform : Measure.map setup μ =
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Ξ × (X → (Fin 20 → UInt8))))) :
    μ {ω | DynamicBonusSetup.BadDERSetup source (setup ω)} ≤
      (150 : ENNReal) * 12 / 256 ^ 6 := by
  have badMeasurable : MeasurableSet
      {p : Ξ × (X → (Fin 20 → UInt8)) |
        DynamicBonusSetup.BadDERSetup source p} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have mapped : μ {ω | DynamicBonusSetup.BadDERSetup source (setup ω)} =
      (Measure.map setup μ)
        {p | DynamicBonusSetup.BadDERSetup source p} := by
    exact (Measure.map_apply setupMeasurable badMeasurable).symm
  rw [mapped, setupUniform]
  exact DynamicBonusProbability.uniform_bad_der_probability source

/-- A conditional unauthorized-spend inequality with the checked setup term.
The good-setup extraction premise must establish actual transaction/Core
refinement and the explicit matched-scan conditions of the byte-model result.
The fresh and puzzle terms must be bounded in one joint quantum hash game with
the adversary's total shared-oracle query budget. -/
theorem unauthorized_measure_bound_with_uniform_setup
    {Ω Ξ X Index Secret Digest Key SignedTx : Type*}
    [MeasurableSpace Ω] [DecidableEq Index]
    [Fintype Ξ] [DecidableEq Ξ] [Fintype X] [DecidableEq X]
    [MeasurableSpace (Ξ × (X → (Fin 20 → UInt8)))]
    [MeasurableSingletonClass (Ξ × (X → (Fin 20 → UInt8)))]
    [Nonempty (Ξ × (X → (Fin 20 → UInt8)))]
    (source : Fin 150 → Ξ → X)
    (μ : Measure Ω)
    (setup : Ω → Ξ × (X → (Fin 20 → UInt8)))
    (setupMeasurable : Measurable setup)
    (setupUniform : Measure.map setup μ =
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Ξ × (X → (Fin 20 → UInt8)))))
    (accepted spendsTarget : SignedTx → Prop)
    (projection : SignedTx → QSB.Game.Projection)
    (authorized : Set QSB.Game.Projection)
    (extractor : QSB.Extractor Index Secret Key SignedTx)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (output : Ω → SignedTx) (released : Ω → Set SignedTx)
    (disclosed : Ω → Finset Index)
    (honest : ∀ ω, QSB.AuthorizedRelease projection authorized (released ω))
    (goodExtraction : ∀ ω,
      ¬DynamicBonusSetup.BadDERSetup source (setup ω) →
      QSB.Game.Unauthorized accepted spendsTarget projection authorized
        (output ω) →
      QSB.ExtractionEvidence extractor hashSecret commitments
        pinRelation roundRelation hashKey target (output ω))
    (εfresh εpuzzle : ENNReal)
    (freshBound : μ {ω | QSB.FreshFailure extractor hashSecret commitments
      (QSB.ForbiddenMessage projection authorized)
      (disclosed ω) (output ω)} ≤ εfresh)
    (puzzleBound : μ {ω | QSB.TwoPuzzleFailure extractor pinRelation
      roundRelation hashKey target
      (QSB.ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)} ≤ εpuzzle) :
    μ {ω | QSB.Game.Unauthorized accepted spendsTarget projection authorized
      (output ω)} ≤
      (εfresh + εpuzzle) + (150 : ENNReal) * 12 / 256 ^ 6 := by
  have setupBound := uniform_setup_bad_event_bound source μ setup
    setupMeasurable setupUniform
  have gapCover :
      {ω | QSB.ExtractionGap accepted spendsTarget projection authorized
        extractor hashSecret commitments pinRelation roundRelation hashKey
        target (output ω)} ⊆
      {ω | DynamicBonusSetup.BadDERSetup source (setup ω)} := by
    intro ω gap
    by_contra good
    exact gap.2 (goodExtraction ω good gap.1)
  have gapBound :
      μ {ω | QSB.ExtractionGap accepted spendsTarget projection authorized
        extractor hashSecret commitments pinRelation roundRelation hashKey
        target (output ω)} ≤
        (150 : ENNReal) * 12 / 256 ^ 6 :=
    (measure_mono gapCover).trans setupBound
  exact QSB.unauthorized_measure_bound_with_gap μ output released disclosed
    honest εfresh εpuzzle ((150 : ENNReal) * 12 / 256 ^ 6)
    freshBound puzzleBound gapBound

/-- The same bound splits the puzzle term by whether the extracted pinning
and final-round key bytes coincide. Neither quantum bound is asserted here;
in particular, a distinct-input search estimate cannot be applied to the
same-key branch. -/
theorem unauthorized_measure_bound_uniform_setup_key_cases
    {Ω Ξ X Index Secret Digest Key SignedTx : Type*}
    [MeasurableSpace Ω] [DecidableEq Index]
    [Fintype Ξ] [DecidableEq Ξ] [Fintype X] [DecidableEq X]
    [MeasurableSpace (Ξ × (X → (Fin 20 → UInt8)))]
    [MeasurableSingletonClass (Ξ × (X → (Fin 20 → UInt8)))]
    [Nonempty (Ξ × (X → (Fin 20 → UInt8)))]
    (source : Fin 150 → Ξ → X)
    (μ : Measure Ω)
    (setup : Ω → Ξ × (X → (Fin 20 → UInt8)))
    (setupMeasurable : Measurable setup)
    (setupUniform : Measure.map setup μ =
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Ξ × (X → (Fin 20 → UInt8)))))
    (accepted spendsTarget : SignedTx → Prop)
    (projection : SignedTx → QSB.Game.Projection)
    (authorized : Set QSB.Game.Projection)
    (extractor : QSB.Extractor Index Secret Key SignedTx)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (output : Ω → SignedTx) (released : Ω → Set SignedTx)
    (disclosed : Ω → Finset Index)
    (honest : ∀ ω, QSB.AuthorizedRelease projection authorized (released ω))
    (goodExtraction : ∀ ω,
      ¬DynamicBonusSetup.BadDERSetup source (setup ω) →
      QSB.Game.Unauthorized accepted spendsTarget projection authorized
        (output ω) →
      QSB.ExtractionEvidence extractor hashSecret commitments
        pinRelation roundRelation hashKey target (output ω))
    (εfresh εdistinct εsame : ENNReal)
    (freshBound : μ {ω | QSB.FreshFailure extractor hashSecret commitments
      (QSB.ForbiddenMessage projection authorized)
      (disclosed ω) (output ω)} ≤ εfresh)
    (distinctBound : μ {ω | QSB.DistinctKeyFailure extractor pinRelation
      roundRelation hashKey target
      (QSB.ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)} ≤ εdistinct)
    (sameBound : μ {ω | QSB.SameKeyFailure extractor pinRelation
      roundRelation hashKey target
      (QSB.ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)} ≤ εsame) :
    μ {ω | QSB.Game.Unauthorized accepted spendsTarget projection authorized
      (output ω)} ≤
      (εfresh + (εdistinct + εsame)) +
        (150 : ENNReal) * 12 / 256 ^ 6 := by
  let distinctEvent : Set Ω :=
    {ω | QSB.DistinctKeyFailure extractor pinRelation roundRelation
      hashKey target (QSB.ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)}
  let sameEvent : Set Ω :=
    {ω | QSB.SameKeyFailure extractor pinRelation roundRelation
      hashKey target (QSB.ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)}
  have cover :
      {ω | QSB.TwoPuzzleFailure extractor pinRelation roundRelation
        hashKey target (QSB.ForbiddenMessage projection authorized)
        (released ω) (disclosed ω) (output ω)} ⊆
        distinctEvent ∪ sameEvent := by
    intro ω puzzle
    simpa [distinctEvent, sameEvent] using
      (QSB.two_puzzle_failure_key_cases.mp puzzle)
  have puzzleBound :
      μ {ω | QSB.TwoPuzzleFailure extractor pinRelation roundRelation
        hashKey target (QSB.ForbiddenMessage projection authorized)
        (released ω) (disclosed ω) (output ω)} ≤
        εdistinct + εsame :=
    (measure_mono cover).trans
      ((measure_union_le distinctEvent sameEvent).trans
        (add_le_add distinctBound sameBound))
  exact unauthorized_measure_bound_with_uniform_setup source μ setup
    setupMeasurable setupUniform accepted spendsTarget projection
    authorized extractor hashSecret commitments pinRelation roundRelation
    hashKey target output released disclosed honest goodExtraction
    εfresh (εdistinct + εsame) freshBound puzzleBound

end QSB.DynamicSetupReduction
