import QSB.DynamicSetupReduction
import QSB.JointSourceChecks

/-!
A probability interface in which one sampled world supplies the same H and R
to the HORS commitments and SHA256-derived signature puzzles. The pinning and
final-round relations remain external; their source-shaped instantiation must
use the same H twice for each SHA256d call. The attacker output, disclosure
history, and accepted transaction predicate may all depend on that world. No
independence or separate query budgets are introduced by the measure argument.

The quantum algorithm, coherent query budget, actual Bitcoin Core extraction,
and a nontrivial bound on the joint event remain external obligations.
-/
namespace QSB.JointOracleReduction
open MeasureTheory
open ByteMachine

variable {Ω Index SignedTx : Type*} [DecidableEq Index]

/-- Everything that may depend on one sampled hash-oracle world and its
adaptive transcript. `functions` is one pair (H,R); source ECDSA relations
must still be tied to its H for SHA256d. -/
structure Experiment (Ω Index SignedTx : Type*) [DecidableEq Index] where
  functions : Ω → JointSourceChecks.Functions
  secrets : Ω → Index → Bytes
  accepted : Ω → SignedTx → Prop
  spendsTarget : Ω → SignedTx → Prop
  projection : SignedTx → Game.Projection
  authorized : Ω → Set Game.Projection
  extractor : Ω → Extractor Index Bytes Bytes SignedTx
  pinRelation : Ω → SignedTx → Bytes → Prop
  roundRelation : Ω → SignedTx → Finset Index → Bytes → Prop
  output : Ω → SignedTx
  released : Ω → Set SignedTx
  disclosed : Ω → Finset Index

def hashSecret (e : Experiment Ω Index SignedTx) (ω : Ω) : Bytes → Bytes :=
  fun secret => (e.functions ω).R ((e.functions ω).H secret)

def commitments (e : Experiment Ω Index SignedTx) (ω : Ω) : Index → Bytes :=
  fun i => hashSecret e ω (e.secrets ω i)

def strictDERTarget : Set Bytes :=
  {signature | DERSyntax.valid signature = true}

def unauthorized (e : Experiment Ω Index SignedTx) (ω : Ω) : Prop :=
  Game.Unauthorized (e.accepted ω) (e.spendsTarget ω) e.projection
    (e.authorized ω) (e.output ω)

/-- The one joint source failure event. Both alternatives are evaluated in
the same sampled world, with the same H and R and the same terminal history.
The relations still need a Core/sighash/ECDSA source instantiation. -/
def jointFailure (e : Experiment Ω Index SignedTx) (ω : Ω) : Prop :=
  FreshFailure (e.extractor ω) (hashSecret e ω) (commitments e ω)
      (ForbiddenMessage e.projection (e.authorized ω))
      (e.disclosed ω) (e.output ω) ∨
    TwoPuzzleFailure (e.extractor ω) (e.pinRelation ω)
      (e.roundRelation ω) (e.functions ω).H strictDERTarget
      (ForbiddenMessage e.projection (e.authorized ω))
      (e.released ω) (e.disclosed ω) (e.output ω)

def extractionGap (e : Experiment Ω Index SignedTx) (ω : Ω) : Prop :=
  ExtractionGap (e.accepted ω) (e.spendsTarget ω) e.projection
    (e.authorized ω) (e.extractor ω) (hashSecret e ω)
    (commitments e ω) (e.pinRelation ω) (e.roundRelation ω)
    (e.functions ω).H strictDERTarget (e.output ω)

/-- Pointwise reduction before any measure or oracle distribution is chosen.
Every argument, including Core acceptance, may vary with the oracle world. -/
theorem unauthorized_joint_or_gap (e : Experiment Ω Index SignedTx)
    (ω : Ω)
    (honest : AuthorizedRelease e.projection (e.authorized ω)
      (e.released ω))
    (bad : unauthorized e ω) :
    jointFailure e ω ∨ extractionGap e ω := by
  simpa only [unauthorized, jointFailure, extractionGap, or_assoc] using
    unauthorized_with_explicit_gap
      (extractor := e.extractor ω)
      (hashSecret := hashSecret e ω)
      (commitments := commitments e ω)
      (pinRelation := e.pinRelation ω)
      (roundRelation := e.roundRelation ω)
      (hashKey := (e.functions ω).H)
      (target := strictDERTarget)
      (disclosed := e.disclosed ω)
      (released := e.released ω) honest bad

/-- One joint-event probability premise, plus the still-visible extraction
gap. A future QROM theorem must bound `jointFailure` for one adversary and one
shared coherent query budget; this theorem supplies no such bound. -/
theorem unauthorized_measure_bound
    [MeasurableSpace Ω]
    (e : Experiment Ω Index SignedTx) (μ : Measure Ω)
    (honest : ∀ ω, AuthorizedRelease e.projection (e.authorized ω)
      (e.released ω))
    (εjoint εgap : ENNReal)
    (jointBound : μ {ω | jointFailure e ω} ≤ εjoint)
    (gapBound : μ {ω | extractionGap e ω} ≤ εgap) :
    μ {ω | unauthorized e ω} ≤ εjoint + εgap := by
  have cover : {ω | unauthorized e ω} ⊆
      {ω | jointFailure e ω} ∪ {ω | extractionGap e ω} := by
    intro ω bad
    exact unauthorized_joint_or_gap e ω (honest ω) bad
  exact (measure_mono cover).trans
    ((measure_union_le _ _).trans (add_le_add jointBound gapBound))

/-- If a good setup really makes arbitrary-witness Core extraction total,
only that setup exception remains alongside the single joint-oracle event.
The stated product-uniform setup marginal is still an explicit premise; the
transcript and attack output may depend on the sampled functions. -/
theorem unauthorized_measure_bound_with_uniform_setup
    [MeasurableSpace Ω]
    {Ξ X : Type*}
    [Fintype Ξ] [DecidableEq Ξ] [Fintype X] [DecidableEq X]
    [MeasurableSpace (Ξ × (X → (Fin 20 → UInt8)))]
    [MeasurableSingletonClass (Ξ × (X → (Fin 20 → UInt8)))]
    [Nonempty (Ξ × (X → (Fin 20 → UInt8)))]
    (e : Experiment Ω Index SignedTx) (μ : Measure Ω)
    (source : Fin 150 → Ξ → X)
    (setup : Ω → Ξ × (X → (Fin 20 → UInt8)))
    (setupMeasurable : Measurable setup)
    (setupUniform : Measure.map setup μ =
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Ξ × (X → (Fin 20 → UInt8)))))
    (honest : ∀ ω, AuthorizedRelease e.projection (e.authorized ω)
      (e.released ω))
    (goodExtraction : ∀ ω,
      ¬DynamicBonusSetup.BadDERSetup source (setup ω) →
      unauthorized e ω →
      ExtractionEvidence (e.extractor ω) (hashSecret e ω)
        (commitments e ω) (e.pinRelation ω) (e.roundRelation ω)
        (e.functions ω).H strictDERTarget (e.output ω))
    (εjoint : ENNReal)
    (jointBound : μ {ω | jointFailure e ω} ≤ εjoint) :
    μ {ω | unauthorized e ω} ≤
      εjoint + (150 : ENNReal) * 12 / 256 ^ 6 := by
  have setupBound := DynamicSetupReduction.uniform_setup_bad_event_bound
    source μ setup setupMeasurable setupUniform
  have cover : {ω | extractionGap e ω} ⊆
      {ω | DynamicBonusSetup.BadDERSetup source (setup ω)} := by
    intro ω gap
    by_contra good
    exact gap.2 (goodExtraction ω good gap.1)
  have gapBound : μ {ω | extractionGap e ω} ≤
      (150 : ENNReal) * 12 / 256 ^ 6 :=
    (measure_mono cover).trans setupBound
  exact unauthorized_measure_bound e μ honest εjoint _ jointBound gapBound

end QSB.JointOracleReduction
