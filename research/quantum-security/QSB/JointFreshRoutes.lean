import QSB.JointOracleReduction

/-!
A fresh final-round opening names an actual extracted witness and one setup
secret. Its equality with that commitment has three exhaustive routes:
the exact secret was recovered, H has a collision on those two distinct byte
strings, or R has a collision on their distinct H outputs. These are reached
pairs, not unrestricted existential collisions of a whole random function.
The theorem supplies no query-success probability for any route.
-/
namespace QSB.JointFreshRoutes
open ByteMachine
open MeasureTheory

variable {Ω Index SignedTx : Type*} [DecidableEq Index]

/-- The candidate is the byte string extracted from the adversary's submitted
transaction at an undisclosed signed position. The matched commitment and the
setup secret are taken from the same sampled world. -/
def reachedOpening (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) (i : Index) (candidate : Bytes) : Prop :=
  ForbiddenMessage (e.projection ω) (e.authorized ω) (e.output ω) ∧
    ∃ pinKey w, ∃ membership : i ∈ w.signed,
      e.extractor ω (e.output ω) = some (pinKey, w) ∧
      i ∉ e.disclosed ω ∧
      candidate = w.opening i membership ∧
      (e.functions ω).R ((e.functions ω).H candidate) =
        (e.functions ω).R ((e.functions ω).H (e.secrets ω i))

def exactSecret (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) : Prop :=
  ∃ i candidate, reachedOpening e ω i candidate ∧
    candidate = e.secrets ω i

def reachedHCollision (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) : Prop :=
  ∃ i candidate, reachedOpening e ω i candidate ∧
    candidate ≠ e.secrets ω i ∧
    (e.functions ω).H candidate = (e.functions ω).H (e.secrets ω i)

def reachedRCollision (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) : Prop :=
  ∃ i candidate, reachedOpening e ω i candidate ∧
    (e.functions ω).H candidate ≠ (e.functions ω).H (e.secrets ω i)

def puzzleFailure (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) : Prop :=
  TwoPuzzleFailure (e.extractor ω) (e.pinRelation ω)
    (e.roundRelation ω) (e.functions ω).H
    JointOracleReduction.strictDERTarget
    (ForbiddenMessage (e.projection ω) (e.authorized ω))
    (e.released ω) (e.disclosed ω) (e.output ω)

/-- Every source-extracted fresh opening has one of the three named routes.
This argument is independent of how the honest setup and attack transcript
were generated, but a quantum bound must account for that causal history. -/
theorem fresh_failure_routes
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (fresh : FreshFailure (e.extractor ω)
      (JointOracleReduction.hashSecret e ω)
      (JointOracleReduction.commitments e ω)
      (ForbiddenMessage (e.projection ω) (e.authorized ω))
      (e.disclosed ω) (e.output ω)) :
    exactSecret e ω ∨ reachedHCollision e ω ∨ reachedRCollision e ω := by
  obtain ⟨forbidden, pinKey, w, extracted, i, membership, undisclosed,
    matched⟩ := fresh
  let candidate := w.opening i membership
  have reached : reachedOpening e ω i candidate := by
    refine ⟨forbidden, pinKey, w, membership, extracted,
      undisclosed, rfl, ?_⟩
    simpa [JointOracleReduction.hashSecret,
      JointOracleReduction.commitments] using matched
  by_cases same : candidate = e.secrets ω i
  · exact Or.inl ⟨i, candidate, reached, same⟩
  · by_cases sameH : (e.functions ω).H candidate =
        (e.functions ω).H (e.secrets ω i)
    · exact Or.inr (Or.inl ⟨i, candidate, reached, same, sameH⟩)
    · exact Or.inr (Or.inr ⟨i, candidate, reached, sameH⟩)

theorem joint_failure_routes
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (bad : JointOracleReduction.jointFailure e ω) :
    exactSecret e ω ∨ reachedHCollision e ω ∨
      reachedRCollision e ω ∨ puzzleFailure e ω := by
  rcases bad with fresh | puzzle
  · rcases fresh_failure_routes e ω fresh with exact | hCollision | rCollision
    · exact Or.inl exact
    · exact Or.inr (Or.inl hCollision)
    · exact Or.inr (Or.inr (Or.inl rCollision))
  · exact Or.inr (Or.inr (Or.inr puzzle))

/-- The existing unauthorized-spend reduction can be refined into reached
opening routes, the unsplit two-puzzle event, or the explicit extraction gap.
No term is assigned a probability here. -/
theorem unauthorized_routes_or_gap
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (honest : AuthorizedRelease (e.projection ω) (e.authorized ω)
      (e.released ω))
    (bad : JointOracleReduction.unauthorized e ω) :
    exactSecret e ω ∨ reachedHCollision e ω ∨
      reachedRCollision e ω ∨ puzzleFailure e ω ∨
      JointOracleReduction.extractionGap e ω := by
  rcases JointOracleReduction.unauthorized_joint_or_gap e ω honest bad with
    joint | gap
  · rcases joint_failure_routes e ω joint with exact | hCollision |
      rCollision | puzzle
    · exact Or.inl exact
    · exact Or.inr (Or.inl hCollision)
    · exact Or.inr (Or.inr (Or.inl rCollision))
    · exact Or.inr (Or.inr (Or.inr (Or.inl puzzle)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr gap)))

/-- An additive interface for route-specific bounds. Every supplied bound
must be for the same world distribution and must charge the same adversary's
global H/R query budget; this statement proves no such route bound. -/
theorem unauthorized_measure_bound_routes
    [MeasurableSpace Ω]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (μ : Measure Ω)
    (honest : ∀ ω, AuthorizedRelease (e.projection ω) (e.authorized ω)
      (e.released ω))
    (εexact εH εR εpuzzle εgap : ENNReal)
    (exactBound : μ {ω | exactSecret e ω} ≤ εexact)
    (HBound : μ {ω | reachedHCollision e ω} ≤ εH)
    (RBound : μ {ω | reachedRCollision e ω} ≤ εR)
    (puzzleBound : μ {ω | puzzleFailure e ω} ≤ εpuzzle)
    (gapBound : μ {ω | JointOracleReduction.extractionGap e ω} ≤ εgap) :
    μ {ω | JointOracleReduction.unauthorized e ω} ≤
      (εexact + (εH + (εR + εpuzzle))) + εgap := by
  let A : Set Ω := {ω | exactSecret e ω}
  let B : Set Ω := {ω | reachedHCollision e ω}
  let C : Set Ω := {ω | reachedRCollision e ω}
  let D : Set Ω := {ω | puzzleFailure e ω}
  let E : Set Ω := {ω | JointOracleReduction.extractionGap e ω}
  have cover : {ω | JointOracleReduction.unauthorized e ω} ⊆
      (A ∪ (B ∪ (C ∪ D))) ∪ E := by
    intro ω bad
    simpa [A, B, C, D, E, or_assoc] using
      unauthorized_routes_or_gap e ω (honest ω) bad
  have innerBound : μ (C ∪ D) ≤ εR + εpuzzle :=
    (measure_union_le C D).trans (add_le_add RBound puzzleBound)
  have middleBound : μ (B ∪ (C ∪ D)) ≤
      εH + (εR + εpuzzle) :=
    (measure_union_le B (C ∪ D)).trans
      (add_le_add HBound innerBound)
  exact QSB.event_bound_with_gap μ
    {ω | JointOracleReduction.unauthorized e ω}
    A (B ∪ (C ∪ D)) E cover
    εexact (εH + (εR + εpuzzle)) εgap
    exactBound middleBound gapBound

end QSB.JointFreshRoutes
