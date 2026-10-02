import QSB.RandomOracleSetup

/-!
A finite counterexample to applying fixed-input random-function marginals to
an output that is allowed to depend on the sampled oracle function.  The
world-indexed definition charges no queries for inspecting the oracle.  If
implemented as a classical algorithm, the inspection below would cost one
query.  This identifies the missing causal/query-limited premise in a
world-indexed terminal game, including `JointOracleReduction.Experiment.output`.
-/
namespace QSB.OracleDependentSelection

def fixedInput : Bool := false

/-- A one-bit honest disclosure from the same sampled oracle. -/
def revealedBit (oracle : Bool → Bool) : Bool := oracle false

/-- Select the disclosed input on a hit and the other input on a miss. -/
def chooseFromDisclosure (bit : Bool) : Bool := if bit then false else true

/-- This world-indexed selector observes one oracle value without a query
charge.  A classical implementation would use one query or correlated advice. -/
def inspectThenChoose (oracle : Bool → Bool) : Bool :=
  chooseFromDisclosure (revealedBit oracle)

/-- The disclosed bit has the ordinary uniform marginal. -/
theorem disclosure_true_count :
    (Finset.univ.filter fun oracle : Bool → Bool =>
      revealedBit oracle = true).card = 2 := by
  decide

/-- A fixed input hits the target `true` in two of four Boolean functions. -/
theorem fixed_hit_count :
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle fixedInput = true).card = 2 := by
  decide

/-- Allowing the chosen input to depend on an oracle value raises the hit
count to three of four worlds.  The missed world maps both inputs to false. -/
theorem inspected_hit_count :
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle (inspectThenChoose oracle) = true).card = 3 := by
  decide

/-- Uniform disclosure alone does not restore independence of the selected
input from the sampled function. -/
theorem correlated_disclosure_hit_count :
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle (chooseFromDisclosure (revealedBit oracle)) = true).card = 3 := by
  decide

/-- Thus the fixed-input target-density count fails for a source selected
from the sampled function itself.  A QROM bound needs a causal algorithm and
must charge its coherent oracle queries; no quantum claim follows here. -/
theorem fixed_marginal_not_adaptive_bound :
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle fixedInput = true).card <
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle (inspectThenChoose oracle) = true).card := by
  rw [fixed_hit_count, inspected_hit_count]
  decide

/-- A toy verifier whose target set for every fixed key has one element. -/
def singletonTarget (key : Bool) : Finset Bool := {key}

theorem singleton_target_card (key : Bool) :
    (singletonTarget key).card = 1 := by
  simp [singletonTarget]

/-- With a fixed key and one fixed digest input, the target hit has the
ordinary one-half marginal over the four Boolean oracle functions. -/
theorem fixed_key_target_hit_count :
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle false ∈ singletonTarget false).card = 2 := by
  decide

/-- If disclosure reveals the digest and the key is selected to be that
digest, the singleton target contains it in all four worlds. The target
cardinality is still one for every fixed key. This world-indexed selection
does not charge the query or advice needed to learn the disclosed bit. -/
theorem disclosed_key_target_hit_count :
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle false ∈ singletonTarget (revealedBit oracle)).card = 4 := by
  decide

/-- A finite per-key target count alone cannot justify applying a
fixed-key target-density bound after oracle-dependent key selection. This is
a toy reduction counterexample, not a QSB spend or a causal QROM lower bound. -/
theorem singleton_target_count_not_adaptive_bound :
    (∀ key : Bool, (singletonTarget key).card = 1) ∧
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle false ∈ singletonTarget false).card <
    (Finset.univ.filter fun oracle : Bool → Bool =>
      oracle false ∈ singletonTarget (revealedBit oracle)).card := by
  constructor
  · exact singleton_target_card
  · rw [fixed_key_target_hit_count, disclosed_key_target_hit_count]
    decide

end QSB.OracleDependentSelection
