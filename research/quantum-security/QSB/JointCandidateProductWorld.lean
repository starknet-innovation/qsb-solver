import QSB.JointCandidateMachine

/-!
Product-world specialization of the conditional classical candidate machine.
The oracle pair is the second world coordinate, while the machine's initial
state is constructed only from the coins coordinate. Thus varying the oracle
at fixed coins cannot directly change that initial state.

`JointCandidateMachine.Realizes` remains a substantive obligation: the one
bounded run must implement the source extractor and its candidate enumeration.
The type of `coins` alone does not prove that a probability distribution
samples it independently of the oracle, nor does this module provide a
coherent quantum machine or a QROM success bound.
-/
namespace QSB.JointCandidateProductWorld
open ByteMachine
open CausalQueryAlgorithm (Query answer Machine run)
open JointCandidateMachine
open JointPostprocessingCausality
open JointFreshPostprocessing

variable {Coins Index SignedTx State : Type*} [LinearOrder Index]

abbrev World (Coins : Type*) := Coins × JointSourceChecks.Functions

/-- Non-oracle initial state, obtained from the coins coordinate only. -/
def initialState (seed : Coins → State) (world : World Coins) : State :=
  seed world.1

theorem initialState_congr (seed : Coins → State)
    {world world' : World Coins} (sameCoins : world'.1 = world.1) :
    initialState seed world' = initialState seed world :=
  congrArg seed sameCoins

/-- At equal coins, agreement on the first bounded run's recorded oracle
replies preserves both the source candidate list and the entire run. The
`realizes` premise still has to be proved from an actual extractor machine. -/
theorem openingPairs_congr_of_product_run
    (e : JointOracleReduction.Experiment (World Coins) Index SignedTx)
    (functionsWorld : ∀ world : World Coins, e.functions world = world.2)
    (m : Machine State (Output Index SignedTx))
    (seed : Coins → State) (budget : Nat)
    (realizes : Realizes e m (initialState seed) budget)
    (world world' : World Coins)
    (sameCoins : world'.1 = world.1)
    (agree : ∀ entry ∈ (run m world.2 budget (seed world.1)).2,
      answer world'.2 entry.1 = answer world.2 entry.1) :
    JointFreshCandidates.openingPairs e world' =
        JointFreshCandidates.openingPairs e world ∧
      run m world'.2 budget (seed world'.1) =
        run m world.2 budget (seed world.1) := by
  have agreeWorld : ∀ entry ∈
      (run m (e.functions world) budget (initialState seed world)).2,
      answer (e.functions world') entry.1 =
        answer (e.functions world) entry.1 := by
    simpa [functionsWorld, initialState] using agree
  have result := openingPairs_congr_of_joint_run e m (initialState seed)
    budget realizes world world' (initialState_congr seed sameCoins) agreeWorld
  simpa [functionsWorld, initialState] using result

/-- Conditional H-route causality in a product world. The combined trace
contains the machine run's recorded queries and two H inputs per pair. -/
theorem hPostTranscript_congr_of_product_run
    (e : JointOracleReduction.Experiment (World Coins) Index SignedTx)
    (functionsWorld : ∀ world : World Coins, e.functions world = world.2)
    (m : Machine State (Output Index SignedTx))
    (seed : Coins → State) (budget : Nat)
    (realizes : Realizes e m (initialState seed) budget)
    (world world' : World Coins)
    (sameCoins : world'.1 = world.1)
    (agreeRun : ∀ entry ∈ (run m world.2 budget (seed world.1)).2,
      answer world'.2 entry.1 = answer world.2 entry.1)
    (agreePost : ∀ q ∈ fixedHTaggedTrace world.2
        (JointFreshCandidates.openingPairs e world),
      answer world'.2 q = answer world.2 q) :
    hPostTranscript e world' = hPostTranscript e world ∧
      hCombinedTrace e m (initialState seed) budget world' =
        hCombinedTrace e m (initialState seed) budget world := by
  have agreeRunWorld : ∀ entry ∈
      (run m (e.functions world) budget (initialState seed world)).2,
      answer (e.functions world') entry.1 =
        answer (e.functions world) entry.1 := by
    simpa [functionsWorld, initialState] using agreeRun
  have agreePostWorld : ∀ q ∈ fixedHTaggedTrace (e.functions world)
      (JointFreshCandidates.openingPairs e world),
      answer (e.functions world') q = answer (e.functions world) q := by
    simpa [functionsWorld] using agreePost
  exact hPostTranscript_congr_of_joint_run e m (initialState seed) budget
    realizes world world' (initialState_congr seed sameCoins)
    agreeRunWorld agreePostWorld

/-- Conditional R-route causality in a product world. The combined trace
contains the machine run's recorded queries, both H inputs, and the adaptive
R inputs for every pair. -/
theorem rPostTranscript_congr_of_product_run
    (e : JointOracleReduction.Experiment (World Coins) Index SignedTx)
    (functionsWorld : ∀ world : World Coins, e.functions world = world.2)
    (m : Machine State (Output Index SignedTx))
    (seed : Coins → State) (budget : Nat)
    (realizes : Realizes e m (initialState seed) budget)
    (world world' : World Coins)
    (sameCoins : world'.1 = world.1)
    (agreeRun : ∀ entry ∈ (run m world.2 budget (seed world.1)).2,
      answer world'.2 entry.1 = answer world.2 entry.1)
    (agreePost : ∀ q ∈ fixedRTaggedTrace world.2
        (JointFreshCandidates.openingPairs e world),
      answer world'.2 q = answer world.2 q) :
    rPostTranscript e world' = rPostTranscript e world ∧
      rCombinedTrace e m (initialState seed) budget world' =
        rCombinedTrace e m (initialState seed) budget world := by
  have agreeRunWorld : ∀ entry ∈
      (run m (e.functions world) budget (initialState seed world)).2,
      answer (e.functions world') entry.1 =
        answer (e.functions world) entry.1 := by
    simpa [functionsWorld, initialState] using agreeRun
  have agreePostWorld : ∀ q ∈ fixedRTaggedTrace (e.functions world)
      (JointFreshCandidates.openingPairs e world),
      answer (e.functions world') q = answer (e.functions world) q := by
    simpa [functionsWorld] using agreePost
  exact rPostTranscript_congr_of_joint_run e m (initialState seed) budget
    realizes world world' (initialState_congr seed sameCoins)
    agreeRunWorld agreePostWorld

end QSB.JointCandidateProductWorld
