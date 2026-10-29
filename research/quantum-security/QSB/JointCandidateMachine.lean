import QSB.JointPostprocessingCausality

/-!
A conditional classical interface for producing the attack transcript and the
extracted opening pairs in one bounded run. `Realizes` is a substantive source
obligation: the machine's output must equal the candidates of the world-indexed
extractor. The machine's own queries are charged to the run budget; showing
that this accounts for the extractor's oracle work is still required.

The initial state may contain non-oracle randomness and setup secrets. A QROM
argument must also justify that it contains no oracle advice; equality of
initial states in the theorem is only a pointwise coupling premise. This
module supplies neither a source extractor implementation nor a quantum
collision bound.
-/
namespace QSB.JointCandidateMachine
open ByteMachine
open CausalQueryAlgorithm (Query answer Machine Transcript run)
open JointPostprocessingCausality
open JointFreshPostprocessing

variable {Ω Index SignedTx State : Type*} [LinearOrder Index]

/-- The attack transcript and the raw opening pairs are one machine output. -/
abbrev Output (Index SignedTx : Type*) :=
  Transcript Index SignedTx × List (Bytes × Bytes)

/-- A fixed machine's completed run must agree with every source-game field
used by the candidate route. Constructing this witness is the unproved
extractor/source-refinement step, not a consequence of oracle agreement. -/
def Realizes (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) : Prop :=
  ∀ ω, ∃ t : Transcript Index SignedTx,
    (run m (e.functions ω) budget (initial ω)).1 =
        some (t, JointFreshCandidates.openingPairs e ω) ∧
      t.output = e.output ω ∧
      t.disclosed = e.disclosed ω ∧
      (∀ tx, tx ∈ t.released ↔ tx ∈ e.released ω)

/-- The machine's recorded run has at most `budget` queries. Identifying these
with all calls used to compute the transcript and candidate list additionally
requires implementing `Realizes` without oracle advice in the initial state. -/
theorem candidate_run_length_le
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) :
    (run m (e.functions ω) budget (initial ω)).2.length ≤ budget :=
  CausalQueryAlgorithm.run_length_le m (e.functions ω) budget (initial ω)

/-- Agreement on the first run's recorded replies, with the same initial
state, fixes the entire run and its extracted raw candidate list. -/
theorem openingPairs_congr_of_joint_run
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat)
    (realizes : Realizes e m initial budget)
    (ω ω' : Ω) (sameInitial : initial ω' = initial ω)
    (agree : ∀ entry ∈
      (run m (e.functions ω) budget (initial ω)).2,
      answer (e.functions ω') entry.1 =
        answer (e.functions ω) entry.1) :
    JointFreshCandidates.openingPairs e ω' =
        JointFreshCandidates.openingPairs e ω ∧
      run m (e.functions ω') budget (initial ω') =
        run m (e.functions ω) budget (initial ω) := by
  have sameRun : run m (e.functions ω') budget (initial ω') =
      run m (e.functions ω) budget (initial ω) := by
    rw [sameInitial]
    exact CausalQueryAlgorithm.run_congr m (e.functions ω)
      (e.functions ω') budget (initial ω) agree
  obtain ⟨t, oldRun, _, _, _⟩ := realizes ω
  obtain ⟨t', newRun, _, _, _⟩ := realizes ω'
  have sameOutput :
      some (t', JointFreshCandidates.openingPairs e ω') =
        some (t, JointFreshCandidates.openingPairs e ω) := by
    calc
      _ = (run m (e.functions ω') budget (initial ω')).1 := newRun.symm
      _ = (run m (e.functions ω) budget (initial ω)).1 :=
        congrArg Prod.fst sameRun
      _ = _ := oldRun
  have samePairs : JointFreshCandidates.openingPairs e ω' =
      JointFreshCandidates.openingPairs e ω := by
    have mapped := congrArg (fun out : Option (Output Index SignedTx) =>
      out.map Prod.snd) sameOutput
    simpa using mapped
  exact ⟨samePairs, sameRun⟩

/-- The machine's recorded queries followed by the H-route queries on the
extracted raw pairs. -/
def hCombinedTrace
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) : List Query :=
  ((run m (e.functions ω) budget (initial ω)).2.map Prod.fst) ++
    fixedHTaggedTrace (e.functions ω)
      (JointFreshCandidates.openingPairs e ω)

/-- The H postprocessor adds two calls per extracted candidate pair. -/
theorem hCombinedTrace_length_le
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) :
    (hCombinedTrace e m initial budget ω).length ≤
      budget + 2 * (JointFreshCandidates.openingPairs e ω).length := by
  simp only [hCombinedTrace, List.length_append, List.length_map,
    fixedHTaggedTrace_length]
  exact Nat.add_le_add_right
    (candidate_run_length_le e m initial budget ω) _

theorem hCombinedTrace_length_le_card [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) :
    (hCombinedTrace e m initial budget ω).length ≤
      budget + 2 * Fintype.card Index := by
  calc
    _ ≤ budget + 2 * (JointFreshCandidates.openingPairs e ω).length :=
      hCombinedTrace_length_le e m initial budget ω
    _ ≤ budget + 2 * Fintype.card Index :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left 2
          (JointFreshCandidates.openingPairs_length_le e ω)) budget

theorem hCombinedTrace_length_le_300
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx)
    (m : Machine State (Output (Fin 150) SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) :
    (hCombinedTrace e m initial budget ω).length ≤ budget + 300 := by
  simpa using hCombinedTrace_length_le_card e m initial budget ω

/-- One realized joint run followed by H postprocessing is causal under
agreement on both of its recorded query segments. -/
theorem hPostTranscript_congr_of_joint_run
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat)
    (realizes : Realizes e m initial budget)
    (ω ω' : Ω) (sameInitial : initial ω' = initial ω)
    (agreeRun : ∀ entry ∈
      (run m (e.functions ω) budget (initial ω)).2,
      answer (e.functions ω') entry.1 =
        answer (e.functions ω) entry.1)
    (agreePost : ∀ q ∈ fixedHTaggedTrace (e.functions ω)
        (JointFreshCandidates.openingPairs e ω),
      answer (e.functions ω') q = answer (e.functions ω) q) :
    hPostTranscript e ω' = hPostTranscript e ω ∧
      hCombinedTrace e m initial budget ω' =
        hCombinedTrace e m initial budget ω := by
  obtain ⟨samePairs, sameRun⟩ :=
    openingPairs_congr_of_joint_run e m initial budget realizes
      ω ω' sameInitial agreeRun
  have samePost :=
    hPostTranscript_congr_of_candidates_eq e ω ω' samePairs agreePost
  have sameTagged :
      fixedHTaggedTrace (e.functions ω')
          (JointFreshCandidates.openingPairs e ω') =
        fixedHTaggedTrace (e.functions ω)
          (JointFreshCandidates.openingPairs e ω) := by
    rw [samePairs]
    simp [fixedHTaggedTrace, fixedHStage, queryPairs_trace]
  refine ⟨samePost, ?_⟩
  simp [hCombinedTrace, sameRun, sameTagged]

/-- The machine's recorded queries followed by the tagged H/R postprocessing
queries. The second segment is adaptive in the H replies. -/
def rCombinedTrace
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) : List Query :=
  ((run m (e.functions ω) budget (initial ω)).2.map Prod.fst) ++
    fixedRTaggedTrace (e.functions ω)
      (JointFreshCandidates.openingPairs e ω)

/-- The first segment charges the machine, including extraction; the second
charges two H and two R calls for each extracted candidate pair. -/
theorem rCombinedTrace_length_le
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) :
    (rCombinedTrace e m initial budget ω).length ≤
      budget + 4 * (JointFreshCandidates.openingPairs e ω).length := by
  simp only [rCombinedTrace, List.length_append, List.length_map,
    fixedRTaggedTrace_length]
  exact Nat.add_le_add_right
    (candidate_run_length_le e m initial budget ω) _

theorem rCombinedTrace_length_le_card [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) :
    (rCombinedTrace e m initial budget ω).length ≤
      budget + 4 * Fintype.card Index := by
  calc
    _ ≤ budget + 4 * (JointFreshCandidates.openingPairs e ω).length :=
      rCombinedTrace_length_le e m initial budget ω
    _ ≤ budget + 4 * Fintype.card Index :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left 4
          (JointFreshCandidates.openingPairs_length_le e ω)) budget

theorem rCombinedTrace_length_le_600
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx)
    (m : Machine State (Output (Fin 150) SignedTx))
    (initial : Ω → State) (budget : Nat) (ω : Ω) :
    (rCombinedTrace e m initial budget ω).length ≤ budget + 600 := by
  simpa using rCombinedTrace_length_le_card e m initial budget ω

/-- The combined run and R postprocessor are causal under agreement on the
two actual recorded query segments. In particular, candidate equality is
derived from the realized machine run rather than postulated. -/
theorem rPostTranscript_congr_of_joint_run
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (m : Machine State (Output Index SignedTx))
    (initial : Ω → State) (budget : Nat)
    (realizes : Realizes e m initial budget)
    (ω ω' : Ω) (sameInitial : initial ω' = initial ω)
    (agreeRun : ∀ entry ∈
      (run m (e.functions ω) budget (initial ω)).2,
      answer (e.functions ω') entry.1 =
        answer (e.functions ω) entry.1)
    (agreePost : ∀ q ∈ fixedRTaggedTrace (e.functions ω)
        (JointFreshCandidates.openingPairs e ω),
      answer (e.functions ω') q = answer (e.functions ω) q) :
    rPostTranscript e ω' = rPostTranscript e ω ∧
      rCombinedTrace e m initial budget ω' =
        rCombinedTrace e m initial budget ω := by
  obtain ⟨samePairs, sameRun⟩ :=
    openingPairs_congr_of_joint_run e m initial budget realizes
      ω ω' sameInitial agreeRun
  obtain ⟨samePost, sameTagged⟩ :=
    rPostTranscript_congr_of_candidates_eq e ω ω' samePairs agreePost
  refine ⟨samePost, ?_⟩
  simp [rCombinedTrace, sameRun, sameTagged]

end QSB.JointCandidateMachine
