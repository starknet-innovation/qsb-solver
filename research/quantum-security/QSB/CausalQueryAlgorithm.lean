import QSB.JointFreshPostprocessing

/-!
A classical adaptive oracle machine with an explicit query budget. Setup,
honest releases, disclosure choices, and the attacker's output are produced
by one such machine from one sampled H/R world and one initial state holding
all other randomness. The run records every query and its actual response,
makes at most `budget` queries, and is causal: changing the oracle anywhere
outside the recorded queries changes nothing in the transcript.

This is the classical special case of the causal algorithm the compressed-
oracle framework requires. Coherent quantum queries, the cost of the
world-indexed source extractor, and any success-probability bound remain
external.
-/
namespace QSB.CausalQueryAlgorithm
open ByteMachine

/-- One classical query to the idealized hash pair. -/
inductive Query where
  | H : Bytes → Query
  | R : Bytes → Query
  deriving DecidableEq, Repr

def Query.input : Query → Bytes
  | .H x => x
  | .R x => x

def answer (functions : JointSourceChecks.Functions) : Query → Bytes
  | .H x => functions.H x
  | .R x => functions.R x

/-- A deterministic machine: from a state it halts with an output or asks one
query; `resume` consumes the response. Randomness lives in the initial
state. -/
structure Machine (State Out : Type*) where
  step : State → Out ⊕ Query
  resume : State → Bytes → State

variable {State Out : Type*}

/-- Run with at most `budget` queries. The recorded trace lists every query
with the response that the continuation actually received, in order. A
machine still asking when the budget is exhausted returns `none`. -/
def run (m : Machine State Out) (functions : JointSourceChecks.Functions) :
    Nat → State → Option Out × List (Query × Bytes)
  | 0, s =>
      (match m.step s with
        | .inl out => some out
        | .inr _ => none, [])
  | budget + 1, s =>
      match m.step s with
      | .inl out => (some out, [])
      | .inr query =>
          let response := answer functions query
          let rest := run m functions budget (m.resume s response)
          (rest.1, (query, response) :: rest.2)

theorem run_length_le (m : Machine State Out)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (s : State),
      (run m functions budget s).2.length ≤ budget
  | 0, s => by simp [run]
  | budget + 1, s => by
      cases hstep : m.step s with
      | inl out => simp [run, hstep]
      | inr query =>
          simp only [run, hstep, List.length_cons]
          exact Nat.succ_le_succ
            (run_length_le m functions budget
              (m.resume s (answer functions query)))

/-- Every recorded response is the actual oracle value at that query. -/
theorem run_sound (m : Machine State Out)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (s : State),
      ∀ entry ∈ (run m functions budget s).2,
        entry.2 = answer functions entry.1
  | 0, s => by simp [run]
  | budget + 1, s => by
      intro entry mem
      cases hstep : m.step s with
      | inl out => simp [run, hstep] at mem
      | inr query =>
          simp only [run, hstep, List.mem_cons] at mem
          rcases mem with rfl | mem
          · rfl
          · exact run_sound m functions budget _ entry mem

/-- Causality: two oracle worlds that agree on the recorded queries of one
run give the same output and the same trace. The run never consults the
oracle anywhere else. -/
theorem run_congr (m : Machine State Out)
    (functions functions' : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (s : State),
      (∀ entry ∈ (run m functions budget s).2,
        answer functions' entry.1 = answer functions entry.1) →
      run m functions' budget s = run m functions budget s
  | 0, s => by
      intro _
      rfl
  | budget + 1, s => by
      intro agree
      cases hstep : m.step s with
      | inl out => simp [run, hstep]
      | inr query =>
          have head : answer functions' query = answer functions query :=
            agree (query, answer functions query) (by simp [run, hstep])
          have tail := run_congr m functions functions' budget
            (m.resume s (answer functions query))
            (fun entry mem => agree entry (by simp [run, hstep, mem]))
          simp only [run, hstep, head, tail]

/-- A halted run's output is recorded; exhausting the budget gives `none`. -/
theorem run_halts_of_step (m : Machine State Out)
    (functions : JointSourceChecks.Functions) (budget : Nat) (s : State)
    (out : Out) (halt : m.step s = .inl out) :
    run m functions budget s = (some out, []) := by
  cases budget <;> simp [run, halt]

/-- The joint causal transcript: the attacker's submitted transaction, the
honest disclosure history, and the honest released transactions. -/
structure Transcript (Index SignedTx : Type*) where
  output : SignedTx
  disclosed : Finset Index
  released : List SignedTx

variable {Ω Index SignedTx : Type*} [DecidableEq Index]

/-- Every world-dependent selector of the joint-oracle experiment is now the
result of one bounded classical run. The source-shaped relations, ledger
acceptance, and the extractor remain world-indexed parameters. -/
structure Causal (Ω Index SignedTx State : Type*) [DecidableEq Index] where
  functions : Ω → JointSourceChecks.Functions
  coins : Ω → State
  machine : Machine State (Transcript Index SignedTx)
  budget : Nat
  fallback : SignedTx
  secrets : Ω → Index → Bytes
  accepted : Ω → SignedTx → Prop
  spendsTarget : Ω → SignedTx → Prop
  projection : Ω → SignedTx → Game.Projection
  authorized : Ω → Set Game.Projection
  extractor : Ω → Extractor Index Bytes Bytes SignedTx
  pinRelation : Ω → SignedTx → Bytes → Prop
  roundRelation : Ω → SignedTx → Finset Index → Bytes → Prop

def transcript (c : Causal Ω Index SignedTx State) (ω : Ω) :
    Option (Transcript Index SignedTx) × List (Query × Bytes) :=
  run c.machine (c.functions ω) c.budget (c.coins ω)

def experiment (c : Causal Ω Index SignedTx State) :
    JointOracleReduction.Experiment Ω Index SignedTx where
  functions := c.functions
  secrets := c.secrets
  accepted := c.accepted
  spendsTarget := c.spendsTarget
  projection := c.projection
  authorized := c.authorized
  extractor := c.extractor
  pinRelation := c.pinRelation
  roundRelation := c.roundRelation
  output := fun ω =>
    ((transcript c ω).1.map Transcript.output).getD c.fallback
  released := fun ω =>
    match (transcript c ω).1 with
    | some t => {tx | tx ∈ t.released}
    | none => ∅
  disclosed := fun ω =>
    ((transcript c ω).1.map Transcript.disclosed).getD ∅

theorem transcript_length_le (c : Causal Ω Index SignedTx State) (ω : Ω) :
    (transcript c ω).2.length ≤ c.budget :=
  run_length_le c.machine (c.functions ω) c.budget (c.coins ω)

theorem transcript_sound (c : Causal Ω Index SignedTx State) (ω : Ω) :
    ∀ entry ∈ (transcript c ω).2,
      entry.2 = answer (c.functions ω) entry.1 :=
  run_sound c.machine (c.functions ω) c.budget (c.coins ω)

/-- The output, disclosed set, and released list are determined by the
oracle's values at the at most `budget` recorded queries. -/
theorem transcript_causal (c : Causal Ω Index SignedTx State) (ω : Ω)
    (functions' : JointSourceChecks.Functions)
    (agree : ∀ entry ∈ (transcript c ω).2,
      answer functions' entry.1 = answer (c.functions ω) entry.1) :
    run c.machine functions' c.budget (c.coins ω) = transcript c ω :=
  run_congr c.machine (c.functions ω) functions' c.budget (c.coins ω) agree

theorem output_of_halted (c : Causal Ω Index SignedTx State) (ω : Ω)
    (t : Transcript Index SignedTx) (halted : (transcript c ω).1 = some t) :
    (experiment c).output ω = t.output := by
  simp [experiment, halted]

theorem disclosed_of_halted (c : Causal Ω Index SignedTx State) (ω : Ω)
    (t : Transcript Index SignedTx) (halted : (transcript c ω).1 = some t) :
    (experiment c).disclosed ω = t.disclosed := by
  simp [experiment, halted]

theorem released_of_halted (c : Causal Ω Index SignedTx State) (ω : Ω)
    (t : Transcript Index SignedTx) (halted : (transcript c ω).1 = some t) :
    (experiment c).released ω = {tx | tx ∈ t.released} := by
  simp [experiment, halted]

/-- With the postprocessor appended, the classical H-collision route needs
at most `budget + 300` recorded classical calls in the 150-index game. The
world-indexed extractor's own evaluations are still uncharged. -/
theorem h_route_classical_calls_le
    (c : Causal Ω (Fin 150) SignedTx State) (ω : Ω) :
    (transcript c ω).2.length +
      (JointFreshPostprocessing.hPostTranscript (experiment c) ω).2.length ≤
        c.budget + 300 :=
  Nat.add_le_add (transcript_length_le c ω)
    (JointFreshPostprocessing.concrete_h_post_trace_length_le_300
      (experiment c) ω)

theorem r_route_classical_calls_le
    (c : Causal Ω (Fin 150) SignedTx State) (ω : Ω) :
    (transcript c ω).2.length +
      ((JointFreshPostprocessing.rPostTranscript (experiment c) ω).2.1.length +
        (JointFreshPostprocessing.rPostTranscript
          (experiment c) ω).2.2.length) ≤
        c.budget + 600 :=
  Nat.add_le_add (transcript_length_le c ω)
    (JointFreshPostprocessing.concrete_r_post_total_trace_length_le_600
      (experiment c) ω)

end QSB.CausalQueryAlgorithm
