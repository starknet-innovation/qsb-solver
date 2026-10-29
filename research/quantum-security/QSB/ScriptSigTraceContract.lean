import QSB.DynamicRawSource
import QSB.ScriptSigQueryBudget
import QSB.CausalQueryAlgorithm

/-!
A narrow source-model contract for accounting for H/R dependencies of an
externally supplied scriptSig evaluator. A certificate lists reached opcode
events and the ordered H/R queries attributed to each event. The 201-opcode
limit, event completeness, and evaluator causality must be supplied by whoever
implements the evaluator. No compiled-Core refinement is asserted.
-/
namespace QSB.ScriptSigTraceContract
open ByteMachine
open CausalQueryAlgorithm (Query answer)

def hCount (queries : List Query) : Nat :=
  (queries.filter fun q => match q with | .H _ => true | .R _ => false).length

def rCount (queries : List Query) : Nat :=
  (queries.filter fun q => match q with | .H _ => false | .R _ => true).length

theorem query_length_eq_counts (queries : List Query) :
    queries.length = hCount queries + rCount queries := by
  induction queries with
  | nil => simp [hCount, rCount]
  | cons q rest ih =>
      cases q <;> simp [hCount, rCount] at ih ⊢ <;> omega

/-- One reached opcode event and the modeled H/R queries it makes. Signature
events may charge up to two H calls per attempted checker pair. -/
structure EventQueries where
  event : ScriptSigQueryBudget.Event
  queries : List Query
  valid : ScriptSigQueryBudget.valid event
  hBound : hCount queries ≤ ScriptSigQueryBudget.hCost event
  rBound : rCount queries ≤ ScriptSigQueryBudget.rCost event

theorem event_query_length_le_twice_op (step : EventQueries) :
    step.queries.length ≤ 2 * ScriptSigQueryBudget.opCost step.event := by
  have split := query_length_eq_counts step.queries
  have joint := ScriptSigQueryBudget.event_joint_le_twice_op step.event
    step.valid
  have hBound := step.hBound
  have rBound := step.rBound
  omega

def queries (steps : List EventQueries) : List Query :=
  steps.flatMap EventQueries.queries

def opCost (steps : List EventQueries) : Nat :=
  (steps.map fun step => ScriptSigQueryBudget.opCost step.event).sum

theorem queries_length_le_twice_ops (steps : List EventQueries) :
    (queries steps).length ≤ 2 * opCost steps := by
  induction steps with
  | nil => simp [queries, opCost]
  | cons step rest ih =>
      have current := event_query_length_le_twice_op step
      simp only [queries, opCost, List.flatMap_cons, List.length_append,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- A successful scriptSig evaluation has an externally justified reached
trace, with a source-shaped 201-opcode bound. The congruence fields prevent
the evaluator's result or adaptive query list from depending on unlisted H/R
answers when all non-oracle inputs and external predicates are held fixed.
They are obligations, not consequences of the evaluator's function type. -/
structure Contract where
  eval : JointSourceChecks.Functions → DynamicRawSource.EvalScriptSig
  reached : JointSourceChecks.Functions → SighashAllWire.TxFields → Nat →
    Bytes → List EventQueries
  successfulOps : ∀ functions tx selected scriptSig stack,
    eval functions tx selected scriptSig = some stack →
      opCost (reached functions tx selected scriptSig) ≤ 201
  resultCongr : ∀ functions functions' tx selected scriptSig,
    (∀ q ∈ queries (reached functions tx selected scriptSig),
      answer functions' q = answer functions q) →
    eval functions' tx selected scriptSig =
      eval functions tx selected scriptSig
  queriesCongr : ∀ functions functions' tx selected scriptSig,
    (∀ q ∈ queries (reached functions tx selected scriptSig),
      answer functions' q = answer functions q) →
    queries (reached functions' tx selected scriptSig) =
      queries (reached functions tx selected scriptSig)

/-- If the supplied reached event trace is complete and obeys Core's
source-shaped 201-opcode limit, its explicitly attributed H/R dependencies
contain at most 402 queries. -/
theorem successful_eval_queries_le_402 (contract : Contract)
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes) (stack : List Bytes)
    (success : contract.eval functions tx selected scriptSig = some stack) :
    (queries (contract.reached functions tx selected scriptSig)).length ≤
      402 := by
  have bound := queries_length_le_twice_ops
    (contract.reached functions tx selected scriptSig)
  have ops := contract.successfulOps functions tx selected scriptSig stack
    success
  omega

end QSB.ScriptSigTraceContract
