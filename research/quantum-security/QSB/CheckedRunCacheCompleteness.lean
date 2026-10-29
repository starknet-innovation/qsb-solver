import QSB.FullCheckedRunPrefixCausality
import QSB.CheckedRunCacheMachine

/-!
Discharge the response-cache machine's prefix-causality premise for one fixed
source-model checked lock run. The resulting classical machine starts with an
empty cache, asks at most 81 tagged H/R queries, and returns the same checked
result as `CoreCheckedStep.run` under the true oracle pair.

The fixed lock, transaction, selected input, initial stack, key validator,
and ECDSA predicate are inputs to the machine. Constructing them in a larger
world-indexed game, calls hidden inside the external functions, compiled-Core
refinement, and coherent quantum queries are separate obligations.
-/
namespace QSB.CheckedRunCacheCompleteness
open CausalQueryAlgorithm (run)

/-- The concrete checked-run dependency list has the prefix property needed
by the first-missing-query cache machine. -/
theorem trace_prefix_causal
    (p : CheckedRunCacheMachine.FixedInput) :
    CheckedRunCacheMachine.TracePrefixCausal p := by
  intro functions functions' k available agree
  exact FullCheckedRunPrefixCausality.checked_lock_prefix_next
    functions functions' p.tx p.selected p.validKey p.ecdsa p.lock
    p.initial k available agree

/-- The initially empty response-cache machine halts within 81 H/R queries
and reproduces the fixed-input checked source-model result. The recorded
queries are the machine's actual classical requests; they need not equal the
source dependency list when repeated inputs are cached or a failed step has
conservative dependencies. -/
theorem run_81_correct
    (p : CheckedRunCacheMachine.FixedInput)
    (functions : JointSourceChecks.Functions) :
    (run (CheckedRunCacheMachine.machine p) functions 81 []).1 =
        some (CheckedRunCacheMachine.checkedResult p functions) ∧
      (run (CheckedRunCacheMachine.machine p) functions 81 []).2.length ≤
        81 := by
  obtain ⟨out, halted, correct, bound⟩ :=
    CheckedRunCacheMachine.run_81_correct p functions
      (trace_prefix_causal p)
  constructor
  · simpa [correct] using halted
  · exact bound

end QSB.CheckedRunCacheCompleteness
