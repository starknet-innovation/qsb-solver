import QSB.ScriptSigTraceContract

/-!
An all-run strengthening of the externally supplied scriptSig trace contract.
`chargedPrefixOps` bounds the cost of the supplied `reached` list on every
result. A future evaluator witness must separately show that this list covers
all actual query-bearing opcode events. Its intended Core interpretation omits
a terminal opcode rejected by an ordinary or CHECKMULTISIG opcode-count guard
before making a modeled query; that interpretation is not proved by this
numeric field. A failed evaluator may still make queries before its failure.

`prefixCausal` states that the next attributed query is fixed by preceding
oracle replies. Together with the inherited result congruence, this is the
trace-level premise for a response-cache machine. These are obligations on a
future evaluator implementation: this module constructs no evaluator, proves
no completeness of its trace against actual calls, and gives no compiled-Core
refinement or quantum-oracle budget. External checker/key-parser effects also
remain outside the H/R inventory.
-/
namespace QSB.ScriptSigBoundedCausalContract
open ByteMachine
open CausalQueryAlgorithm (Query answer)

def trace (contract : ScriptSigTraceContract.Contract)
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes) : List Query :=
  ScriptSigTraceContract.queries
    (contract.reached functions tx selected scriptSig)

/-- An all-run charged prefix bound and one-step adaptive trace causality,
added to the original result and full-list congruence obligations. -/
structure Contract extends ScriptSigTraceContract.Contract where
  chargedPrefixOps : ∀ functions tx selected scriptSig,
    ScriptSigTraceContract.opCost
      (reached functions tx selected scriptSig) ≤ 201
  prefixCausal : ∀ functions functions' tx selected scriptSig k,
    k < (trace toContract functions tx selected scriptSig).length →
    (∀ q ∈ (trace toContract functions tx selected scriptSig).take k,
      answer functions' q = answer functions q) →
    (trace toContract functions' tx selected scriptSig).take (k + 1) =
      (trace toContract functions tx selected scriptSig).take (k + 1)

/-- Every evaluator result, including `none`, has at most 402 attributed
H/R entries under the charged-prefix premise. -/
theorem trace_length_le_402 (contract : Contract)
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes) :
    (trace contract.toContract functions tx selected scriptSig).length ≤
      402 := by
  have eventBound := ScriptSigTraceContract.queries_length_le_twice_ops
    (contract.reached functions tx selected scriptSig)
  have opBound := contract.chargedPrefixOps functions tx selected scriptSig
  dsimp [trace]
  omega

/-- The contract's prefix obligation in the form consumed by an adaptive
query-trace cache: prior replies determine the next query position. -/
theorem trace_prefix (contract : Contract)
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes) (k : Nat)
    (within : k < (trace contract.toContract functions tx selected
      scriptSig).length)
    (agree : ∀ q ∈ (trace contract.toContract functions tx selected
      scriptSig).take k, answer functions' q = answer functions q) :
    (trace contract.toContract functions' tx selected scriptSig).take
      (k + 1) =
    (trace contract.toContract functions tx selected scriptSig).take
      (k + 1) :=
  contract.prefixCausal functions functions' tx selected scriptSig k
    within agree

end QSB.ScriptSigBoundedCausalContract
