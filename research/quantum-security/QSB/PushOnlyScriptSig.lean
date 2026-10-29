import QSB.CoreGetOp
import QSB.ScriptSigBoundedCausalContract

/-!
A source-level evaluator for a restricted push-only scriptSig grammar. It
accepts OP_0, direct pushes, PUSHDATA1, PUSHDATA2, OP_1NEGATE, and OP_1 through
OP_16. These forms cover the pinned app builder's `push_data` and
`push_number` outputs when each element fits Bitcoin's 520-byte stack-cell
limit. The evaluator also checks a 10000-byte script limit and a 1000-cell
main-stack limit, returning a bottom-first stack.

`CoreGetOp.parse` supplies source-shaped opcode boundaries; this module does
not prove equivalence to compiled Bitcoin Core, the Python witness builder,
or arbitrary scriptSig execution. Unsupported opcodes (including signature
checks) are rejected. No H/R oracle function is consulted by this evaluator.
-/
namespace QSB.PushOnlyScriptSig
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- Interpret the bytes of one complete source-shaped parsed push opcode.
`CoreGetOp.parse` checks the data length before this classifier is called. -/
def pushedValue : Bytes → Option Bytes
  | [] => none
  | op :: payload =>
      let n := op.toNat
      if n ≤ 75 then some payload
      else if n == 0x4c then
        match payload with
        | _size :: data => some data
        | [] => none
      else if n == 0x4d then
        match payload with
        | _lo :: _hi :: data => some data
        | _ => none
      else if n == 0x4f then some [0x81]
      else if 0x51 ≤ n && n ≤ 0x60 then
        some [UInt8.ofNat (n - 0x50)]
      else none

/-- Parse one supported push and return its exact stack cell and remaining
script bytes. PUSHDATA4 is deliberately outside this builder grammar. -/
def parsePush (script : Bytes) : Option (Bytes × Bytes) := do
  let (chunk, rest) ← CoreGetOp.parse script
  let value ← pushedValue chunk
  some (value, rest)

/-- Execute at most `fuel` push opcodes. The second component counts decoded
pushes reached before halt or rejection, including the push that exceeds a
resource limit. No branch depends on H or R. -/
def runTrace : Nat → Bytes → List Bytes → Option (List Bytes) × Nat
  | 0, script, stack =>
      (if script.isEmpty then some stack else none, 0)
  | fuel + 1, script, stack =>
      if script.isEmpty then (some stack, 0)
      else
        match parsePush script with
        | none => (none, 0)
        | some (value, rest) =>
            if value.length > 520 || stack.length ≥ 1000 then (none, 1)
            else
              let later := runTrace fuel rest (stack ++ [value])
              (later.1, later.2 + 1)

/-- Global script-size rejection precedes any opcode. The evaluator runs
from an empty stack with one unit of fuel per input byte. -/
def execution (scriptSig : Bytes) : Option (List Bytes) × Nat :=
  if scriptSig.length > 10000 then (none, 0)
  else runTrace scriptSig.length scriptSig []

/-- Transaction fields are unused because this grammar contains no
signature opcode. A successful result is the bottom-first stack. -/
def eval (_tx : SighashAllWire.TxFields) (_selected : Nat)
    (scriptSig : Bytes) : Option (List Bytes) :=
  (execution scriptSig).1

private def pushEvent : ScriptSigTraceContract.EventQueries where
  event := .uncounted
  queries := []
  valid := by trivial
  hBound := by simp [ScriptSigTraceContract.hCount,
    ScriptSigQueryBudget.hCost]
  rBound := by simp [ScriptSigTraceContract.rCount,
    ScriptSigQueryBudget.rCost]

/-- One query-free event per decoded push reached by the source evaluator. -/
def reached (scriptSig : Bytes) : List ScriptSigTraceContract.EventQueries :=
  List.replicate (execution scriptSig).2 pushEvent

private theorem queries_replicate_pushEvent (count : Nat) :
    ScriptSigTraceContract.queries
      (List.replicate count pushEvent) = [] := by
  simp [ScriptSigTraceContract.queries, pushEvent]

theorem queries_reached_nil (scriptSig : Bytes) :
    ScriptSigTraceContract.queries (reached scriptSig) = [] :=
  queries_replicate_pushEvent (execution scriptSig).2

private theorem opCost_replicate_pushEvent (count : Nat) :
    ScriptSigTraceContract.opCost
      (List.replicate count pushEvent) = 0 := by
  simp [ScriptSigTraceContract.opCost, pushEvent,
    ScriptSigQueryBudget.opCost]

theorem opCost_reached_zero (scriptSig : Bytes) :
    ScriptSigTraceContract.opCost (reached scriptSig) = 0 :=
  opCost_replicate_pushEvent (execution scriptSig).2

/-- The all-run contract has no H/R dependencies: every attributed event is
a push and has zero query and counted-opcode cost. -/
def contract : ScriptSigBoundedCausalContract.Contract where
  eval := fun _functions => eval
  reached := fun _functions _tx _selected scriptSig => reached scriptSig
  successfulOps := by
    intro functions tx selected scriptSig stack _
    rw [opCost_reached_zero]
    omega
  resultCongr := by
    intro functions functions' tx selected scriptSig _
    rfl
  queriesCongr := by
    intro functions functions' tx selected scriptSig _
    rfl
  chargedPrefixOps := by
    intro functions tx selected scriptSig
    rw [opCost_reached_zero]
    omega
  prefixCausal := by
    intro functions functions' tx selected scriptSig k within _
    change k < (ScriptSigTraceContract.queries
      (reached scriptSig)).length at within
    simp [queries_reached_nil] at within

/-- A concrete zero-request implementation of the pure push-only evaluator. -/
def machine (scriptSig : Bytes) :
    CausalQueryAlgorithm.Machine Unit (Option (List Bytes)) where
  step := fun _ => .inl (execution scriptSig).1
  resume := fun state _ => state

theorem machine_run_zero
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes) :
    CausalQueryAlgorithm.run (machine scriptSig) functions 0 () =
      (some (eval tx selected scriptSig),
        (ScriptSigTraceContract.queries (reached scriptSig)).map
          (fun q => (q, answer functions q))) := by
  simp [CausalQueryAlgorithm.run, machine, eval, queries_reached_nil]

end QSB.PushOnlyScriptSig
