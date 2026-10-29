import QSB.ScriptSigBoundedCausalContract
import QSB.FullCheckedRunPrefixCausality

/-!
A concrete, deliberately narrow scriptSig evaluator. It accepts only a direct
push of an opening, `OP_HASH160`, a direct push of the expected digest,
`OP_EQUALVERIFY`, and a final direct push of one lock-entry stack cell. Direct
pushes use the 0–75-byte form. The initial push and HASH160 opcode are
validated before execution; unsupported prefixes therefore make no query.
Once HASH160 is reached, malformed suffixes and failed equality still retain
its H then R calls. A successful result is the bottom-first stack `[payload]`.

This module witnesses the all-run scriptSig trace contract for that restricted
evaluator only. It does not execute arbitrary bare scriptSig, PUSHDATA forms,
signature checks, or compiled Bitcoin Core. Its event list records the
recognized instructions of this fragment, and its separate classical machine
shows that the attributed H/R list is the actual two-request transcript.
-/
namespace QSB.RestrictedScriptSigHash160
open ByteMachine
open CausalQueryAlgorithm (Query answer)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Decode one direct push, including OP_0, and reject larger push encodings. -/
def directPush : Bytes → Option (Bytes × Bytes)
  | [] => none
  | size :: rest =>
      if size.toNat ≤ 75 ∧ size.toNat ≤ rest.length then
        some (rest.take size.toNat, rest.drop size.toNat)
      else none

/-- The HASH160 site is reached only after a valid first direct push and the
literal HASH160 opcode. The unparsed suffix is retained for post-query work. -/
def hashPrefix (scriptSig : Bytes) : Option (Bytes × Bytes) := do
  let (opening, rest) ← directPush scriptSig
  if rest.head? == some 0xa9 then
    some (opening, rest.drop 1)
  else none

/-- After H and R have answered, compare the expected digest and decode the
one final direct push. A malformed suffix or mismatch returns `none`. -/
def suffix (rest digest : Bytes) : Option (List Bytes) := do
  let (expected, afterPush) ← directPush rest
  if afterPush.head? != some 0x88 then none
  else if digest != expected then none
  else do
    let (payload, trailing) ← directPush (afterPush.drop 1)
    if trailing = [] then some [payload] else none

/-- The restricted evaluator ignores transaction fields because it has no
signature opcode. Its result is a bottom-first stack. -/
def eval (functions : JointSourceChecks.Functions)
    (_tx : SighashAllWire.TxFields) (_selected : Nat)
    (scriptSig : Bytes) : Option (List Bytes) :=
  match hashPrefix scriptSig with
  | none => none
  | some (opening, rest) =>
      suffix rest (functions.R (functions.H opening))

private def pushEvent : ScriptSigTraceContract.EventQueries where
  event := .uncounted
  queries := []
  valid := by trivial
  hBound := by simp [ScriptSigTraceContract.hCount,
    ScriptSigQueryBudget.hCost]
  rBound := by simp [ScriptSigTraceContract.rCount,
    ScriptSigQueryBudget.rCost]

private def equalEvent : ScriptSigTraceContract.EventQueries where
  event := .other
  queries := []
  valid := by trivial
  hBound := by simp [ScriptSigTraceContract.hCount,
    ScriptSigQueryBudget.hCost]
  rBound := by simp [ScriptSigTraceContract.rCount,
    ScriptSigQueryBudget.rCost]

private def hashEvent (functions : JointSourceChecks.Functions)
    (opening : Bytes) : ScriptSigTraceContract.EventQueries where
  event := .hash160
  queries := [.H opening, .R (functions.H opening)]
  valid := by trivial
  hBound := by simp [ScriptSigTraceContract.hCount,
    ScriptSigQueryBudget.hCost]
  rBound := by simp [ScriptSigTraceContract.rCount,
    ScriptSigQueryBudget.rCost]

/-- Query-free reached suffix instructions, including the equality opcode on
a failed digest comparison. A parsed final push is recorded even when an
unsupported trailing byte makes the overall evaluator fail. -/
private def tailEvents (functions : JointSourceChecks.Functions)
    (opening rest : Bytes) : List ScriptSigTraceContract.EventQueries :=
  match directPush rest with
  | none => []
  | some (expected, afterPush) =>
      [pushEvent] ++
      if afterPush.head? == some 0x88 then
        [equalEvent] ++
        if functions.R (functions.H opening) == expected then
          match directPush (afterPush.drop 1) with
          | none => []
          | some _ => [pushEvent]
        else []
      else []

/-- Reached instructions in the restricted evaluator; only HASH160 carries
H/R queries. The hashPrefix's initial direct push is prevalidated together with
HASH160. -/
def reached (functions : JointSourceChecks.Functions)
    (scriptSig : Bytes) : List ScriptSigTraceContract.EventQueries :=
  match hashPrefix scriptSig with
  | none => []
  | some (opening, rest) =>
      [pushEvent, hashEvent functions opening] ++
        tailEvents functions opening rest

private theorem tailEvents_queries_nil
    (functions : JointSourceChecks.Functions)
    (opening rest : Bytes) :
    ScriptSigTraceContract.queries (tailEvents functions opening rest) =
      [] := by
  unfold tailEvents
  split
  · simp [ScriptSigTraceContract.queries]
  · split_ifs <;> (try split) <;>
      simp [ScriptSigTraceContract.queries, pushEvent, equalEvent]

private theorem tailEvents_opCost_le_one
    (functions : JointSourceChecks.Functions)
    (opening rest : Bytes) :
    ScriptSigTraceContract.opCost (tailEvents functions opening rest) ≤
      1 := by
  unfold tailEvents
  split
  · simp [ScriptSigTraceContract.opCost]
  · split_ifs <;> (try split) <;>
      simp [ScriptSigTraceContract.opCost, pushEvent, equalEvent,
        ScriptSigQueryBudget.opCost]

/-- The attributed ordered H/R list is exactly H(opening), then R of H's
answer, even if post-hash parsing or equality later fails. -/
theorem queries_reached (functions : JointSourceChecks.Functions)
    (scriptSig : Bytes) :
    ScriptSigTraceContract.queries (reached functions scriptSig) =
      match hashPrefix scriptSig with
      | none => []
      | some (opening, _) =>
          [.H opening, .R (functions.H opening)] := by
  cases found : hashPrefix scriptSig with
  | none => simp [reached, found, ScriptSigTraceContract.queries]
  | some pair =>
      obtain ⟨opening, rest⟩ := pair
      have tail : (tailEvents functions opening rest).flatMap
          ScriptSigTraceContract.EventQueries.queries = [] :=
        tailEvents_queries_nil functions opening rest
      simp only [reached, found, ScriptSigTraceContract.queries,
        List.flatMap_append]
      rw [tail]
      simp [hashEvent, pushEvent]

private theorem opCost_reached_le_two
    (functions : JointSourceChecks.Functions)
    (scriptSig : Bytes) :
    ScriptSigTraceContract.opCost (reached functions scriptSig) ≤ 2 := by
  cases found : hashPrefix scriptSig with
  | none => simp [reached, found, ScriptSigTraceContract.opCost]
  | some pair =>
      obtain ⟨opening, rest⟩ := pair
      have tail := tailEvents_opCost_le_one functions opening rest
      simp [reached, found, ScriptSigTraceContract.opCost,
        pushEvent, hashEvent, ScriptSigQueryBudget.opCost] at tail ⊢
      omega

/-- Before the first request, the opening is fixed by the script bytes;
after it, that H reply fixes the R request's input. -/
theorem queries_hashPrefixCausal
    (functions functions' : JointSourceChecks.Functions)
    (scriptSig : Bytes) (k : Nat)
    (within : k < (ScriptSigTraceContract.queries
      (reached functions scriptSig)).length)
    (agree : ∀ q ∈ (ScriptSigTraceContract.queries
      (reached functions scriptSig)).take k,
      answer functions' q = answer functions q) :
    (ScriptSigTraceContract.queries
      (reached functions' scriptSig)).take (k + 1) =
    (ScriptSigTraceContract.queries
      (reached functions scriptSig)).take (k + 1) := by
  cases found : hashPrefix scriptSig with
  | none => simp [queries_reached, found] at within
  | some pair =>
      obtain ⟨opening, rest⟩ := pair
      have causal := FullCheckedRunPrefixCausality.two_stage_prefix
        (.H opening)
        (fun f : JointSourceChecks.Functions => .R (f.H opening))
        (by
          intro f g same
          simp only [answer] at same
          simp [same])
      simpa [queries_reached, found] using
        (causal functions functions' k
          (by simpa [queries_reached, found] using within)
          (by simpa [queries_reached, found] using agree))

/-- Full agreement on this two-query list fixes the evaluator's optional
bottom-first stack. -/
theorem eval_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes)
    (agree : ∀ q ∈ ScriptSigTraceContract.queries
      (reached functions scriptSig),
      answer functions' q = answer functions q) :
    eval functions' tx selected scriptSig =
      eval functions tx selected scriptSig := by
  cases found : hashPrefix scriptSig with
  | none => simp [eval, found]
  | some pair =>
      obtain ⟨opening, rest⟩ := pair
      have sameH : functions'.H opening = functions.H opening := by
        exact agree (.H opening) (by simp [queries_reached, found])
      have sameR : functions'.R (functions.H opening) =
          functions.R (functions.H opening) := by
        exact agree (.R (functions.H opening))
          (by simp [queries_reached, found])
      simp [eval, found, sameH, sameR]

/-- Full agreement also fixes the attributed adaptive query list. -/
theorem queries_congr
    (functions functions' : JointSourceChecks.Functions)
    (scriptSig : Bytes)
    (agree : ∀ q ∈ ScriptSigTraceContract.queries
      (reached functions scriptSig),
      answer functions' q = answer functions q) :
    ScriptSigTraceContract.queries (reached functions' scriptSig) =
      ScriptSigTraceContract.queries (reached functions scriptSig) := by
  cases found : hashPrefix scriptSig with
  | none => simp [queries_reached, found]
  | some pair =>
      obtain ⟨opening, rest⟩ := pair
      have sameH : functions'.H opening = functions.H opening := by
        exact agree (.H opening) (by simp [queries_reached, found])
      simp [queries_reached, found, sameH]

/-- A concrete inhabitant of the all-run contract for this restricted
evaluator. Every reached trace costs at most two counted opcodes. -/
def contract : ScriptSigBoundedCausalContract.Contract where
  eval := eval
  reached := fun functions _ _ scriptSig => reached functions scriptSig
  successfulOps := by
    intro functions tx selected scriptSig stack _
    have bound := opCost_reached_le_two functions scriptSig
    simpa using (le_trans bound (by omega : 2 ≤ 201))
  resultCongr := by
    intro functions functions' tx selected scriptSig agree
    exact eval_congr functions functions' tx selected scriptSig agree
  queriesCongr := by
    intro functions functions' tx selected scriptSig agree
    exact queries_congr functions functions' scriptSig agree
  chargedPrefixOps := by
    intro functions tx selected scriptSig
    exact (opCost_reached_le_two functions scriptSig).trans (by omega)
  prefixCausal := by
    intro functions functions' tx selected scriptSig k within agree
    exact queries_hashPrefixCausal functions functions' scriptSig k within agree

/-- A machine phase stores only replies already received. -/
inductive Phase where
  | start
  | afterH (rest hReply : Bytes)
  | afterR (rest rReply : Bytes)

/-- A concrete two-request classical implementation of the restricted
evaluator. Its step never consults the true H/R functions. -/
def machine (scriptSig : Bytes) :
    CausalQueryAlgorithm.Machine Phase (Option (List Bytes)) where
  step := fun phase =>
    match phase with
    | .start =>
        match hashPrefix scriptSig with
        | none => .inl none
        | some (opening, _) => .inr (.H opening)
    | .afterH _ hReply => .inr (.R hReply)
    | .afterR rest rReply => .inl (suffix rest rReply)
  resume := fun phase reply =>
    match phase with
    | .start =>
        match hashPrefix scriptSig with
        | none => .start
        | some (_, rest) => .afterH rest reply
    | .afterH rest _ => .afterR rest reply
    | .afterR rest rReply => .afterR rest rReply

/-- The machine always halts in two requests and records exactly the
attributed H/R calls, including on failed post-hash continuation paths. -/
theorem machine_run_exact
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes) :
    CausalQueryAlgorithm.run (machine scriptSig) functions 2 .start =
      (some (eval functions tx selected scriptSig),
        (ScriptSigTraceContract.queries (reached functions scriptSig)).map
          (fun q => (q, answer functions q))) := by
  cases found : hashPrefix scriptSig with
  | none =>
      simp [CausalQueryAlgorithm.run, machine, eval, found,
        queries_reached]
  | some pair =>
      obtain ⟨opening, rest⟩ := pair
      simp [CausalQueryAlgorithm.run, machine, eval, found,
        queries_reached, answer]

/-- If the suffix is malformed immediately after HASH160, both hash
requests were already made and the evaluator returns failure. -/
theorem malformed_after_hash
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig opening rest : Bytes)
    (found : hashPrefix scriptSig = some (opening, rest))
    (bad : directPush rest = none) :
    eval functions tx selected scriptSig = none ∧
      (CausalQueryAlgorithm.run (machine scriptSig) functions 2 .start).2.map
        Prod.fst = [.H opening, .R (functions.H opening)] := by
  constructor
  · simp [eval, found, suffix, bad]
  · rw [machine_run_exact functions tx selected]
    simp [queries_reached, found]

/-- A reached equality mismatch also returns failure after both requests. -/
theorem equality_failure
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig opening rest expected afterPush : Bytes)
    (found : hashPrefix scriptSig = some (opening, rest))
    (pushed : directPush rest = some (expected, afterPush))
    (opcode : afterPush.head? = some 0x88)
    (mismatch : functions.R (functions.H opening) ≠ expected) :
    eval functions tx selected scriptSig = none ∧
      (CausalQueryAlgorithm.run (machine scriptSig) functions 2 .start).2.map
        Prod.fst = [.H opening, .R (functions.H opening)] := by
  constructor
  · simp [eval, found, suffix, pushed, opcode, mismatch]
  · rw [machine_run_exact functions tx selected]
    simp [queries_reached, found]

end QSB.RestrictedScriptSigHash160
