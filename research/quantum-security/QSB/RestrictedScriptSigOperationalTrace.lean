import QSB.RestrictedScriptSigHash160

/-!
An instrumented operational interpreter for the deliberately restricted
direct-push `HASH160`/`EQUALVERIFY` scriptSig fragment. It records every
recognized event in its output, as well as every actual H/R request in the
ordinary `CausalQueryAlgorithm.run` log. Its suffix interpreter makes each
parse, equality, and final-push branch independently of the existing
`RestrictedScriptSigHash160.reached` definition.

The first direct push and HASH160 opcode are validated atomically by
`hashPrefix` before the first event or query. Thus a malformed or unsupported
prefix has an empty event list. This is the restricted evaluator's semantics,
not byte-by-byte Bitcoin Core execution. No arbitrary scriptSig, PUSHDATA,
signature, or compiled-Core refinement follows.
-/
namespace QSB.RestrictedScriptSigOperationalTrace
open ByteMachine
open CausalQueryAlgorithm (Query answer)
open ScriptSigTraceContract (EventQueries)

private def pushEvent : EventQueries where
  event := .uncounted
  queries := []
  valid := by trivial
  hBound := by simp [ScriptSigTraceContract.hCount,
    ScriptSigQueryBudget.hCost]
  rBound := by simp [ScriptSigTraceContract.rCount,
    ScriptSigQueryBudget.rCost]

private def equalEvent : EventQueries where
  event := .other
  queries := []
  valid := by trivial
  hBound := by simp [ScriptSigTraceContract.hCount,
    ScriptSigQueryBudget.hCost]
  rBound := by simp [ScriptSigTraceContract.rCount,
    ScriptSigQueryBudget.rCost]

/-- The R request's input is the H reply already stored in the phase. -/
private def hashEvent (opening hReply : Bytes) : EventQueries where
  event := .hash160
  queries := [.H opening, .R hReply]
  valid := by trivial
  hBound := by simp [ScriptSigTraceContract.hCount,
    ScriptSigQueryBudget.hCost]
  rBound := by simp [ScriptSigTraceContract.rCount,
    ScriptSigQueryBudget.rCost]

/-- Execute the query-free suffix. An expected direct push is recorded even
if the next opcode is unsupported; EQUALVERIFY is recorded before a failed
digest comparison; a final push is recorded before rejecting trailing bytes. -/
def finish (rest digest : Bytes) :
    Option (List Bytes) × List EventQueries :=
  match RestrictedScriptSigHash160.directPush rest with
  | none => (none, [])
  | some (expected, afterPush) =>
      if afterPush.head? == some 0x88 then
        if digest == expected then
          match RestrictedScriptSigHash160.directPush
              (afterPush.drop 1) with
          | none => (none, [pushEvent, equalEvent])
          | some (payload, trailing) =>
              (if trailing = [] then some [payload] else none,
                [pushEvent, equalEvent, pushEvent])
        else (none, [pushEvent, equalEvent])
      else (none, [pushEvent])

/-- A direct description of which suffix instructions were recognized.
`finish` does not call this definition; the next lemma checks its branches. -/
private def suffixEvents (rest digest : Bytes) : List EventQueries :=
  match RestrictedScriptSigHash160.directPush rest with
  | none => []
  | some (expected, afterPush) =>
      [pushEvent] ++
      if afterPush.head? == some 0x88 then
        [equalEvent] ++
        if digest == expected then
          match RestrictedScriptSigHash160.directPush
              (afterPush.drop 1) with
          | none => []
          | some _ => [pushEvent]
        else []
      else []

private theorem finish_result (rest digest : Bytes) :
    (finish rest digest).1 =
      RestrictedScriptSigHash160.suffix rest digest := by
  cases pushed : RestrictedScriptSigHash160.directPush rest with
  | none => simp [finish, RestrictedScriptSigHash160.suffix, pushed]
  | some pair =>
      obtain ⟨expected, afterPush⟩ := pair
      by_cases opcode : afterPush.head? = some 0x88
      · by_cases same : digest = expected
        · cases finalPush : RestrictedScriptSigHash160.directPush
            afterPush.tail with
          | none =>
              simp [finish, RestrictedScriptSigHash160.suffix,
                pushed, opcode, same, finalPush, List.drop_one]
          | some pair =>
              obtain ⟨payload, trailing⟩ := pair
              simp [finish, RestrictedScriptSigHash160.suffix,
                pushed, opcode, same, finalPush, List.drop_one]
        · simp [finish, RestrictedScriptSigHash160.suffix,
            pushed, opcode, same]
      · simp [finish, RestrictedScriptSigHash160.suffix,
          pushed, opcode]

private theorem finish_events (rest digest : Bytes) :
    (finish rest digest).2 = suffixEvents rest digest := by
  cases pushed : RestrictedScriptSigHash160.directPush rest with
  | none => simp [finish, suffixEvents, pushed]
  | some pair =>
      obtain ⟨expected, afterPush⟩ := pair
      by_cases opcode : afterPush.head? = some 0x88
      · by_cases same : digest = expected
        · cases finalPush : RestrictedScriptSigHash160.directPush
            afterPush.tail with
          | none =>
              simp [finish, suffixEvents, pushed, opcode, same,
                finalPush, List.drop_one]
          | some pair =>
              obtain ⟨payload, trailing⟩ := pair
              simp [finish, suffixEvents, pushed, opcode, same,
                finalPush, List.drop_one]
        · simp [finish, suffixEvents, pushed, opcode, same]
      · simp [finish, suffixEvents, pushed, opcode]

private theorem suffixEvents_queries_nil (rest digest : Bytes) :
    ScriptSigTraceContract.queries (suffixEvents rest digest) = [] := by
  unfold suffixEvents
  split
  · simp [ScriptSigTraceContract.queries]
  · split_ifs <;> (try split) <;>
      simp [ScriptSigTraceContract.queries, pushEvent, equalEvent]

private theorem suffixEvents_each_queries_nil (rest digest : Bytes) :
    ∀ event ∈ suffixEvents rest digest, event.queries = [] := by
  unfold suffixEvents
  split
  · simp
  · split_ifs <;> (try split) <;>
      simp [pushEvent, equalEvent]

private theorem reached_of_prefix
    (functions : JointSourceChecks.Functions)
    (scriptSig opening rest : Bytes)
    (found : RestrictedScriptSigHash160.hashPrefix scriptSig =
      some (opening, rest)) :
    RestrictedScriptSigHash160.reached functions scriptSig =
      [pushEvent, hashEvent opening (functions.H opening)] ++
        suffixEvents rest (functions.R (functions.H opening)) := by
  simp only [RestrictedScriptSigHash160.reached, found]
  rfl

/-- The H reply and R reply are retained until the final stack and event
list can be produced. -/
inductive Phase where
  | start
  | afterH (opening rest hReply : Bytes)
  | afterR (opening rest hReply rReply : Bytes)

/-- An operational machine whose output contains both the final stack result
and the recognized event list. No step consults an H/R function directly. -/
def machine (scriptSig : Bytes) :
    CausalQueryAlgorithm.Machine Phase
      (Option (List Bytes) × List EventQueries) where
  step := fun phase =>
    match phase with
    | .start =>
        match RestrictedScriptSigHash160.hashPrefix scriptSig with
        | none => .inl (none, [])
        | some (opening, _) => .inr (.H opening)
    | .afterH _ _ hReply => .inr (.R hReply)
    | .afterR opening rest hReply rReply =>
        let suffix := finish rest rReply
        .inl (suffix.1,
          [pushEvent, hashEvent opening hReply] ++ suffix.2)
  resume := fun phase reply =>
    match phase with
    | .start =>
        match RestrictedScriptSigHash160.hashPrefix scriptSig with
        | none => .start
        | some (opening, rest) => .afterH opening rest reply
    | .afterH opening rest hReply =>
        .afterR opening rest hReply reply
    | .afterR opening rest hReply rReply =>
        .afterR opening rest hReply rReply

/-- The complete operational output agrees with the restricted evaluator's
stack and its entire reached-event list, while the machine's separate H/R log
agrees with the attributed query projection. This includes failures after
HASH160. -/
theorem run_exact (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptSig : Bytes) :
    CausalQueryAlgorithm.run (machine scriptSig) functions 2 .start =
      (some (RestrictedScriptSigHash160.eval functions tx selected scriptSig,
        RestrictedScriptSigHash160.reached functions scriptSig),
        (ScriptSigTraceContract.queries
          (RestrictedScriptSigHash160.reached functions scriptSig)).map
            (fun q => (q, answer functions q))) := by
  cases found : RestrictedScriptSigHash160.hashPrefix scriptSig with
  | none =>
      simp [CausalQueryAlgorithm.run, machine,
        RestrictedScriptSigHash160.eval,
        RestrictedScriptSigHash160.reached, found,
        ScriptSigTraceContract.queries]
  | some pair =>
      obtain ⟨opening, rest⟩ := pair
      rw [reached_of_prefix functions scriptSig opening rest found]
      simp [CausalQueryAlgorithm.run, machine,
        RestrictedScriptSigHash160.eval, found,
        ScriptSigTraceContract.queries, answer,
        finish_result, finish_events, pushEvent, hashEvent]
      exact suffixEvents_each_queries_nil rest
        (functions.R (functions.H opening))

end QSB.RestrictedScriptSigOperationalTrace
