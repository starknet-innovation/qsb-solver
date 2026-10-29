import QSB.BuilderWitnessPushBridge

/-!
`CScript::IsPushOnly` in Bitcoin Core v27.2 (`script.cpp`)
walks `GetOp` boundaries and checks that every opcode is at most OP_16. The
source-shaped predicate here follows those two branches, including Core's
acceptance of OP_RESERVED by the predicate. The concrete `PushOnlyScriptSig`
evaluator is narrower: it rejects OP_RESERVED and PUSHDATA4.

We prove that every script accepted by that evaluator also passes this
separate source-shaped push-only check. This is a Lean-model implication; it
does not connect to compiled Bitcoin Core or establish that an arbitrary
attacker scriptSig is accepted by the evaluator.
-/
namespace QSB.CorePushOnlyAcceptance
open ByteMachine

/-- Source-shaped `CScript::IsPushOnly` loop with explicit fuel. The `GetOp`
parser consumes a complete opcode, including its PUSHDATA payload. -/
def scan : Nat → Bytes → Bool
  | 0, script => script.isEmpty
  | fuel + 1, script =>
      if script.isEmpty then true
      else
        match CoreGetOp.parse script with
        | none => false
        | some (chunk, rest) =>
            match chunk with
            | [] => false
            | op :: _ => op.toNat ≤ 0x60 && scan fuel rest

def isPushOnly (script : Bytes) : Bool := scan script.length script

private theorem pushedValue_opcode_le
    (op : UInt8) (payload value : Bytes)
    (found : PushOnlyScriptSig.pushedValue (op :: payload) = some value) :
    op.toNat ≤ 0x60 := by
  simp only [PushOnlyScriptSig.pushedValue] at found
  split_ifs at found
  all_goals simp_all
  all_goals omega

private theorem parsePush_source_step
    (script value rest : Bytes)
    (parsed : PushOnlyScriptSig.parsePush script = some (value, rest)) :
    ∃ op payload,
      CoreGetOp.parse script = some (op :: payload, rest) ∧
        op.toNat ≤ 0x60 := by
  unfold PushOnlyScriptSig.parsePush at parsed
  cases hcore : CoreGetOp.parse script with
  | none => simp [hcore] at parsed
  | some pair =>
      rcases pair with ⟨chunk, tail⟩
      cases chunk with
      | nil => simp [hcore, PushOnlyScriptSig.pushedValue] at parsed
      | cons op payload =>
          cases hvalue : PushOnlyScriptSig.pushedValue (op :: payload) with
          | none => simp [hcore, hvalue] at parsed
          | some got =>
              simp [hcore, hvalue] at parsed
              rcases parsed with ⟨rfl, rfl⟩
              exact ⟨op, payload, rfl, pushedValue_opcode_le op payload got hvalue⟩

/-- Successful execution of the narrow push evaluator implies the independent
source-shaped `IsPushOnly` loop accepts the same byte string. This includes
scripts using PUSHDATA1/2 and scripts that are nonminimal under policy flags. -/
theorem runTrace_success_isPushOnly
    (fuel : Nat) (script : Bytes) (stack result : List Bytes) (count : Nat)
    (executed : PushOnlyScriptSig.runTrace fuel script stack =
      (some result, count)) :
    scan fuel script = true := by
  induction fuel generalizing script stack result count with
  | zero =>
      simp only [PushOnlyScriptSig.runTrace] at executed
      simp [scan] at executed ⊢
      exact executed.1.1
  | succ fuel ih =>
      by_cases empty : script.isEmpty
      · simp [scan, empty]
      · cases parsed : PushOnlyScriptSig.parsePush script with
        | none => simp [PushOnlyScriptSig.runTrace, empty, parsed] at executed
        | some pair =>
            rcases pair with ⟨value, rest⟩
            have step := parsePush_source_step script value rest parsed
            rcases step with ⟨op, payload, hcore, small⟩
            simp only [PushOnlyScriptSig.runTrace, empty, parsed] at executed
            by_cases large : value.length > 520 ∨ stack.length ≥ 1000
            · simp [large] at executed
            · have notLarge : ¬ value.length > 520 := by omega
              have room : ¬ stack.length ≥ 1000 := by omega
              simp only [notLarge, room] at executed
              have later :
                  (PushOnlyScriptSig.runTrace fuel rest (stack ++ [value])).1 =
                    some result := by simpa using congrArg Prod.fst executed
              cases hrun : PushOnlyScriptSig.runTrace fuel rest
                  (stack ++ [value]) with
              | mk out n =>
                  have full : PushOnlyScriptSig.runTrace fuel rest
                      (stack ++ [value]) = (some result, n) := by
                    simpa [hrun] using later
                  have tail := ih rest (stack ++ [value]) result n full
                  simp [scan, empty, hcore, small, tail]

theorem execution_success_isPushOnly
    (script : Bytes) (result : List Bytes) (count : Nat)
    (executed : PushOnlyScriptSig.execution script =
      (some result, count)) :
    isPushOnly script = true := by
  simp only [PushOnlyScriptSig.execution] at executed
  by_cases large : script.length > 10000
  · simp [large] at executed
  · simp only [large, ↓reduceIte] at executed
    exact runTrace_success_isPushOnly script.length script [] result count executed

/-- Every resource-bounded builder-token serialization in the proven grammar
passes the source-shaped Core `IsPushOnly` check. This does not prove the
Python builder emits the modeled bytes. -/
theorem builder_tokens_isPushOnly
    (tokens : List BuilderWitnessPushBridge.BuilderToken)
    (scriptSize : (BuilderWitnessPushBridge.encodeTokens tokens).length ≤ 10000)
    (stackCapacity : tokens.length ≤ 1000) :
    isPushOnly (BuilderWitnessPushBridge.encodeTokens tokens) = true := by
  have executed := BuilderWitnessPushBridge.execution_tokens tokens
    scriptSize stackCapacity
  exact execution_success_isPushOnly _
    (BuilderWitnessPushBridge.values tokens) tokens.length executed

end QSB.CorePushOnlyAcceptance
