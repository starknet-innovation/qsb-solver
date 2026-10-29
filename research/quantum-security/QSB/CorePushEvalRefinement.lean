import QSB.PushOnlyScriptSig

/-!
A separate source-shaped model of the push-only fragment of Bitcoin Core
v27.2 `EvalScript` in BASE mode. `CoreGetOp.parse` models GetOp's byte
boundaries. This module independently classifies the resulting opcodes and
stack cells, including PUSHDATA4, and checks the BASE script-size, element-size,
and stack-size limits. The optional minimal-push check represents
`SCRIPT_VERIFY_MINIMALDATA`; the refinement theorem below fixes it to false.

This is a Lean model of the relevant C++ branches, not a proof about compiled
Bitcoin Core or the surrounding `VerifyScript` transaction checks. The model
rejects non-push instructions even though full `EvalScript` executes some of
them. Its success theorem applies only to scripts accepted by the narrower
`PushOnlyScriptSig` evaluator.
-/
namespace QSB.CorePushEvalRefinement
open ByteMachine

/-- Stack cell produced by a parsed `GetOp` chunk under the push branches of
Core's `EvalScript`. Unlike the narrow evaluator, this includes PUSHDATA4. -/
def pushValue : Bytes → Option Bytes
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
      else if n == 0x4e then
        match payload with
        | _a :: _b :: _c :: _d :: data => some data
        | _ => none
      else if n == 0x4f then some [0x81]
      else if 0x51 ≤ n && n ≤ 0x60 then
        some [UInt8.ofNat (n - 0x50)]
      else none

/-- The `CheckMinimalPush` decision for a complete parsed data-push chunk.
The numeric OP_1NEGATE and OP_1..OP_16 branches do not call this check. -/
def minimalDataPush (opcode : UInt8) (value : Bytes) : Bool :=
  if value.isEmpty then opcode.toNat == 0
  else if value.length == 1 &&
      ((1 ≤ (value.head?.getD 0).toNat && (value.head?.getD 0).toNat ≤ 16) ||
       value.head? == some 0x81) then false
  else if value.length ≤ 75 then opcode.toNat == value.length
  else if value.length ≤ 255 then opcode.toNat == 0x4c
  else if value.length ≤ 65535 then opcode.toNat == 0x4d
  else true

/-- One Core-shaped `GetOp` plus push dispatch. The `requireMinimal` argument
corresponds to `SCRIPT_VERIFY_MINIMALDATA`. -/
def parsePush (requireMinimal : Bool) (script : Bytes) :
    Option (Bytes × Bytes) := do
  let (chunk, rest) ← CoreGetOp.parse script
  let value ← pushValue chunk
  match chunk with
  | [] => none
  | opcode :: _ =>
      if requireMinimal && opcode.toNat ≤ 0x4e &&
          !minimalDataPush opcode value then none
      else some (value, rest)

/-- BASE push-fragment execution. The count records decoded pushes reached,
including a push rejected for exceeding a resource limit. -/
def runTrace : Nat → Bytes → List Bytes → Option (List Bytes) × Nat
  | 0, script, stack =>
      (if script.isEmpty then some stack else none, 0)
  | fuel + 1, script, stack =>
      if script.isEmpty then (some stack, 0)
      else
        match parsePush false script with
        | none => (none, 0)
        | some (value, rest) =>
            if value.length > 520 || stack.length ≥ 1000 then (none, 1)
            else
              let later := runTrace fuel rest (stack ++ [value])
              (later.1, later.2 + 1)

/-- BASE execution from an empty stack with `MINIMALDATA` disabled. -/
def execution (script : Bytes) : Option (List Bytes) × Nat :=
  if script.length > 10000 then (none, 0)
  else runTrace script.length script []

private theorem pushValue_of_narrow (chunk value : Bytes)
    (found : PushOnlyScriptSig.pushedValue chunk = some value) :
    pushValue chunk = some value := by
  cases chunk with
  | nil => simp [PushOnlyScriptSig.pushedValue] at found
  | cons op payload =>
      simp only [PushOnlyScriptSig.pushedValue, pushValue] at found ⊢
      by_cases small : op.toNat ≤ 75
      · simpa [small] using found
      · by_cases push1 : op.toNat == 0x4c
        · simpa [small, push1] using found
        · by_cases push2 : op.toNat == 0x4d
          · simpa [small, push1, push2] using found
          · by_cases push4 : op.toNat == 0x4e
            · have op78 : op.toNat = 78 := by simpa using push4
              simp [op78] at found
            · simpa [small, push1, push2, push4] using found

private theorem parsePush_of_narrow (script value rest : Bytes)
    (found : PushOnlyScriptSig.parsePush script = some (value, rest)) :
    parsePush false script = some (value, rest) := by
  unfold PushOnlyScriptSig.parsePush at found
  cases parsed : CoreGetOp.parse script with
  | none => simp [parsed] at found
  | some pair =>
      rcases pair with ⟨chunk, tail⟩
      cases decoded : PushOnlyScriptSig.pushedValue chunk with
      | none => simp [parsed, decoded] at found
      | some got =>
          simp [parsed, decoded] at found
          rcases found with ⟨rfl, rfl⟩
          have core := pushValue_of_narrow chunk got decoded
          cases chunk with
          | nil => simp [PushOnlyScriptSig.pushedValue] at decoded
          | cons opcode payload =>
              simp [parsePush, parsed, core]

/-- Every successful narrow push-only run has the same exact bottom-first
stack and push count in the independently classified Core-shaped BASE push
fragment. -/
theorem runTrace_success (fuel : Nat) (script : Bytes)
    (stack result : List Bytes) (count : Nat)
    (found : PushOnlyScriptSig.runTrace fuel script stack =
      (some result, count)) :
    runTrace fuel script stack = (some result, count) := by
  induction fuel generalizing script stack result count with
  | zero => simpa [PushOnlyScriptSig.runTrace, runTrace] using found
  | succ fuel ih =>
      by_cases empty : script.isEmpty
      · simpa [PushOnlyScriptSig.runTrace, runTrace, empty] using found
      · cases parsed : PushOnlyScriptSig.parsePush script with
        | none => simp [PushOnlyScriptSig.runTrace, empty, parsed] at found
        | some pair =>
            rcases pair with ⟨value, rest⟩
            have coreParsed := parsePush_of_narrow script value rest parsed
            simp only [PushOnlyScriptSig.runTrace, empty, parsed] at found
            by_cases oversized : value.length > 520 ∨ stack.length ≥ 1000
            · simp [oversized] at found
            · have small : ¬ value.length > 520 := by omega
              have room : ¬ stack.length ≥ 1000 := by omega
              simp only [small, room] at found
              cases later : PushOnlyScriptSig.runTrace fuel rest
                  (stack ++ [value]) with
              | mk out n =>
                  have outEq : out = some result := by
                    simpa [later] using congrArg Prod.fst found
                  have countEq : n + 1 = count := by
                    simpa [later] using congrArg Prod.snd found
                  subst out
                  have coreLater := ih rest (stack ++ [value]) result n later
                  simp [runTrace, empty, coreParsed, small, room,
                    coreLater, countEq]

/-- Successful narrow scriptSig execution refines the Core-shaped BASE push
fragment with `MINIMALDATA` disabled, including exact cells/order and count. -/
theorem execution_success (script : Bytes) (result : List Bytes)
    (count : Nat)
    (found : PushOnlyScriptSig.execution script = (some result, count)) :
    execution script = (some result, count) := by
  unfold PushOnlyScriptSig.execution at found
  by_cases large : script.length > 10000
  · simp [large] at found
  · simp only [large, ↓reduceIte] at found
    simpa [execution, large] using
      runTrace_success script.length script [] result count found

/-- Core's PUSHDATA4 empty push lies outside the narrow evaluator grammar. -/
theorem pushdata4_empty_boundary :
    parsePush false [0x4e, 0, 0, 0, 0] = some ([], []) ∧
      PushOnlyScriptSig.parsePush [0x4e, 0, 0, 0, 0] = none := by
  decide

/-- A direct one-byte push of `1` is accepted by the narrow evaluator but
rejected by Core's `MINIMALDATA` branch, which requires OP_1. -/
theorem minimaldata_singleton_boundary :
    parsePush true [0x01, 0x01] = none ∧
      PushOnlyScriptSig.parsePush [0x01, 0x01] = some ([0x01], []) := by
  decide

end QSB.CorePushEvalRefinement
