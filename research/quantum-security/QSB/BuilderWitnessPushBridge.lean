import QSB.PushOnlyScriptSig
import QSB.CorePushSerialize
import QSB.CoreSerialize
import QSB.DynamicSerializedRound

/-!
A source-level bridge for the forms emitted by the pinned Config A witness
builder: data cells shorter than 76 bytes and nonnegative witness index
numbers below 256. The encoded bytes use the Core-shaped
direct-push pattern and ScriptNum serializer; zero and numbers 1 through 16
use their dedicated push opcodes, as in the builder's `push_number` branch.

The parser and execution theorems concern Lean's source models. This file does
not prove byte-for-byte equality with Python `cmd_assemble`, compiled Bitcoin
Core, arbitrary scriptSig, or PUSHDATA branches for data cells of length 76
or more. Script-size and stack-capacity assumptions remain explicit.
-/
namespace QSB.BuilderWitnessPushBridge
open ByteMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

inductive BuilderToken where
  | data (bytes : Bytes) (short : bytes.length < 76)
  | number (value : Fin 256)

/-- ScriptNum bytes for a permitted nonnegative witness index. The fallback
is unreachable, as the finite-domain theorem below certifies. -/
def numberBytes (n : Fin 256) : Bytes :=
  (CoreSerialize.coreSerialize (Int.ofNat n.val)).getD []

theorem numberBytes_defined :
    ∀ n : Fin 256,
      CoreSerialize.coreSerialize (Int.ofNat n.val) =
        some (numberBytes n) := by decide

theorem numberBytes_short :
    ∀ n : Fin 256, (numberBytes n).length < 76 := by decide

theorem numberBytes_small :
    ∀ n : Fin 256, n.val ≤ 16 →
      numberBytes n =
        if n.val = 0 then [] else [UInt8.ofNat n.val] := by decide

/-- The cell produced by executing one builder token. -/
def BuilderToken.value : BuilderToken → Bytes
  | .data bytes _ => bytes
  | .number n => numberBytes n

/-- Source-shaped byte encoding of the two builder-token forms. -/
def BuilderToken.encode : BuilderToken → Bytes
  | .data bytes _ => CorePushSerialize.pushPattern bytes
  | .number n =>
      if n.val = 0 then [0x00]
      else if n.val ≤ 16 then [UInt8.ofNat (0x50 + n.val)]
      else CorePushSerialize.pushPattern (numberBytes n)

theorem encode_nonempty (token : BuilderToken) :
    token.encode ≠ [] := by
  cases token with
  | data bytes short =>
      exact CorePushSerialize.pushPattern_nonempty bytes
  | number n =>
      simp [BuilderToken.encode]
      split_ifs <;> simp [CorePushSerialize.pushPattern_nonempty]

theorem value_length_le_520 (token : BuilderToken) :
    token.value.length ≤ 520 := by
  cases token with
  | data bytes short =>
      simp [BuilderToken.value]
      omega
  | number n =>
      simp [BuilderToken.value]
      have short := numberBytes_short n
      omega

/-- One canonical short data push leaves the subsequent script untouched. -/
theorem parse_data (bytes tail : Bytes) (short : bytes.length < 76) :
    PushOnlyScriptSig.parsePush
      (CorePushSerialize.pushPattern bytes ++ tail) =
      some (bytes, tail) := by
  have simple := DynamicSerializedRound.short_push_simple bytes short
  have parsed := CoreGetOp.parse_simple_chunk
    (CorePushSerialize.pushPattern bytes) simple tail
  have width : (UInt8.ofNat bytes.length).toNat = bytes.length :=
    UInt8.toNat_ofNat_of_lt (by change bytes.length < 256; omega)
  simp only [PushOnlyScriptSig.parsePush, parsed]
  rw [show CorePushSerialize.pushPattern bytes =
    UInt8.ofNat bytes.length :: bytes by
      simp [CorePushSerialize.pushPattern, short]]
  simp [PushOnlyScriptSig.pushedValue, width,
    show bytes.length ≤ 75 by omega]

/-- Dedicated OP_0, OP_1..OP_16, and direct ScriptNum encodings all decode
to exactly the source-model ScriptNum cell. -/
theorem parse_number (n : Fin 256) (tail : Bytes) :
    PushOnlyScriptSig.parsePush
      ((BuilderToken.number n).encode ++ tail) =
      some (numberBytes n, tail) := by
  by_cases zero : n.val = 0
  · have small : n.val ≤ 16 := by omega
    have value := numberBytes_small n small
    simp [BuilderToken.encode, zero, value,
      PushOnlyScriptSig.parsePush, CoreGetOp.parse, CoreGetOp.width]
    rfl
  · by_cases small : n.val ≤ 16
    · have value := numberBytes_small n small
      have positive : 1 ≤ n.val := by omega
      interval_cases h : n.val <;>
        simp [BuilderToken.encode, zero, small, value, h,
          PushOnlyScriptSig.parsePush, CoreGetOp.parse,
          CoreGetOp.width] <;> rfl
    · have short := numberBytes_short n
      simpa [BuilderToken.encode, zero, small] using
        parse_data (numberBytes n) tail short

theorem parse_token (token : BuilderToken) (tail : Bytes) :
    PushOnlyScriptSig.parsePush (token.encode ++ tail) =
      some (token.value, tail) := by
  cases token with
  | data bytes short =>
      exact parse_data bytes tail short
  | number n =>
      exact parse_number n tail

def encodeTokens (tokens : List BuilderToken) : Bytes :=
  (tokens.map BuilderToken.encode).flatten

def values (tokens : List BuilderToken) : List Bytes :=
  tokens.map BuilderToken.value

theorem token_count_le_script_bytes (tokens : List BuilderToken) :
    tokens.length ≤ (encodeTokens tokens).length := by
  induction tokens with
  | nil => simp [encodeTokens]
  | cons token rest ih =>
      have nonempty := encode_nonempty token
      have positive : 0 < token.encode.length :=
        List.length_pos_iff_ne_nil.mpr nonempty
      simp [encodeTokens, List.length_append] at ih ⊢
      omega

/-- Executing the serialized token stream appends its cells in builder order
to a bottom-first stack, with one reached push event per token. -/
theorem runTrace_tokens (tokens : List BuilderToken)
    (stack : List Bytes) (fuel : Nat)
    (enough : tokens.length ≤ fuel)
    (capacity : stack.length + tokens.length ≤ 1000) :
    PushOnlyScriptSig.runTrace fuel (encodeTokens tokens) stack =
      (some (stack ++ values tokens), tokens.length) := by
  induction tokens generalizing stack fuel with
  | nil =>
      cases fuel <;> simp [encodeTokens, values,
        PushOnlyScriptSig.runTrace]
  | cons token rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have restEnough : rest.length ≤ fuel := by
            simp only [List.length_cons] at enough
            omega
          have restCapacity :
              (stack ++ [token.value]).length + rest.length ≤ 1000 := by
            simp only [List.length_append, List.length_cons,
              List.length_nil] at capacity ⊢
            omega
          have stackRoom : stack.length < 1000 := by
            simp only [List.length_cons] at capacity
            omega
          have small := value_length_le_520 token
          have parsed := parse_token token (encodeTokens rest)
          have scriptNonempty :
              (encodeTokens (token :: rest)).isEmpty = false := by
            simp [encodeTokens, encode_nonempty token]
          have encodedCons :
              encodeTokens (token :: rest) =
                token.encode ++ encodeTokens rest := rfl
          have scriptNonempty' :
              (token.encode ++ encodeTokens rest).isEmpty = false := by
            simpa [encodedCons] using scriptNonempty
          rw [encodedCons]
          simp only [PushOnlyScriptSig.runTrace, scriptNonempty',
            parsed]
          have small' : ¬ token.value.length > 520 := by omega
          have room' : ¬ stack.length ≥ 1000 := by omega
          simp only [small', room']
          rw [ih (stack ++ [token.value]) fuel restEnough restCapacity]
          simp [values, List.append_assoc]

/-- At the evaluator's byte-length fuel, valid builder-token bytes produce
exactly the ordered bottom-first cells. -/
theorem execution_tokens (tokens : List BuilderToken)
    (scriptSize : (encodeTokens tokens).length ≤ 10000)
    (stackCapacity : tokens.length ≤ 1000) :
    PushOnlyScriptSig.execution (encodeTokens tokens) =
      (some (values tokens), tokens.length) := by
  have enough := token_count_le_script_bytes tokens
  have executed := runTrace_tokens tokens []
    (encodeTokens tokens).length enough (by simpa using stackCapacity)
  simp [PushOnlyScriptSig.execution, show ¬ (encodeTokens tokens).length > 10000
    by omega, executed]

end QSB.BuilderWitnessPushBridge
