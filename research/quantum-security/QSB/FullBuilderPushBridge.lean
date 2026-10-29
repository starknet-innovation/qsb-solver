import QSB.BuilderWitnessPushBridge

/-!
Source-level data-push bridge through Bitcoin's 520-byte stack-cell bound.
Unlike `BuilderWitnessPushBridge`, data tokens here may use direct pushes,
PUSHDATA1, or PUSHDATA2. The source-shaped `CoreGetOp` parser and
`PushOnlyScriptSig` evaluator are used; Python and compiled Bitcoin Core
equivalence are not asserted.
-/
namespace QSB.FullBuilderPushBridge
open ByteMachine
open BuilderWitnessPushBridge
set_option maxRecDepth 20000
set_option maxHeartbeats 300000

private theorem parse_of_width (chunk tail : Bytes)
    (width : CoreGetOp.width (chunk ++ tail) = some chunk.length) :
    CoreGetOp.parse (chunk ++ tail) = some (chunk, tail) := by
  simp [CoreGetOp.parse, width]

private theorem parse_pushdata1 (data tail : Bytes)
    (long : 76 ≤ data.length) (small : data.length ≤ 255) :
    PushOnlyScriptSig.parsePush
      (CorePushSerialize.pushPattern data ++ tail) =
      some (data, tail) := by
  have notShort : ¬ data.length < 76 := by omega
  have byteLength : (UInt8.ofNat data.length).toNat = data.length :=
    UInt8.toNat_ofNat_of_lt (by change data.length < 256; omega)
  have pattern : CorePushSerialize.pushPattern data =
      [0x4c, UInt8.ofNat data.length] ++ data := by
    simp [CorePushSerialize.pushPattern, notShort, small]
  rw [pattern]
  have width :
      CoreGetOp.width
        (([0x4c, UInt8.ofNat data.length] ++ data) ++ tail) =
        some (([0x4c, UInt8.ofNat data.length] ++ data).length) := by
    simp [CoreGetOp.width, byteLength, List.length_append]
    omega
  have parsed := parse_of_width
    ([0x4c, UInt8.ofNat data.length] ++ data) tail width
  unfold PushOnlyScriptSig.parsePush
  rw [parsed]
  simp [PushOnlyScriptSig.pushedValue]

private theorem parse_pushdata2 (data tail : Bytes)
    (long : 256 ≤ data.length) (small : data.length ≤ 520) :
    PushOnlyScriptSig.parsePush
      (CorePushSerialize.pushPattern data ++ tail) =
      some (data, tail) := by
  have notShort : ¬ data.length < 76 := by omega
  have notOne : ¬ data.length ≤ 255 := by omega
  have two : data.length ≤ 65535 := by omega
  have low : (UInt8.ofNat data.length).toNat = data.length % 256 := by
    simp
  have high : (UInt8.ofNat (data.length / 256)).toNat =
      data.length / 256 :=
    UInt8.toNat_ofNat_of_lt (by change data.length / 256 < 256; omega)
  have pieces : data.length % 256 + 256 * (data.length / 256) =
      data.length := by omega
  have pattern : CorePushSerialize.pushPattern data =
      [0x4d, UInt8.ofNat data.length,
        UInt8.ofNat (data.length / 256)] ++ data := by
    simp [CorePushSerialize.pushPattern, notShort, notOne, two]
  rw [pattern]
  have width :
      CoreGetOp.width
        (([0x4d, UInt8.ofNat data.length,
          UInt8.ofNat (data.length / 256)] ++ data) ++ tail) =
        some (([0x4d, UInt8.ofNat data.length,
          UInt8.ofNat (data.length / 256)] ++ data).length) := by
    simp [CoreGetOp.width, low, high, pieces,
      List.length_append]
    omega
  have parsed := parse_of_width
    ([0x4d, UInt8.ofNat data.length,
      UInt8.ofNat (data.length / 256)] ++ data) tail width
  unfold PushOnlyScriptSig.parsePush
  rw [parsed]
  simp [PushOnlyScriptSig.pushedValue]

/-- All canonical Core-shaped data pushes through 520 bytes parse to their
exact payload and leave the arbitrary suffix untouched. -/
theorem parse_data_520 (data tail : Bytes) (bounded : data.length ≤ 520) :
    PushOnlyScriptSig.parsePush
      (CorePushSerialize.pushPattern data ++ tail) =
      some (data, tail) := by
  by_cases short : data.length < 76
  · exact BuilderWitnessPushBridge.parse_data data tail short
  · by_cases one : data.length ≤ 255
    · exact parse_pushdata1 data tail (by omega) one
    · exact parse_pushdata2 data tail (by omega) bounded

inductive Token where
  | data (bytes : Bytes) (bounded : bytes.length ≤ 520)
  | number (depth : Fin 256)

def Token.value : Token → Bytes
  | .data bytes _ => bytes
  | .number depth => numberBytes depth

def Token.encode : Token → Bytes
  | .data bytes _ => CorePushSerialize.pushPattern bytes
  | .number depth => (BuilderToken.number depth).encode

theorem token_encode_nonempty (token : Token) : token.encode ≠ [] := by
  cases token with
  | data bytes _ => exact CorePushSerialize.pushPattern_nonempty bytes
  | number depth =>
      simpa [Token.encode] using
        BuilderWitnessPushBridge.encode_nonempty (BuilderToken.number depth)

theorem token_value_length_le_520 (token : Token) :
    token.value.length ≤ 520 := by
  cases token with
  | data bytes bounded => exact bounded
  | number depth =>
      simpa [Token.value] using
        BuilderWitnessPushBridge.value_length_le_520 (.number depth)

theorem parse_token (token : Token) (tail : Bytes) :
    PushOnlyScriptSig.parsePush (token.encode ++ tail) =
      some (token.value, tail) := by
  cases token with
  | data bytes bounded => exact parse_data_520 bytes tail bounded
  | number depth =>
      exact BuilderWitnessPushBridge.parse_number depth tail

def encodeTokens (tokens : List Token) : Bytes :=
  (tokens.map Token.encode).flatten

def values (tokens : List Token) : List Bytes :=
  tokens.map Token.value

theorem token_count_le_script_bytes (tokens : List Token) :
    tokens.length ≤ (encodeTokens tokens).length := by
  induction tokens with
  | nil => simp [encodeTokens]
  | cons token rest ih =>
      have nonempty := token_encode_nonempty token
      have positive : 0 < token.encode.length :=
        List.length_pos_iff_ne_nil.mpr nonempty
      simp [encodeTokens, List.length_append] at ih ⊢
      omega

/-- An arbitrary permitted data/number token list executes to the ordered
bottom-first cells, including PUSHDATA1 and PUSHDATA2 data pushes. -/
theorem runTrace_tokens (tokens : List Token)
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
          have small := token_value_length_le_520 token
          have parsed := parse_token token (encodeTokens rest)
          have scriptNonempty :
              (encodeTokens (token :: rest)).isEmpty = false := by
            simp [encodeTokens, token_encode_nonempty token]
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

theorem execution_tokens (tokens : List Token)
    (scriptSize : (encodeTokens tokens).length ≤ 10000)
    (stackCapacity : tokens.length ≤ 1000) :
    PushOnlyScriptSig.execution (encodeTokens tokens) =
      (some (values tokens), tokens.length) := by
  have enough := token_count_le_script_bytes tokens
  have executed := runTrace_tokens tokens []
    (encodeTokens tokens).length enough (by simpa using stackCapacity)
  simp [PushOnlyScriptSig.execution, show ¬ (encodeTokens tokens).length > 10000
    by omega, executed]

end QSB.FullBuilderPushBridge
