import QSB.CoreScriptNum
import QSB.CoreSerialize
import QSB.ByteIndexRange
import QSB.FirstNumericRange

/-!
Source-shaped numeric operations for Bitcoin Core v27.2's `OP_MIN` and
`OP_ADD`: parse two four-byte ScriptNums, perform integer arithmetic, and
serialize the result. This module proves byte equality with `ByteMachine`'s
numeric substeps for every byte pair and relates the reached `OP_MIN` and
`OP_ADD` stack steps under the opcode budget. It does not refine the compiled
interpreter or its full execution trace.
-/
namespace QSB.CoreNumericOps
open ByteMachine

def coreMin (x y : Bytes) : Option Bytes := do
  let a ← CoreScriptNum.coreSetVch x
  let b ← CoreScriptNum.coreSetVch y
  CoreSerialize.coreSerialize (min a b)

def modelMin (x y : Bytes) : Option Bytes := do
  let a ← ByteIndex.parseScriptNum x
  let b ← ByteIndex.parseScriptNum y
  ByteIndex.encodeScriptNum (min a b)

def coreAdd (x y : Bytes) : Option Bytes := do
  let a ← CoreScriptNum.coreSetVch x
  let b ← CoreScriptNum.coreSetVch y
  CoreSerialize.coreSerialize (a + b)

def modelAdd (x y : Bytes) : Option Bytes := do
  let a ← ByteIndex.parseScriptNum x
  let b ← ByteIndex.parseScriptNum y
  ByteIndex.encodeScriptNum (a + b)

/-- Both source-shaped parsing and serialization agree for every byte pair,
including negative, nonminimal, and oversized operand encodings. -/
theorem coreMin_eq_model (x y : Bytes) :
    coreMin x y = modelMin x y := by
  simp [coreMin, modelMin, CoreScriptNum.coreSetVch_eq_parseScriptNum,
    CoreSerialize.coreSerialize_eq_model]

theorem coreAdd_eq_model (x y : Bytes) :
    coreAdd x y = modelAdd x y := by
  simp [coreAdd, modelAdd, CoreScriptNum.coreSetVch_eq_parseScriptNum,
    CoreSerialize.coreSerialize_eq_model]

theorem coreMin_defined_of_parsed (x y : Bytes) (a b : Int)
    (parsedX : ByteIndex.parseScriptNum x = some a)
    (parsedY : ByteIndex.parseScriptNum y = some b) :
    ∃ raw, coreMin x y = some raw := by
  obtain ⟨raw, encoded⟩ :=
    ByteIndexRange.min_parsed_defined x y a b parsedX parsedY
  refine ⟨raw, ?_⟩
  simpa [coreMin_eq_model, modelMin, parsedX, parsedY] using encoded

theorem coreAdd_defined_of_parsed (x y : Bytes) (a b : Int)
    (parsedX : ByteIndex.parseScriptNum x = some a)
    (parsedY : ByteIndex.parseScriptNum y = some b) :
    ∃ raw, coreAdd x y = some raw := by
  obtain ⟨raw, encoded⟩ :=
    ByteIndexRange.add_parsed_defined x y a b parsedX parsedY
  refine ⟨raw, ?_⟩
  simpa [coreAdd_eq_model, modelAdd, parsedX, parsedY] using encoded

/-- Core stores arithmetic results in signed 64 bits. Adding two admitted
four-byte ScriptNum operands cannot overflow that representation. -/
theorem parsed_add_fits_int64 (x y : Bytes) (a b : Int)
    (parsedX : ByteIndex.parseScriptNum x = some a)
    (parsedY : ByteIndex.parseScriptNum y = some b) :
    -(2 ^ 63 : Int) ≤ a + b ∧ a + b < 2 ^ 63 := by
  have ha := ByteIndex.parsed_in_int32 x a parsedX
  have hb := ByteIndex.parsed_in_int32 y b parsedY
  omega

/-- A reached numeric opcode with budget remaining has the same byte stack
transition as the source-shaped parse/serialize operation. -/
theorem min_step_source (hashes : Hashes) (x y : Bytes)
    (stack : List Bytes) (outcomes : List Bool) (ops : Nat)
    (budget : ops + 1 ≤ 201) :
    ByteMachine.step hashes .min (State.mk (x :: y :: stack) outcomes ops) =
      (coreMin x y).map
        (fun raw => State.mk (raw :: stack) outcomes (ops + 1)) := by
  have within : ¬ ops + 1 > 201 := by omega
  unfold ByteMachine.step
  simp [within, coreMin_eq_model, modelMin, Option.map]
  cases hx : ByteIndex.parseScriptNum x with
  | none => simp
  | some a =>
      cases hy : ByteIndex.parseScriptNum y with
      | none => simp
      | some b =>
          cases hz : ByteIndex.encodeScriptNum (min a b) <;>
            simp [hz]

theorem add_step_source (hashes : Hashes) (x y : Bytes)
    (stack : List Bytes) (outcomes : List Bool) (ops : Nat)
    (budget : ops + 1 ≤ 201) :
    ByteMachine.step hashes .add (State.mk (x :: y :: stack) outcomes ops) =
      (coreAdd x y).map
        (fun raw => State.mk (raw :: stack) outcomes (ops + 1)) := by
  have within : ¬ ops + 1 > 201 := by omega
  unfold ByteMachine.step
  simp [within, coreAdd_eq_model, modelAdd, Option.map]
  cases hx : ByteIndex.parseScriptNum x with
  | none => simp
  | some a =>
      cases hy : ByteIndex.parseScriptNum y with
      | none => simp
      | some b =>
          cases hz : ByteIndex.encodeScriptNum (a + b) <;>
            simp [hz]

theorem coreMin_eq_model_of_result_small (x y : Bytes) (a b : Int)
    (parsedX : ByteIndex.parseScriptNum x = some a)
    (parsedY : ByteIndex.parseScriptNum y = some b)
    (lower : -(1023 : Int) ≤ min a b)
    (upper : min a b ≤ 1023) :
    coreMin x y = modelMin x y := by
  simp [coreMin, modelMin, CoreScriptNum.coreSetVch_eq_parseScriptNum,
    parsedX, parsedY, CoreSerialize.coreSerialize_eq_model_small _ lower upper]

theorem coreAdd_eq_model_of_result_small (x y : Bytes) (a b : Int)
    (parsedX : ByteIndex.parseScriptNum x = some a)
    (parsedY : ByteIndex.parseScriptNum y = some b)
    (lower : -(1023 : Int) ≤ a + b)
    (upper : a + b ≤ 1023) :
    coreAdd x y = modelAdd x y := by
  simp [coreAdd, modelAdd, CoreScriptNum.coreSetVch_eq_parseScriptNum,
    parsedX, parsedY, CoreSerialize.coreSerialize_eq_model_small _ lower upper]

/-- The generated first `OP_MIN` cap is 152. Every nonnegative parsed input,
including a nonminimal byte encoding or an overshoot, therefore has a bounded
serialized result on which the Core-shaped and byte-model paths agree. -/
theorem first_min_nonnegative_eq_model (raw : Bytes) (value : Int)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (nonnegative : 0 ≤ value) :
    coreMin [0x98, 0x00] raw = modelMin [0x98, 0x00] raw := by
  apply coreMin_eq_model_of_result_small
    [0x98, 0x00] raw 152 value ByteIndex.positive_152 parsed
  · omega
  · omega

/-- Once `OP_MIN` retains a value from 0 through 152, adding the generated
constant 151 also stays inside the all-proved serializer interval. -/
theorem first_add_capped_eq_model (raw : Bytes) (value : Int)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (lower : 0 ≤ value) (upper : value ≤ 152) :
    coreAdd [0x97, 0x00] raw = modelAdd [0x97, 0x00] raw := by
  apply coreAdd_eq_model_of_result_small
    [0x97, 0x00] raw 151 value FirstOvershoot.parse_151 parsed
  · omega
  · omega

/-- The two exact source-shaped bytes in an in-range first signed lookup
agree with the byte-model canonical index and roll-offset bytes. -/
theorem inrange_first_min_bytes (raw : Bytes) (n : Fin 152)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n.val)) :
    coreMin [0x98, 0x00] raw =
      some (FirstNumericRange.canonicalIndex n) := by
  have hn : n.val < 152 := n.isLt
  have hupper : Int.ofNat n.val ≤ 151 := by
    change (n.val : Int) ≤ 151
    exact_mod_cast (show n.val ≤ 151 by omega)
  have hmin : min (152 : Int) (Int.ofNat n.val) =
      Int.ofNat n.val := by omega
  rw [first_min_nonnegative_eq_model raw (Int.ofNat n.val) parsed
    (by simp)]
  simpa [modelMin, ByteIndex.positive_152, parsed, hmin] using
    FirstNumericRange.encode_canonical_index n

theorem inrange_first_add_bytes (n : Fin 152) :
    coreAdd [0x97, 0x00] (FirstNumericRange.canonicalIndex n) =
      some (FirstNumericRange.signedOffset n) := by
  have hn : n.val < 152 := n.isLt
  have hupper : Int.ofNat n.val ≤ 151 := by
    change (n.val : Int) ≤ 151
    exact_mod_cast (show n.val ≤ 151 by omega)
  rw [first_add_capped_eq_model
    (FirstNumericRange.canonicalIndex n) (Int.ofNat n.val)
    (FirstNumericRange.parse_canonical_index n)
    (by simp) (by omega)]
  have hsum : (151 : Int) + Int.ofNat n.val =
      Int.ofNat (151 + n.val) := by norm_cast
  simpa [modelAdd, FirstOvershoot.parse_151,
    FirstNumericRange.parse_canonical_index, hsum] using
    FirstNumericRange.encode_signed_offset n

end QSB.CoreNumericOps
