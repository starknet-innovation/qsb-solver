import QSB.ByteIndex

/-!
The modeled numeric serializer is partial outside its five-magnitude-byte
domain. Core's `OP_ADD` and `OP_MIN` start from four-byte `CScriptNum`
operands, whose parsed signed range is small enough that their results never
hit this artificial guard. This closes only the serializer-definedness part
of the numeric opcode refinement; byte-for-byte C++ serialization still needs
the Core-to-Lean bridge.
-/
namespace QSB.ByteIndexRange
open ByteIndex

theorem encode_defined_of_natAbs_lt (value : Int)
    (h : value.natAbs < 256 ^ 5) :
    ∃ raw, encodeScriptNum value = some raw := by
  unfold encodeScriptNum
  have guard : ¬ value.natAbs ≥ 256 ^ 5 := by omega
  simp only [guard, ↓reduceIte]
  split_ifs <;> simp

theorem add_parsed_defined (x y : List UInt8) (a b : Int)
    (hx : parseScriptNum x = some a)
    (hy : parseScriptNum y = some b) :
    ∃ raw, encodeScriptNum (a + b) = some raw := by
  have ha := parsed_in_int32 x a hx
  have hb := parsed_in_int32 y b hy
  have h : (a + b).natAbs < 256 ^ 5 := by omega
  exact encode_defined_of_natAbs_lt (a + b) h

theorem min_parsed_defined (x y : List UInt8) (a b : Int)
    (hx : parseScriptNum x = some a)
    (hy : parseScriptNum y = some b) :
    ∃ raw, encodeScriptNum (min a b) = some raw := by
  have ha := parsed_in_int32 x a hx
  have hb := parsed_in_int32 y b hy
  have h : (min a b).natAbs < 256 ^ 5 := by
    by_cases hab : a ≤ b
    · rw [Int.min_eq_left hab]
      omega
    · rw [Int.min_eq_right (by omega : b ≤ a)]
      omega
  exact encode_defined_of_natAbs_lt (min a b) h

end QSB.ByteIndexRange
