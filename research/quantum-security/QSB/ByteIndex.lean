import QSB.Bonus

/-!
A byte-level ScriptNum candidate for QSB's index opcodes. Bitcoin Core v27.2
`CScriptNum::set_vch` interprets at most four little-endian bytes, with the top
bit of the last byte as the sign. The pinned `bitcoinconsensus` VERIFY_ALL flag
set does not enable MINIMALDATA, so nonminimal encodings and negative zero are
not rejected solely by ScriptNum parsing.

This Lean function mirrors that source-level rule. Its equivalence to the
compiled Core interpreter for *every* byte string is still a refinement
obligation; the native boundary cases are recorded separately. In particular,
this file does not turn the canonical stack-region theorem into an
arbitrary-witness extraction theorem.
-/
namespace QSB.ByteIndex
open StackMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def unsignedLE (bytes : List UInt8) : Nat :=
  ((List.range bytes.length).map
    (fun i => (bytes[i]?.getD 0).toNat * 256 ^ i)).sum

def parseScriptNum (bytes : List UInt8) : Option Int :=
  if bytes.length > 4 then none
  else
    let high := (bytes.getLast?.getD 0).toNat
    let negative := high ≥ 128
    let magnitude := unsignedLE bytes -
      (if negative then 128 * 256 ^ (bytes.length - 1) else 0)
    some (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)

/-- Ordinary QSB arithmetic starts from four-byte ScriptNum operands and only
adds small lock constants, so five magnitude bytes suffice for its results.
The explicit size guard prevents silent truncation outside that scope. -/
def encodeScriptNum (value : Int) : Option (List UInt8) :=
  let magnitude := value.natAbs
  if magnitude ≥ 256 ^ 5 then none
  else if magnitude = 0 then some []
  else
    let digits := ((List.range 5).map
      (fun i => UInt8.ofNat ((magnitude / 256 ^ i) % 256))).reverse
        |>.dropWhile (· == 0)
        |>.reverse
    let high := (digits.getLast?.getD 0).toNat
    if high ≥ 128 then
      some (digits ++ [if value < 0 then 0x80 else 0x00])
    else if value < 0 then
      some (digits.dropLast ++ [UInt8.ofNat (high + 128)])
    else some digits

/-- The local `OP_MIN; OP_ROLL` suffix applied to a byte-encoded index after
the canonical preceding stack region. It is not the complete Bitcoin Script. -/
def selectEncoded (bytes : List UInt8) : Option Cell := do
  let n ← parseScriptNum bytes
  Bonus.selectFromRegion n

theorem empty_is_zero : parseScriptNum [] = some 0 := by decide
theorem negative_zero_is_zero : parseScriptNum [0x80] = some 0 := by decide
theorem nonminimal_ten : parseScriptNum [0x0a, 0x00] = some 10 := by decide
theorem positive_152 : parseScriptNum [0x98, 0x00] = some 152 := by decide
theorem nonminimal_positive_152 :
    parseScriptNum [0x98, 0x00, 0x00] = some 152 := by decide
theorem negative_152 : parseScriptNum [0x98, 0x80] = some (-152) := by decide
theorem five_bytes_rejected :
    parseScriptNum [0x98, 0x00, 0x00, 0x00, 0x00] = none := by decide
theorem encode_zero : encodeScriptNum 0 = some [] := by decide
theorem encode_ten : encodeScriptNum 10 = some [0x0a] := by decide
theorem encode_positive_152 :
    encodeScriptNum 152 = some [0x98, 0x00] := by decide
theorem encode_negative_152 :
    encodeScriptNum (-152) = some [0x98, 0x80] := by decide
theorem encode_zero_roundtrip :
    (encodeScriptNum 0).bind parseScriptNum = some 0 := by decide
theorem encode_152_roundtrip :
    (encodeScriptNum 152).bind parseScriptNum = some 152 := by decide

theorem nonminimal_ten_selects_dummy :
    selectEncoded [0x0a, 0x00] = some (.atom 1158) := by decide
theorem nonminimal_152_selects_commitment :
    selectEncoded [0x98, 0x00, 0x00] =
      some (.hash160 (.atom 157)) := by decide
theorem negative_152_cannot_roll :
    selectEncoded [0x98, 0x80] = none := by decide
theorem oversized_encoding_cannot_roll :
    selectEncoded [0x98, 0x00, 0x00, 0x00, 0x00] = none := by decide

end QSB.ByteIndex
