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
