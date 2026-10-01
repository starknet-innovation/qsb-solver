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

/-- Little-endian byte assembly in Horner form. -/
def unsignedLE : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * unsignedLE rest

theorem unsignedLE_lt_pow (bytes : List UInt8) :
    unsignedLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [unsignedLE]
  | cons b rest ih =>
    simp only [unsignedLE, List.length_cons, Nat.pow_succ]
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    omega

/-- The same assembly using the bytewise OR operations in Core's `set_vch`.
The recursive order is equivalent to inserting successive bytes at offsets
`8*i`: each new byte occupies a disjoint eight-bit lane. -/
def coreOrWord : List UInt8 → Nat
  | [] => 0
  | b :: rest => (coreOrWord rest <<< 8) ||| b.toNat

theorem coreOrWord_eq_unsignedLE (bytes : List UInt8) :
    coreOrWord bytes = unsignedLE bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    simp only [coreOrWord, unsignedLE, ih]
    have hb : b.toNat < 2 ^ 8 := UInt8.toNat_lt b
    rw [← Nat.shiftLeft_add_eq_or_of_lt hb]
    simp [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm]

/-- A source-shaped conversion after Core's four-byte length check. The sign
mask is expressed as subtraction of the highest bit, whose lane is disjoint
from the remaining magnitude bits. This is a pure arithmetic model; it does
not assert that arbitrary script execution reaches this conversion. -/
def coreOrScriptNum (bytes : List UInt8) : Option Int :=
  if bytes.length > 4 then none
  else
    let high := (bytes.getLast?.getD 0).toNat
    let negative := high ≥ 128
    let magnitude := coreOrWord bytes -
      (if negative then 128 * 256 ^ (bytes.length - 1) else 0)
    some (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)

def parseScriptNum (bytes : List UInt8) : Option Int :=
  if bytes.length > 4 then none
  else
    let high := (bytes.getLast?.getD 0).toNat
    let negative := high ≥ 128
    let magnitude := unsignedLE bytes -
      (if negative then 128 * 256 ^ (bytes.length - 1) else 0)
    some (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)

theorem coreOrScriptNum_eq_parseScriptNum (bytes : List UInt8) :
    coreOrScriptNum bytes = parseScriptNum bytes := by
  simp only [coreOrScriptNum, parseScriptNum,
    coreOrWord_eq_unsignedLE]

/-- If a word has exactly its `bit`-th bit as the highest possible set bit,
retaining the lower bits is the same as subtracting that bit. -/
theorem clear_sign_bit_eq_sub (word bit : Nat)
    (set : 2 ^ bit ≤ word)
    (fits : word < 2 ^ (bit + 1)) :
    word &&& (2 ^ bit - 1) = word - 2 ^ bit := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.pow_succ] at fits
  rw [Nat.mod_eq_sub_mod set, Nat.mod_eq_of_lt (by omega)]

/-- For any negative one- through four-byte ScriptNum encoding, the parser's
subtraction removes exactly the top sign bit. The right-hand mask retains
every lower bit of the assembled word. -/
theorem negative_sign_mask (bytes : List UInt8)
    (hsize : bytes.length ≤ 4)
    (hneg : (bytes.getLast?.getD 0).toNat ≥ 128) :
    unsignedLE bytes &&& (128 * 256 ^ (bytes.length - 1) - 1) =
      unsignedLE bytes - 128 * 256 ^ (bytes.length - 1) := by
  rcases bytes with _ | ⟨a, bytes⟩
  · simp at hneg
  rcases bytes with _ | ⟨b, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    simp at hneg
    simpa [unsignedLE] using
      clear_sign_bit_eq_sub (a.toNat) 7 (by omega) (by omega)
  rcases bytes with _ | ⟨c, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    simp at hneg
    simpa [unsignedLE] using
      clear_sign_bit_eq_sub (a.toNat + 256 * b.toNat) 15 (by omega) (by omega)
  rcases bytes with _ | ⟨d, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    have hc : c.toNat < 256 := by simpa using UInt8.toNat_lt c
    simp at hneg
    simpa [unsignedLE] using
      clear_sign_bit_eq_sub (a.toNat + 256 * (b.toNat + 256 * c.toNat))
        23 (by omega) (by omega)
  rcases bytes with _ | ⟨e, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    have hc : c.toNat < 256 := by simpa using UInt8.toNat_lt c
    have hd : d.toNat < 256 := by simpa using UInt8.toNat_lt d
    simp at hneg
    simpa [unsignedLE] using
      clear_sign_bit_eq_sub
        (a.toNat + 256 * (b.toNat + 256 * (c.toNat + 256 * d.toNat)))
        31 (by omega) (by omega)
  simp at hsize

/-- Every successfully parsed four-byte ScriptNum is inside Core's signed
32-bit `getint` interval. In particular, `OP_ROLL` sees the same integer
without saturation. -/
theorem parsed_in_int32 (bytes : List UInt8) (value : Int)
    (parsed : parseScriptNum bytes = some value) :
    -(2147483647 : Int) ≤ value ∧ value ≤ 2147483647 := by
  rcases bytes with _ | ⟨a, bytes⟩
  · simp [parseScriptNum, unsignedLE] at parsed
    omega
  rcases bytes with _ | ⟨b, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    by_cases hb : a.toNat ≥ 128
    · simp [parseScriptNum, unsignedLE, hb] at parsed
      omega
    · simp [parseScriptNum, unsignedLE, hb] at parsed
      omega
  rcases bytes with _ | ⟨c, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    by_cases hc : b.toNat ≥ 128
    · simp [parseScriptNum, unsignedLE, hc] at parsed
      omega
    · simp [parseScriptNum, unsignedLE, hc] at parsed
      omega
  rcases bytes with _ | ⟨d, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    have hc : c.toNat < 256 := by simpa using UInt8.toNat_lt c
    by_cases hd : c.toNat ≥ 128
    · simp [parseScriptNum, unsignedLE, hd] at parsed
      omega
    · simp [parseScriptNum, unsignedLE, hd] at parsed
      omega
  rcases bytes with _ | ⟨e, bytes⟩
  · have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    have hc : c.toNat < 256 := by simpa using UInt8.toNat_lt c
    have hd : d.toNat < 256 := by simpa using UInt8.toNat_lt d
    by_cases he : d.toNat ≥ 128
    · simp [parseScriptNum, unsignedLE, he] at parsed
      omega
    · simp [parseScriptNum, unsignedLE, he] at parsed
      omega
  simp [parseScriptNum] at parsed

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
