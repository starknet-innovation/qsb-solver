import QSB.ByteMachine

/-!
A source-shaped translation of Bitcoin Core v27.2
`script/interpreter.cpp::IsValidSignatureEncoding`. It includes the trailing
sighash byte but imposes no hashtype, low-S, scalar-range, curve, or ECDSA
condition. The byte positions and check order match that function; equality
with the compiled Core library is a separate refinement obligation.
-/
namespace QSB.DERSyntax

abbrev Bytes := ByteMachine.Bytes

def byte (sig : Bytes) (i : Nat) : Nat :=
  (sig[i]?.getD 0).toNat

/-- Strict DER syntax including one trailing sighash byte. The size and length
guards make every position used by a successful result in bounds. -/
def valid (sig : Bytes) : Bool :=
  let n := sig.length
  let lenR := byte sig 3
  let lenS := byte sig (5 + lenR)
  decide (9 ≤ n ∧ n ≤ 73 ∧
    byte sig 0 = 0x30 ∧
    byte sig 1 = n - 3 ∧
    5 + lenR < n ∧
    lenR + lenS + 7 = n ∧
    byte sig 2 = 0x02 ∧
    0 < lenR ∧
    byte sig 4 < 128 ∧
    (lenR ≤ 1 ∨ byte sig 4 ≠ 0 ∨ 128 ≤ byte sig 5) ∧
    byte sig (lenR + 4) = 0x02 ∧
    0 < lenS ∧
    byte sig (lenR + 6) < 128 ∧
    (lenS ≤ 1 ∨ byte sig (lenR + 6) ≠ 0 ∨
      128 ≤ byte sig (lenR + 7)))

/-- Source-shaped `CheckSignatureEncoding` under the pinned adapter's
`VERIFY_ALL` flags: Core permits an empty signature as an invalid-check
placeholder, while a nonempty signature must satisfy strict DER. Actual
ECDSA verification rejects the empty placeholder; this predicate models only
the encoding gate. -/
def verifyAllEncoding (sig : Bytes) : Bool :=
  sig.isEmpty || valid sig

theorem verifyAllEncoding_empty : verifyAllEncoding [] = true := by
  decide

theorem verifyAllEncoding_nonempty (sig : Bytes) (nonempty : sig ≠ []) :
    verifyAllEncoding sig = valid sig := by
  cases sig with
  | nil => exact False.elim (nonempty rfl)
  | cons b rest => simp [verifyAllEncoding]

/-- Every twenty-byte strict DER signature has positive R and S byte lengths
adding to thirteen. The remaining conditions constrain the leading bytes. -/
theorem valid_twenty_byte_lengths (sig : Bytes)
    (width : sig.length = 20) (accepted : valid sig = true) :
    0 < byte sig 3 ∧ 0 < byte sig (5 + byte sig 3) ∧
      byte sig 3 + byte sig (5 + byte sig 3) = 13 := by
  unfold valid at accepted
  simp only [decide_eq_true_eq] at accepted
  obtain ⟨_, _, _, _, _, sum, _, posR, _, _, _, posS, _, _⟩ := accepted
  constructor
  · exact posR
  constructor
  · exact posS
  · rw [width] at sum
    omega

/-- In particular, neither component can consume all thirteen integer bytes. -/
theorem valid_twenty_byte_ranges (sig : Bytes)
    (width : sig.length = 20) (accepted : valid sig = true) :
    1 ≤ byte sig 3 ∧ byte sig 3 ≤ 12 ∧
      1 ≤ byte sig (5 + byte sig 3) ∧
      byte sig (5 + byte sig 3) ≤ 12 := by
  obtain ⟨rPos, sPos, sum⟩ :=
    valid_twenty_byte_lengths sig width accepted
  omega

/-- The six public byte positions that determine the basic twenty-byte DER
shape, before applying leading-integer-byte rules or any ECDSA condition. -/
theorem valid_twenty_byte_header (sig : Bytes)
    (width : sig.length = 20) (accepted : valid sig = true) :
    byte sig 0 = 0x30 ∧
    byte sig 1 = 0x11 ∧
    byte sig 2 = 0x02 ∧
    1 ≤ byte sig 3 ∧ byte sig 3 ≤ 12 ∧
    byte sig (byte sig 3 + 4) = 0x02 ∧
    byte sig (byte sig 3 + 5) = 13 - byte sig 3 := by
  unfold valid at accepted
  simp only [decide_eq_true_eq] at accepted
  obtain ⟨_, _, tag, total, _, sum, rTag, posR, _, _, sTag, posS,
    _, _⟩ := accepted
  have smallR : byte sig 3 ≤ 12 := by
    rw [width] at sum
    omega
  refine ⟨tag, ?_, rTag, by omega, smallR, by simpa [Nat.add_comm] using sTag, ?_⟩
  · rw [width] at total
    simpa using total
  · rw [width] at sum
    simpa [Nat.add_comm] using (show byte sig (5 + byte sig 3) =
      13 - byte sig 3 by omega)

theorem crafted_twenty_byte_signature_valid :
    valid [0x30, 0x11, 0x02, 0x01, 0x01, 0x02, 0x0c, 0x01,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x11, 0x03] = true := by decide

theorem wrong_sequence_length_rejected :
    valid [0x30, 0x10, 0x02, 0x01, 0x01, 0x02, 0x0c, 0x01,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x11, 0x03] = false := by decide

end QSB.DERSyntax
