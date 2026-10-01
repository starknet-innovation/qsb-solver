import QSB.ByteIndex
import Mathlib.Data.Nat.Bitwise

/-!
Source-shaped arithmetic for Bitcoin Core v27.2 `CScriptNum::set_vch` after
its four-byte operand-length check, with `fRequireMinimal = false` as in the
pinned adapter's `VERIFY_ALL` flags. Core ORs shifted bytes into an `int64_t`,
tests the final byte's 0x80 bit, and removes that bit with a 64-bit complement
mask. `coreSetVch` transcribes those operations over natural numbers. The
final theorem below proves it equals the existing Lean ScriptNum parser for
every byte list. This is a pure conversion theorem, not a refinement of the C++
interpreter or arbitrary script execution.
-/

namespace QSB.CoreScriptNum

theorem mask64_agree (word bit : Nat)
    (fits : word < 2 ^ (bit + 1))
    (mask_mod : (2 ^ 64 - 1 - 2 ^ bit) % 2 ^ (bit + 1) = 2 ^ bit - 1) :
    word &&& (2 ^ 64 - 1 - 2 ^ bit) = word &&& (2 ^ bit - 1) := by
  have lhs_lt : word &&& (2 ^ 64 - 1 - 2 ^ bit) < 2 ^ (bit + 1) := by
    rw [Nat.and_comm]
    exact Nat.and_lt_two_pow _ fits
  have eqmod := Nat.and_mod_two_pow (a := word)
    (b := 2 ^ 64 - 1 - 2 ^ bit) (n := bit + 1)
  rw [Nat.mod_eq_of_lt lhs_lt, Nat.mod_eq_of_lt fits, mask_mod] at eqmod
  exact eqmod

end QSB.CoreScriptNum

namespace QSB.CoreScriptNum

theorem mask64_7 (word : Nat) (fits : word < 2 ^ 8) :
    word &&& (2 ^ 64 - 1 - 2 ^ 7) = word &&& (2 ^ 7 - 1) :=
  mask64_agree word 7 fits (by decide)

theorem mask64_15 (word : Nat) (fits : word < 2 ^ 16) :
    word &&& (2 ^ 64 - 1 - 2 ^ 15) = word &&& (2 ^ 15 - 1) :=
  mask64_agree word 15 fits (by decide)

theorem mask64_23 (word : Nat) (fits : word < 2 ^ 24) :
    word &&& (2 ^ 64 - 1 - 2 ^ 23) = word &&& (2 ^ 23 - 1) :=
  mask64_agree word 23 fits (by decide)

theorem mask64_31 (word : Nat) (fits : word < 2 ^ 32) :
    word &&& (2 ^ 64 - 1 - 2 ^ 31) = word &&& (2 ^ 31 - 1) :=
  mask64_agree word 31 fits (by decide)

end QSB.CoreScriptNum

namespace QSB.CoreScriptNum
open QSB.ByteIndex

def signMask (bytes : List UInt8) : Nat := 128 * 256 ^ (bytes.length - 1)

theorem coreWord_fits_signed64 (bytes : List UInt8)
    (hsize : bytes.length ≤ 4) :
    coreOrWord bytes < 2 ^ 63 := by
  rw [coreOrWord_eq_unsignedLE]
  have hword := unsignedLE_lt_pow bytes
  have hpow : 256 ^ bytes.length ≤ 256 ^ 4 :=
    Nat.pow_le_pow_right (by decide) hsize
  have hmax : 256 ^ 4 < 2 ^ 63 := by decide
  omega

theorem short_mask_agrees (bytes : List UInt8)
    (hsize : bytes.length ≤ 4) :
    coreOrWord bytes &&& (2 ^ 64 - 1 - signMask bytes) =
      coreOrWord bytes &&& (signMask bytes - 1) := by
  have bound : coreOrWord bytes < 256 ^ bytes.length := by
    rw [coreOrWord_eq_unsignedLE]
    exact unsignedLE_lt_pow bytes
  rcases bytes with _ | ⟨a, bytes⟩
  · decide
  rcases bytes with _ | ⟨b, bytes⟩
  · simpa [signMask] using
      mask64_7 (coreOrWord [a]) (by simpa [List.length] using bound)
  rcases bytes with _ | ⟨c, bytes⟩
  · simpa [signMask] using
      mask64_15 (coreOrWord [a, b]) (by simpa [List.length] using bound)
  rcases bytes with _ | ⟨d, bytes⟩
  · simpa [signMask] using
      mask64_23 (coreOrWord [a, b, c]) (by simpa [List.length] using bound)
  rcases bytes with _ | ⟨e, bytes⟩
  · simpa [signMask] using
      mask64_31 (coreOrWord [a, b, c, d]) (by simpa [List.length] using bound)
  simp at hsize

end QSB.CoreScriptNum

namespace QSB.CoreScriptNum

theorem byte_sign_test (b : UInt8) :
    (b.toNat &&& 128 != 0) = decide (b.toNat ≥ 128) := by
  have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
  by_cases h : b.toNat ≥ 128
  · have bit : (b.toNat).testBit 7 = true :=
      Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
        (by omega : 2 ^ 7 ≤ b.toNat) (by omega : b.toNat < 2 ^ (7 + 1))
    have hand : b.toNat &&& 128 = (b.toNat.testBit 7).toNat * 128 := by
      simpa only [show (2 : Nat) ^ 7 = 128 from by decide] using
        Nat.and_two_pow b.toNat 7
    simp [hand, bit, h]
  · have bit : (b.toNat).testBit 7 = false :=
      Nat.testBit_lt_two_pow (by omega : b.toNat < 2 ^ 7)
    have hand : b.toNat &&& 128 = (b.toNat.testBit 7).toNat * 128 := by
      simpa only [show (2 : Nat) ^ 7 = 128 from by decide] using
        Nat.and_two_pow b.toNat 7
    simp [hand, bit, h]

end QSB.CoreScriptNum

namespace QSB.CoreScriptNum
open QSB.ByteIndex

theorem core64_negative_magnitude (bytes : List UInt8)
    (hsize : bytes.length ≤ 4)
    (hneg : (bytes.getLast?.getD 0).toNat ≥ 128) :
    coreOrWord bytes &&& (2 ^ 64 - 1 - signMask bytes) =
      unsignedLE bytes - signMask bytes := by
  rw [short_mask_agrees bytes hsize, coreOrWord_eq_unsignedLE]
  exact negative_sign_mask bytes hsize hneg

def coreSetVch (bytes : List UInt8) : Option Int :=
  if bytes.length > 4 then none
  else
    let word := coreOrWord bytes
    let high := (bytes.getLast?.getD 0).toNat
    if high &&& 128 != 0 then
      some (-Int.ofNat (word &&& (2 ^ 64 - 1 - signMask bytes)))
    else
      some (Int.ofNat word)

theorem coreSetVch_eq_parseScriptNum (bytes : List UInt8) :
    coreSetVch bytes = parseScriptNum bytes := by
  unfold coreSetVch parseScriptNum
  by_cases hsize : bytes.length > 4
  · simp [hsize]
  · have hshort : bytes.length ≤ 4 := by omega
    have sign := byte_sign_test (bytes.getLast?.getD 0)
    by_cases hneg : (bytes.getLast?.getD 0).toNat ≥ 128
    · have masked := core64_negative_magnitude bytes hshort hneg
      have hm : unsignedLE bytes &&&
          (2 ^ 64 - 1 - 128 * 256 ^ (bytes.length - 1)) =
            unsignedLE bytes - 128 * 256 ^ (bytes.length - 1) := by
        simpa [coreOrWord_eq_unsignedLE, signMask] using masked
      simp [hsize, sign, hneg, coreOrWord_eq_unsignedLE, signMask]
      simpa only [show (2 : Nat) ^ 64 - 1 = 18446744073709551615 from by decide]
        using congrArg Int.ofNat hm
    · simp [hsize, sign, hneg, coreOrWord_eq_unsignedLE]

end QSB.CoreScriptNum
