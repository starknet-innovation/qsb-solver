import QSB.DERSyntax
import QSB.CoreScriptNum

/-!
A second source-shaped model of Bitcoin Core v27.2
`IsValidSignatureEncoding` (`src/script/interpreter.cpp` lines 101-173).
It keeps the C++ early-return check order and 0x80 bit tests. A theorem below
relates this model to `DERSyntax.valid` for every byte string. This is not
compiled-C++ refinement or an ECDSA-validity claim.
-/
namespace QSB.CoreDEREncoding
open DERSyntax

def bit80 (sig : Bytes) (i : Nat) : Bool :=
  ((sig[i]?.getD 0).toNat &&& 128) != 0

theorem bit80_eq_ge (sig : Bytes) (i : Nat) :
    bit80 sig i = decide (128 ≤ DERSyntax.byte sig i) := by
  exact CoreScriptNum.byte_sign_test (sig[i]?.getD 0)

def failFast : List Bool → Bool
  | [] => true
  | check :: rest => if check then failFast rest else false

theorem failFast_eq_all (checks : List Bool) :
    failFast checks = checks.all id := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      cases check <;> simp [failFast, ih]

private theorem not_decide_ge_128 (x : Nat) :
    (!decide (128 ≤ x)) = decide (x < 128) := by
  by_cases h : 128 ≤ x
  · have nh : ¬ x < 128 := by omega
    simp [h, nh]
  · have hl : x < 128 := by omega
    simp [h, hl]

private theorem not_decide_gt_one (x : Nat) :
    (!decide (1 < x)) = decide (x ≤ 1) := by
  by_cases h : 1 < x
  · have nh : ¬ x ≤ 1 := by omega
    simp [h, nh]
  · have hl : x ≤ 1 := by omega
    simp [h, hl]

private theorem decide_ge_eq_not_lt (x : Nat) :
    decide (128 ≤ x) = !decide (x < 128) := by
  by_cases h : 128 ≤ x
  · have nh : ¬ x < 128 := by omega
    simp [h, nh]
  · have hl : x < 128 := by omega
    simp [h, hl]

def valid (sig : Bytes) : Bool :=
  let n := sig.length
  let lenR := byte sig 3
  let lenS := byte sig (5 + lenR)
  failFast [
    decide (9 ≤ n),
    decide (n ≤ 73),
    decide (byte sig 0 = 0x30),
    decide (byte sig 1 = n - 3),
    decide (5 + lenR < n),
    decide (lenR + lenS + 7 = n),
    decide (byte sig 2 = 0x02),
    decide (0 < lenR),
    !bit80 sig 4,
    !(decide (1 < lenR) && decide (byte sig 4 = 0) && !bit80 sig 5),
    decide (byte sig (lenR + 4) = 0x02),
    decide (0 < lenS),
    !bit80 sig (lenR + 6),
    !(decide (1 < lenS) && decide (byte sig (lenR + 6) = 0) &&
        !bit80 sig (lenR + 7))]

theorem valid_eq_model (sig : Bytes) :
    valid sig = DERSyntax.valid sig := by
  simp [valid, failFast_eq_all, DERSyntax.valid, bit80_eq_ge,
    Bool.or_assoc, not_decide_ge_128, not_decide_gt_one]
  rw [decide_ge_eq_not_lt (byte sig 5),
    decide_ge_eq_not_lt (byte sig (byte sig 3 + 7))]

/-- Every indexed byte in a successful source-shaped check is in bounds when
Core reaches it. The final lookahead is used only for a multi-byte S. -/
theorem accepted_indices_in_bounds (sig : Bytes) (accepted : valid sig = true) :
    4 < sig.length ∧
    5 + byte sig 3 < sig.length ∧
    byte sig 3 + 6 < sig.length ∧
    (1 < byte sig (5 + byte sig 3) →
      byte sig 3 + 7 < sig.length) := by
  rw [valid_eq_model] at accepted
  unfold DERSyntax.valid at accepted
  simp only [decide_eq_true_eq] at accepted
  obtain ⟨sizeMin, _, _, _, lenSInBounds, total, _, _, _, _, _, lenSPos, _, _⟩ :=
    accepted
  constructor
  · omega
  constructor
  · exact lenSInBounds
  constructor
  · omega
  · intro lenSMore
    omega

end QSB.CoreDEREncoding
