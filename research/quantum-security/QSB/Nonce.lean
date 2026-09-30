import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Module.Basic

/-!
Scalar equation underlying a fixed ECDSA signature and a chosen recovery point.
There is no discrete-log hardness assumption. A production EC verification can
have several recovery points (r or r+N, either parity). This lemma fixes ONE
such point/scalar; it does not assert global uniqueness across recovery choices.
Instantiating it with secp256k1, its byte parsing, and reduction modulo N remains
a separate refinement obligation.
-/
namespace QSB
variable {F : Type*} [Field F]

def NonceEquation (r s k z x : F) : Prop := s * k = z + r * x

/-- Knowing the nonce scalar suffices to calculate the candidate public-key
scalar. The production fixed nonce scalars are public constants. -/
theorem public_scalar_satisfies (r s k z : F) (hr : r ≠ 0) :
    NonceEquation r s k z ((s * k - z) / r) := by
  unfold NonceEquation
  field_simp
  ring

theorem fixed_recovery_point_message_unique {r s k z₁ z₂ x : F}
    (h₁ : NonceEquation r s k z₁ x) (h₂ : NonceEquation r s k z₂ x) :
    z₁ = z₂ := by
  unfold NonceEquation at h₁ h₂
  exact add_right_cancel (h₁.symm.trans h₂)

theorem fixed_message_key_unique {r s k z x₁ x₂ : F} (hr : r ≠ 0)
    (h₁ : NonceEquation r s k z x₁) (h₂ : NonceEquation r s k z x₂) :
    x₁ = x₂ := by
  unfold NonceEquation at h₁ h₂
  exact mul_left_cancel₀ hr (add_left_cancel (h₁.symm.trans h₂))

/-- For two fixed signatures and fixed recovery nonce scalars, sharing the
same key scalar forces equality of their publicly computable recovered-key
expressions. The actual secp256k1 system has several recovery-point choices
and byte encodings; each must be treated separately. -/
theorem common_key_requires_equal_recoveries
    {r₁ s₁ k₁ z₁ r₂ s₂ k₂ z₂ x : F}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (pin : NonceEquation r₁ s₁ k₁ z₁ x)
    (round : NonceEquation r₂ s₂ k₂ z₂ x) :
    (s₁ * k₁ - z₁) / r₁ = (s₂ * k₂ - z₂) / r₂ := by
  have hp := public_scalar_satisfies r₁ s₁ k₁ z₁ hr₁
  have hr := public_scalar_satisfies r₂ s₂ k₂ z₂ hr₂
  exact (fixed_message_key_unique hr₁ hp pin).trans
    (fixed_message_key_unique hr₂ hr round).symm

/-- Conversely, equality of the recovered scalars supplies a common key in
this field model. This is an algebraic search condition, not a probability
bound for correlated Bitcoin sighashes. -/
theorem equal_recoveries_give_common_key
    {r₁ s₁ k₁ z₁ r₂ s₂ k₂ z₂ : F}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (equal : (s₁ * k₁ - z₁) / r₁ = (s₂ * k₂ - z₂) / r₂) :
    ∃ x, NonceEquation r₁ s₁ k₁ z₁ x ∧
      NonceEquation r₂ s₂ k₂ z₂ x := by
  refine ⟨(s₁ * k₁ - z₁) / r₁, public_scalar_satisfies r₁ s₁ k₁ z₁ hr₁, ?_⟩
  rw [equal]
  exact public_scalar_satisfies r₂ s₂ k₂ z₂ hr₂

/-!
For a fixed ECDSA signature (r,s), a publicly known recovery point R, and
ANY new message point Z, the verification equation has a computable public key
Q. The equation itself is only algebra; the real parser, r-to-point recovery,
mod-N scalar conversion and Bitcoin sighash remain separate obligations.
-/
variable {G : Type*} [AddCommGroup G] [Module F G]

def RecoveryEquation (r s : F) (R Z Q : G) : Prop :=
  s • R = Z + r • Q

theorem public_recovery_for_any_message (r s : F) (R Z : G) (hr : r ≠ 0) :
    RecoveryEquation r s R Z (r⁻¹ • (s • R - Z)) := by
  unfold RecoveryEquation
  rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  exact (sub_add_cancel (s • R) Z).symm.trans (add_comm _ _)

end QSB
