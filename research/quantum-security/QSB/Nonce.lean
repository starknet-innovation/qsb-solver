import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Finset.Card

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

/-- Negating ECDSA's S scalar negates the matching recovery point. Bitcoin
Core normalizes high-S signatures before calling libsecp256k1; retaining the
original DER scalar in a target-set argument is sound only if both signs of
an admissible recovery point are included. This is the algebraic step, not a
proof of Core's parser or normalization behavior. -/
theorem recovery_negate_s_point (r s : F) (R Z Q : G) :
    RecoveryEquation r (-s) R Z Q ↔
      RecoveryEquation r s (-R) Z Q := by
  simp [RecoveryEquation, neg_smul, smul_neg]

theorem public_recovery_for_any_message (r s : F) (R Z : G) (hr : r ≠ 0) :
    RecoveryEquation r s R Z (r⁻¹ • (s • R - Z)) := by
  unfold RecoveryEquation
  rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  exact (sub_add_cancel (s • R) Z).symm.trans (add_comm _ _)

/-- For a fixed public key and one ECDSA recovery point, the message group
element is uniquely determined. A different admissible recovery point may
produce a different message even when the signature and key are unchanged. -/
def messageForPoint (r s : F) (R Q : G) : G :=
  s • R - r • Q

theorem recovery_iff_message_for_point (r s : F) (R Z Q : G) :
    RecoveryEquation r s R Z Q ↔ Z = messageForPoint r s R Q := by
  unfold RecoveryEquation messageForPoint
  constructor
  · intro h
    exact (eq_sub_iff_add_eq).mpr h.symm
  · intro h
    rw [h]
    exact (sub_add_cancel (s • R) (r • Q)).symm

/-- A fixed signature and admissible recovery point allow public recovery for
both messages. If the message group elements differ, their recovered keys
must differ. This says nothing about whether either key has an accepted
Bitcoin encoding, or whether a transaction reaches the corresponding Script
check; those are separate Core/refinement obligations. -/
theorem public_recovery_for_changed_message (r s : F) (R Z₁ Z₂ : G)
    (hr : r ≠ 0) :
    ∃ Q₁ Q₂ : G,
      RecoveryEquation r s R Z₁ Q₁ ∧
      RecoveryEquation r s R Z₂ Q₂ ∧
      (Z₁ ≠ Z₂ → Q₁ ≠ Q₂) := by
  let Q₁ : G := r⁻¹ • (s • R - Z₁)
  let Q₂ : G := r⁻¹ • (s • R - Z₂)
  have first : RecoveryEquation r s R Z₁ Q₁ := by
    dsimp [Q₁]
    exact public_recovery_for_any_message r s R Z₁ hr
  have second : RecoveryEquation r s R Z₂ Q₂ := by
    dsimp [Q₂]
    exact public_recovery_for_any_message r s R Z₂ hr
  refine ⟨Q₁, Q₂, first, second, ?_⟩
  intro different equal
  apply different
  have firstTarget := (recovery_iff_message_for_point r s R Z₁ Q₁).mp first
  have secondTarget := (recovery_iff_message_for_point r s R Z₂ Q₂).mp second
  exact firstTarget.trans
    ((congrArg (messageForPoint r s R) equal).trans secondTarget.symm)

/-- For one fixed recovery point, the recovered public key is the group
identity only at the single message point `s • R`. This isolates one algebraic
exception; Core key encodings and all other verifier conditions remain
external. -/
theorem recovery_identity_key_iff (r s : F) (R Z : G) :
    RecoveryEquation r s R Z 0 ↔ Z = s • R := by
  simp [RecoveryEquation, eq_comm]

theorem public_recovery_nonidentity_for_new_message (r s : F) (R Z : G)
    (hr : r ≠ 0) (notExceptional : Z ≠ s • R) :
    ∃ Q : G, RecoveryEquation r s R Z Q ∧ Q ≠ 0 := by
  let Q : G := r⁻¹ • (s • R - Z)
  have recovered : RecoveryEquation r s R Z Q := by
    dsimp [Q]
    exact public_recovery_for_any_message r s R Z hr
  refine ⟨Q, recovered, ?_⟩
  intro identity
  have exceptional : Z = s • R :=
    (recovery_identity_key_iff r s R Z).mp (identity ▸ recovered)
  exact notExceptional exceptional

/-- If both `R` and `-R` are admissible for the same signature scalar `r`,
they give two different message targets unless `sR` is 2-torsion. On
secp256k1 a point and its negation share an x-coordinate; admissibility and
the at-most-four-point count require separate curve/parser refinement. -/
theorem opposite_points_distinct_messages (r s : F) (R Q : G)
    (notTwoTorsion : s • R ≠ -(s • R)) :
    messageForPoint r s R Q ≠ messageForPoint r s (-R) Q := by
  intro equal
  unfold messageForPoint at equal
  rw [smul_neg] at equal
  have same : s • R = -(s • R) := by
    have h := congrArg (fun x : G => x + r • Q) equal
    simpa using h
  exact notTwoTorsion same

/-- A finite set of admissible recovery points gives at most that many
message group-element targets for a fixed signature and key. This is the
right target-set interface for a same-key replay analysis; it does not count
the actual secp256k1 recovery points or bound quantum hash queries. -/
def messageTargets [DecidableEq G] (r s : F) (Q : G)
    (points : Finset G) : Finset G :=
  points.image (fun R => messageForPoint r s R Q)

theorem messageTargets_card_le [DecidableEq G] (r s : F) (Q : G)
    (points : Finset G) :
    (messageTargets r s Q points).card ≤ points.card := by
  exact Finset.card_image_le

theorem recovery_in_messageTargets [DecidableEq G] (r s : F) (Q Z R : G)
    (points : Finset G) (present : R ∈ points)
    (verified : RecoveryEquation r s R Z Q) :
    Z ∈ messageTargets r s Q points := by
  rw [(recovery_iff_message_for_point r s R Z Q).mp verified]
  exact Finset.mem_image_of_mem _ present

/-- A verifier that normalizes `s` to `-s` still lands in the target set
defined using the original DER scalar, provided that the admitted recovery
points are closed under negation. Core's parser and that closure are external
obligations for the concrete Bitcoin instantiation. -/
theorem normalized_recovery_in_messageTargets [DecidableEq G]
    (r s : F) (Q Z R : G) (points : Finset G)
    (closed : ∀ T ∈ points, -T ∈ points)
    (present : R ∈ points)
    (verified : RecoveryEquation r (-s) R Z Q) :
    Z ∈ messageTargets r s Q points := by
  exact recovery_in_messageTargets r s Q Z (-R) points
    (closed R present) ((recovery_negate_s_point r s R Z Q).mp verified)

end QSB
