import QSB.Nonce
import Mathlib.Tactic

/-!
An arithmetic interface for the number of ECDSA recovery points. The curve
fiber bound remains an explicit premise: this module does not formalize the
secp256k1 curve, its parser, or Bitcoin's hash-to-scalar rule.
-/
namespace QSB.RecoveryCandidates

def secpFieldPrime : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def secpGroupOrder : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

theorem secp_prime_lt_twice_order : secpFieldPrime < 2 * secpGroupOrder := by
  decide

theorem x_coordinate_candidates {p n r x : Nat}
    (positive : 0 < n) (primeBound : p ≤ 2 * n)
    (inField : x < p) (residue : x % n = r) :
    x = r ∨ x = r + n := by
  have below : x < 2 * n := lt_of_lt_of_le inField primeBound
  have quotient : x / n < 2 := (Nat.div_lt_iff_lt_mul positive).mpr (by simpa using below)
  have decompose : x = x % n + n * (x / n) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div x n).symm
  have cases : x / n = 0 ∨ x / n = 1 := by
    have nonnegative : 0 ≤ x / n := Nat.zero_le _
    omega
  rcases cases with h | h
  · left
    simpa [h, residue] using decompose
  · right
    simpa [h, residue, Nat.add_comm] using decompose

variable {P : Type*} [DecidableEq P]

/-- If each admissible x-coordinate has at most two recovery points, and
the field prime is at most twice the group order, a fixed ECDSA r
has at most four admissible points. The fiber hypothesis is where the curve
equation and point-parser proof must enter. -/
theorem recovery_points_card_le_four
    (points : Finset P) (xCoord : P → Nat) (p n r : Nat)
    (positive : 0 < n) (primeBound : p ≤ 2 * n)
    (admissible : ∀ R ∈ points,
      xCoord R < p ∧ xCoord R % n = r)
    (fiber : ∀ x, (points.filter (fun R => xCoord R = x)).card ≤ 2) :
    points.card ≤ 4 := by
  let first := points.filter (fun R => xCoord R = r)
  let second := points.filter (fun R => xCoord R = r + n)
  have cover : points = first ∪ second := by
    apply Finset.ext
    intro R
    constructor
    · intro h
      obtain ⟨inField, residue⟩ := admissible R h
      rcases x_coordinate_candidates positive primeBound inField residue with hr | hr
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨h, hr⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨h, hr⟩))
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
  rw [cover]
  exact (Finset.card_union_le first second).trans (by
    have h1 := fiber r
    have h2 := fiber (r + n)
    dsimp [first, second]
    omega)

/-- The secp256k1 numeric inequality discharges the generic modulus-range
premise. The curve/parsing fiber bound and admissibility remain explicit. -/
theorem secp_recovery_points_card_le_four
    (points : Finset P) (xCoord : P → Nat) (r : Nat)
    (admissible : ∀ R ∈ points,
      xCoord R < secpFieldPrime ∧ xCoord R % secpGroupOrder = r)
    (fiber : ∀ x, (points.filter (fun R => xCoord R = x)).card ≤ 2) :
    points.card ≤ 4 := by
  exact recovery_points_card_le_four points xCoord secpFieldPrime
    secpGroupOrder r (by decide)
    (Nat.le_of_lt secp_prime_lt_twice_order) admissible fiber

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G]

/-- At most four group-element message targets for one signature/key, under
the explicit recovery-point admissibility and two-points-per-x premises.
No SHA256d quantum preimage or Core ECDSA parser theorem is implied. -/
theorem secp_messageTargets_card_le_four
    (r s : F) (Q : G) (points : Finset G)
    (xCoord : G → Nat) (rNat : Nat)
    (admissible : ∀ R ∈ points,
      xCoord R < secpFieldPrime ∧ xCoord R % secpGroupOrder = rNat)
    (fiber : ∀ x, (points.filter (fun R => xCoord R = x)).card ≤ 2) :
    (QSB.messageTargets r s Q points).card ≤ 4 :=
  (QSB.messageTargets_card_le r s Q points).trans
    (secp_recovery_points_card_le_four points xCoord rNat admissible fiber)

end QSB.RecoveryCandidates
