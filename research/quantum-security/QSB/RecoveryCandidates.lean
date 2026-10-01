import QSB.Nonce
import Mathlib.Tactic

/-!
An arithmetic interface for the number of ECDSA recovery points. The
two-points-per-x fiber bound is derived from a field-valued affine curve
equation and coordinate uniqueness, but mapping Core's accepted recovery
points to those coordinates remains an explicit premise. This module does
not formalize Core's curve parser or Bitcoin's hash-to-scalar rule.
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

/-- Two roots of the same square equation in a field agree up to sign.
This is the algebraic source of the two-affine-points-per-x bound. -/
theorem square_roots_eq_or_neg {K : Type*} [Field K]
    (left right : K) (same : left * left = right * right) :
    left = right ∨ left = -right := by
  have product : (left - right) * (left + right) = 0 := by
    calc
      (left - right) * (left + right) = left * left - right * right := by ring
      _ = 0 := sub_eq_zero.mpr same
  rcases mul_eq_zero.mp product with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- Any collection of affine points satisfying one square equation per x
has at most two points at each x, provided the x/y coordinates uniquely
identify a point. It does not cover an infinity point, Core's point parser,
or the assertion that parsed points satisfy the secp256k1 equation. -/
theorem affine_fiber_card_le_two
    {P K : Type*} [DecidableEq P] [Field K] [DecidableEq K]
    (points : Finset P) (xCoord : P → Nat) (yCoord : P → K)
    (curveRhs : Nat → K)
    (onCurve : ∀ R ∈ points,
      yCoord R * yCoord R = curveRhs (xCoord R))
    (coordinateUnique : ∀ R ∈ points, ∀ S ∈ points,
      xCoord R = xCoord S → yCoord R = yCoord S → R = S)
    (x : Nat) :
    (points.filter (fun R => xCoord R = x)).card ≤ 2 := by
  classical
  let fiber := points.filter (fun R => xCoord R = x)
  by_cases nonempty : fiber.Nonempty
  · obtain ⟨anchor, anchorMem⟩ := nonempty
    let choices : Finset K := {yCoord anchor, -yCoord anchor}
    have anchorData := Finset.mem_filter.mp anchorMem
    have mapsTo : Set.MapsTo yCoord (fiber : Set P) (choices : Set K) := by
      intro R present
      have data := Finset.mem_filter.mp present
      have sameSquare : yCoord R * yCoord R =
          yCoord anchor * yCoord anchor := by
        rw [onCurve R data.1, onCurve anchor anchorData.1,
          data.2, anchorData.2]
      rcases square_roots_eq_or_neg (yCoord R) (yCoord anchor)
          sameSquare with same | opposite
      · simp [choices, same]
      · simp [choices, opposite]
    have injective : (fiber : Set P).InjOn yCoord := by
      intro R rMem S sMem equalY
      have rData := Finset.mem_filter.mp rMem
      have sData := Finset.mem_filter.mp sMem
      exact coordinateUnique R rData.1 S sData.1
        (rData.2.trans sData.2.symm) equalY
    have cardChoices : choices.card ≤ 2 := by
      dsimp [choices]
      simpa using Finset.card_insert_le (yCoord anchor)
        ({-yCoord anchor} : Finset K)
    exact (Finset.card_le_card_of_injOn yCoord mapsTo injective).trans
      cardChoices
  · simp [fiber, Finset.not_nonempty_iff_eq_empty.mp nonempty]

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

/-- Replace the abstract two-points-per-x premise by a field-valued affine
curve equation and coordinate uniqueness. Supplying these facts for Core's
parsed secp256k1 points remains a separate refinement obligation. -/
theorem secp_messageTargets_card_le_four_of_curve
    {K : Type*} [Field K] [DecidableEq K]
    (r s : F) (Q : G) (points : Finset G)
    (xCoord : G → Nat) (yCoord : G → K) (rNat : Nat)
    (admissible : ∀ R ∈ points,
      xCoord R < secpFieldPrime ∧ xCoord R % secpGroupOrder = rNat)
    (onCurve : ∀ R ∈ points,
      yCoord R * yCoord R = (xCoord R : K) ^ 3 + 7)
    (coordinateUnique : ∀ R ∈ points, ∀ S ∈ points,
      xCoord R = xCoord S → yCoord R = yCoord S → R = S) :
    (QSB.messageTargets r s Q points).card ≤ 4 := by
  apply secp_messageTargets_card_le_four r s Q points xCoord rNat admissible
  exact affine_fiber_card_le_two points xCoord yCoord
    (fun x => (x : K) ^ 3 + 7) onCurve coordinateUnique

/-- A 256-bit SHA256d digest, viewed as an unsigned integer, is smaller than
twice the secp256k1 group order. This is a wire-range fact, not a claim about
the distribution of SHA256d or Core's digest-to-scalar conversion. -/
theorem secp_digest_lt_twice_order : 2 ^ 256 < 2 * secpGroupOrder := by
  decide

def digestCandidates (order bound residue : Nat) : Finset Nat :=
  ({residue, residue + order} : Finset Nat).filter (· < bound)

theorem digestCandidates_card_le_two (order bound residue : Nat) :
    (digestCandidates order bound residue).card ≤ 2 := by
  unfold digestCandidates
  have filtered := Finset.card_filter_le
    ({residue, residue + order} : Finset Nat) (· < bound)
  have pair : ({residue, residue + order} : Finset Nat).card ≤ 2 := by
    simpa using Finset.card_insert_le residue ({residue + order} : Finset Nat)
  exact filtered.trans pair

/-- Every 256-bit digest with a specified residue modulo the group order
is one of two unsigned integers. The residue premise is an explicit numeric
bridge to the ECDSA field model. -/
theorem secp_digest_in_candidates {digest residue : Nat}
    (wire : digest < 2 ^ 256)
    (reduction : digest % secpGroupOrder = residue) :
    digest ∈ digestCandidates secpGroupOrder (2 ^ 256) residue := by
  have candidates := x_coordinate_candidates (by decide)
    (Nat.le_of_lt secp_digest_lt_twice_order) wire reduction
  unfold digestCandidates
  apply Finset.mem_filter.mpr
  constructor
  · rcases candidates with same | plus
    · simp [same]
    · simp [plus]
  · exact wire

def digestTargets (order bound : Nat) (residues : Finset Nat) : Finset Nat :=
  residues.biUnion (digestCandidates order bound)

theorem digestTargets_card_le_twice (order bound : Nat)
    (residues : Finset Nat) :
    (digestTargets order bound residues).card ≤ 2 * residues.card := by
  induction residues using Finset.induction_on with
  | empty => simp [digestTargets]
  | @insert residue rest absent ih =>
      have union := Finset.card_union_le
        (digestCandidates order bound residue)
        (digestTargets order bound rest)
      have one := digestCandidates_card_le_two order bound residue
      simp only [digestTargets, Finset.biUnion_insert] at *
      simp only [Finset.card_insert_of_notMem absent]
      omega

/-- At most eight *wire digest values* can reduce to at most four admitted
ECDSA message residues for one fixed signature and key. The curve fiber,
group-to-residue map, Core verifier and actual SHA256d behavior remain
external premises; this theorem is only finite target accounting. -/
theorem secp_digestTargets_card_le_eight
    (r s : F) (Q : G) (points : Finset G)
    (xCoord : G → Nat) (rNat : Nat) (residueOf : G → Nat)
    (admissible : ∀ R ∈ points,
      xCoord R < secpFieldPrime ∧ xCoord R % secpGroupOrder = rNat)
    (fiber : ∀ x, (points.filter (fun R => xCoord R = x)).card ≤ 2) :
    (digestTargets secpGroupOrder (2 ^ 256)
      ((QSB.messageTargets r s Q points).image residueOf)).card ≤ 8 := by
  have messages := secp_messageTargets_card_le_four r s Q points xCoord rNat
    admissible fiber
  have mapped : ((QSB.messageTargets r s Q points).image residueOf).card ≤ 4 :=
    (Finset.card_image_le).trans messages
  exact (digestTargets_card_le_twice secpGroupOrder (2 ^ 256) _).trans (by omega)

theorem secp_digestTargets_card_le_eight_of_curve
    {K : Type*} [Field K] [DecidableEq K]
    (r s : F) (Q : G) (points : Finset G)
    (xCoord : G → Nat) (yCoord : G → K) (rNat : Nat)
    (residueOf : G → Nat)
    (admissible : ∀ R ∈ points,
      xCoord R < secpFieldPrime ∧ xCoord R % secpGroupOrder = rNat)
    (onCurve : ∀ R ∈ points,
      yCoord R * yCoord R = (xCoord R : K) ^ 3 + 7)
    (coordinateUnique : ∀ R ∈ points, ∀ S ∈ points,
      xCoord R = xCoord S → yCoord R = yCoord S → R = S) :
    (digestTargets secpGroupOrder (2 ^ 256)
      ((QSB.messageTargets r s Q points).image residueOf)).card ≤ 8 := by
  apply secp_digestTargets_card_le_eight r s Q points xCoord rNat residueOf
    admissible
  exact affine_fiber_card_le_two points xCoord yCoord
    (fun x => (x : K) ^ 3 + 7) onCurve coordinateUnique

/-- Conditional event bridge: if the verifier's message target is admitted
and its scalar residue is the digest's reduction, then the complete unsigned
wire digest belongs to the corresponding finite target set. The two premises
are precisely where Core ECDSA and digest conversion must be refined. -/
theorem secp_digest_in_targetSet
    (r s : F) (Q : G) (points : Finset G) (residueOf : G → Nat)
    (digest : Nat) (target : G)
    (wire : digest < 2 ^ 256)
    (targetAdmitted : target ∈ QSB.messageTargets r s Q points)
    (reduction : digest % secpGroupOrder = residueOf target) :
    digest ∈ digestTargets secpGroupOrder (2 ^ 256)
      ((QSB.messageTargets r s Q points).image residueOf) := by
  unfold digestTargets
  apply Finset.mem_biUnion.mpr
  exact ⟨residueOf target, Finset.mem_image_of_mem _ targetAdmitted,
    secp_digest_in_candidates wire reduction⟩

end QSB.RecoveryCandidates
