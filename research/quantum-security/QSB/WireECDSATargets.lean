import QSB.DynamicDisclosureEvent
import QSB.RecoveryCandidates
import QSB.WireIntegers

/-!
A byte-level constructor for the fixed-signature ECDSA target contract.
The conditional verifier premise says that every successful 32-byte Core
digest has one of at most four admitted message residues modulo the secp256k1
order. The result converts those residues to at most eight actual digest byte
strings. It does not prove that compiled Core satisfies the verifier premise.
-/
namespace QSB.WireECDSATargets
open ByteMachine

/-- The remaining Core/secp256k1 refinement obligation for one fixed
signature and encoded public key. `readBE` interprets the 32 bytes passed to
the scalar parser in their in-memory order; that byte-order correspondence
still needs to be checked against the compiled transaction checker. -/
structure FourResidueVerifier
    (ecdsa : Bytes → Bytes → Bytes → Bool) where
  residues : Bytes → Bytes → Finset Nat
  card_le_four : ∀ sig key, (residues sig key).card ≤ 4
  sound : ∀ sig key digest, ecdsa sig key digest = true →
    digest.length = 32 ∧
    WireIntegers.readBE digest %
      RecoveryCandidates.secpGroupOrder ∈ residues sig key

def targets
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    (contract : FourResidueVerifier ecdsa)
    (sig key : Bytes) : Finset Bytes :=
  (RecoveryCandidates.digestTargets
    RecoveryCandidates.secpGroupOrder (2 ^ 256)
    (contract.residues sig key)).image (WireIntegers.beBytes 32)

theorem targets_card_le_eight
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    (contract : FourResidueVerifier ecdsa)
    (sig key : Bytes) :
    (targets contract sig key).card ≤ 8 := by
  have imageBound :
      ((RecoveryCandidates.digestTargets
        RecoveryCandidates.secpGroupOrder (2 ^ 256)
        (contract.residues sig key)).image
          (WireIntegers.beBytes 32)).card ≤
      (RecoveryCandidates.digestTargets
        RecoveryCandidates.secpGroupOrder (2 ^ 256)
        (contract.residues sig key)).card := Finset.card_image_le
  have numericBound := RecoveryCandidates.digestTargets_card_le_twice
    RecoveryCandidates.secpGroupOrder (2 ^ 256)
    (contract.residues sig key)
  have residueBound := contract.card_le_four sig key
  unfold targets
  omega

theorem checked_digest_mem_targets
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    (contract : FourResidueVerifier ecdsa)
    (sig key digest : Bytes)
    (checked : ecdsa sig key digest = true) :
    digest ∈ targets contract sig key := by
  obtain ⟨length, residue⟩ := contract.sound sig key digest checked
  have wire : WireIntegers.readBE digest < 2 ^ 256 := by
    simpa [length] using WireIntegers.readBE_lt digest
  have numberIn : WireIntegers.readBE digest ∈
      RecoveryCandidates.digestTargets
        RecoveryCandidates.secpGroupOrder (2 ^ 256)
        (contract.residues sig key) := by
    unfold RecoveryCandidates.digestTargets
    apply Finset.mem_biUnion.mpr
    exact ⟨WireIntegers.readBE digest %
      RecoveryCandidates.secpGroupOrder, residue,
      RecoveryCandidates.secp_digest_in_candidates wire rfl⟩
  unfold targets
  apply Finset.mem_image.mpr
  exact ⟨WireIntegers.readBE digest, numberIn,
    WireIntegers.beBytes_readBE digest 32 length⟩

/-- A four-residue verifier contract is sufficient for the eight-wire-target
contract used by the unauthorized-spend source reduction. This does not
manufacture the Core verifier premise or a quantum search bound. -/
def toECDSATargets
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    (contract : FourResidueVerifier ecdsa) :
    DynamicDisclosureEvent.ECDSATargets ecdsa where
  targets := targets contract
  sound := checked_digest_mem_targets contract
  card_le_eight := targets_card_le_eight contract

/-- A more structural route to the four-residue premise: for each parsed
signature/key, provide the admitted recovery points and the exact Core
verification-to-recovery equation. The point fiber and admissibility
conditions are the same ones used by `RecoveryCandidates` to prove the
four-point count. Compiled Core's parser and curve implementation still have
to be shown to satisfy these fields. -/
structure RecoveryVerifier
    (F G : Type*) [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (ecdsa : Bytes → Bytes → Bytes → Bool) where
  r : Bytes → Bytes → F
  s : Bytes → Bytes → F
  keyPoint : Bytes → Bytes → G
  points : Bytes → Bytes → Finset G
  xCoord : G → Nat
  rNat : Bytes → Bytes → Nat
  residueOf : G → Nat
  admissible : ∀ sig key, ∀ R ∈ points sig key,
    xCoord R < RecoveryCandidates.secpFieldPrime ∧
    xCoord R % RecoveryCandidates.secpGroupOrder = rNat sig key
  fiber : ∀ sig key x,
    ((points sig key).filter (fun R => xCoord R = x)).card ≤ 2
  sound : ∀ sig key digest, ecdsa sig key digest = true →
    digest.length = 32 ∧
    ∃ target ∈ QSB.messageTargets (r sig key) (s sig key)
        (keyPoint sig key) (points sig key),
      WireIntegers.readBE digest %
        RecoveryCandidates.secpGroupOrder = residueOf target

def recoveryToFourResidues
    {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq G]
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    (contract : RecoveryVerifier F G ecdsa) :
    FourResidueVerifier ecdsa where
  residues := fun sig key =>
    (QSB.messageTargets (contract.r sig key) (contract.s sig key)
      (contract.keyPoint sig key) (contract.points sig key)).image
      contract.residueOf
  card_le_four := by
    intro sig key
    have imageBound :
        ((QSB.messageTargets (contract.r sig key) (contract.s sig key)
          (contract.keyPoint sig key) (contract.points sig key)).image
            contract.residueOf).card ≤
        (QSB.messageTargets (contract.r sig key) (contract.s sig key)
          (contract.keyPoint sig key) (contract.points sig key)).card :=
      Finset.card_image_le
    exact imageBound.trans
      (RecoveryCandidates.secp_messageTargets_card_le_four
        (contract.r sig key) (contract.s sig key)
        (contract.keyPoint sig key) (contract.points sig key)
        contract.xCoord (contract.rNat sig key)
        (contract.admissible sig key) (contract.fiber sig key))
  sound := by
    intro sig key digest checked
    obtain ⟨length, target, admitted, reduction⟩ :=
      contract.sound sig key digest checked
    exact ⟨length, Finset.mem_image.mpr
      ⟨target, admitted, reduction.symm⟩⟩

def recoveryToECDSATargets
    {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq G]
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    (contract : RecoveryVerifier F G ecdsa) :
    DynamicDisclosureEvent.ECDSATargets ecdsa :=
  toECDSATargets (recoveryToFourResidues contract)

end QSB.WireECDSATargets
