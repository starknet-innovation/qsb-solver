import QSB.DynamicJointTransaction
import QSB.DynamicScriptLimits

/-!
Separate a fresh hash-to-DER key from a reused key whose fixed ALL signature
is checked on a new transaction preimage. The two branches share the same H;
there is no independence or quantum-query assertion here. Approved preimages
range over every valid release in the same ledger context, including releases
chosen adaptively before the attempted spend.
-/
namespace QSB.DynamicDisclosureEvent
open ByteMachine

def approvedAllPreimages
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) : Set Bytes :=
  { preimage | ∃ (released : SighashAllWire.TxFields)
      (selected : Nat) (scriptCode : Bytes),
      SighashAllWire.valid released ∧
      scriptCode.length < 256 ^ 8 ∧
      SighashAllWire.projectionWithLedger ledger released ∈ authorized ∧
      preimage = SighashAllWire.sourceAllPreimage released selected scriptCode }

/-- Source-shaped ALL binding excludes every owner-approved release preimage,
regardless of which selected input or scriptCode that release used. -/
theorem forbidden_all_preimage_fresh
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes)
    (attemptedValid : SighashAllWire.valid attempted)
    (scriptCodeValid : scriptCode.length < 256 ^ 8)
    (forbidden : SighashAllWire.projectionWithLedger ledger attempted ∉
      authorized) :
    SighashAllWire.sourceAllPreimage attempted selected scriptCode ∉
      approvedAllPreimages ledger authorized := by
  intro present
  obtain ⟨released, releasedSelected, releasedScript,
    releasedValid, releasedScriptValid, approved, same⟩ := present
  exact SighashAllWire.unauthorized_sourceAll_distinct_preimage
    ledger authorized releasedSelected selected releasedScript scriptCode
    releasedValid attemptedValid releasedScriptValid scriptCodeValid
    approved forbidden same

/-- Either a checked pin/final key is outside the freely disclosed key set
and has a DER-shaped H output, or both keys are in that set and both fixed
ALL signatures verify on preimages outside the owner-approved release set.
The equal-key case is included. The key set may depend on the adaptive honest
transcript; a QROM bound must account for that dependence and a single shared
query budget. -/
theorem search_fresh_key_or_known_all_retarget
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final))
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (knownKeys : Set Bytes)
    (txValid : SighashAllWire.valid tx)
    (forbidden : SighashAllWire.projectionWithLedger ledger tx ∉
      authorized) :
    ∃ (pinKey finalKey : Bytes)
      (beforePin beforeCheck : CoreOpcodeStep.State),
      DynamicJointTransaction.reachedPinKey beforePin = pinKey ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some finalKey ∧
      (let pinPreimage := SighashAllWire.sourceAllPreimage tx selected
          (DynamicJointTransaction.reachedPinScriptCode lock beforePin)
       let finalPreimage := SighashAllWire.sourceAllPreimage tx selected
          (CoreMultisigSourceScan.deletedScript
            (DynamicCheckedCertificate.wire lock)
            beforeCheck.stack.reverse 10 10)
       (pinKey ∉ knownKeys ∧
          DERSyntax.valid (functions.H pinKey) = true) ∨
       (finalKey ∉ knownKeys ∧
          DERSyntax.valid (functions.H finalKey) = true) ∨
       (pinKey ∈ knownKeys ∧ finalKey ∈ knownKeys ∧
          pinPreimage ∉ approvedAllPreimages ledger authorized ∧
          finalPreimage ∉ approvedAllPreimages ledger authorized ∧
          ecdsa lock.pin.dropLast pinKey
            (functions.H (functions.H pinPreimage)) = true ∧
          ecdsa lock.nonce1.dropLast finalKey
            (functions.H (functions.H finalPreimage)) = true)) := by
  obtain ⟨pinKey, finalKey, beforePin, beforeCheck,
    _pinReached, _finalReached, _pinSig, pinKeyAt, _nonceSig,
    finalKeyAt, pinDER, finalDER, _input, pinVerified, finalVerified⟩ :=
    DynamicJointTransaction.search_two_key_joint_hit functions tx selected
      lock secondWidth stack validKey ecdsa firstRound final found
      pinAll nonceAll
  have wireBound : (DynamicCheckedCertificate.wire lock).length <
      256 ^ 8 := by
    have h := (DynamicScriptLimits.full_wire_below_core_limit
      lock.pin lock.nonce0 lock.nonce1
      lock.firstCommitment lock.secondCommitment
      firstWidth secondWidth pinShort nonce0Short nonce1Short).2
    change (DynamicCheckedCertificate.wire lock).length < 10000 at h
    exact lt_trans h (by decide)
  have pinCodeBound :
      (DynamicJointTransaction.reachedPinScriptCode lock beforePin).length <
        256 ^ 8 := by
    apply lt_of_le_of_lt _ wireBound
    simpa [DynamicJointTransaction.reachedPinScriptCode] using
      CoreFindAndDelete.run_length_le 880
        (DynamicCheckedCertificate.wire lock)
        (CorePushSerialize.pushPattern
          (DynamicJointTransaction.reachedPinSignature beforePin))
  have finalCodeBound :
      (CoreMultisigSourceScan.deletedScript
        (DynamicCheckedCertificate.wire lock)
        beforeCheck.stack.reverse 10 10).length < 256 ^ 8 := by
    apply lt_of_le_of_lt _ wireBound
    simpa [CoreMultisigSourceScan.deletedScript] using
      CoreFindAndDelete.runMany_length_le 880
        (DynamicCheckedCertificate.wire lock)
        ((CoreMultisigSourceScan.reachedSignatures
          beforeCheck.stack.reverse 10 10).map
          CorePushSerialize.pushPattern)
  have pinFresh := forbidden_all_preimage_fresh ledger authorized
    tx selected (DynamicJointTransaction.reachedPinScriptCode lock beforePin)
    txValid pinCodeBound forbidden
  have finalFresh := forbidden_all_preimage_fresh ledger authorized
    tx selected
    (CoreMultisigSourceScan.deletedScript
      (DynamicCheckedCertificate.wire lock)
      beforeCheck.stack.reverse 10 10)
    txValid finalCodeBound forbidden
  refine ⟨pinKey, finalKey, beforePin, beforeCheck, pinKeyAt,
    finalKeyAt, ?_⟩
  dsimp
  by_cases pinKnown : pinKey ∈ knownKeys
  · by_cases finalKnown : finalKey ∈ knownKeys
    · exact Or.inr (Or.inr ⟨pinKnown, finalKnown, pinFresh,
        finalFresh, pinVerified, finalVerified⟩)
    · exact Or.inr (Or.inl ⟨finalKnown, finalDER⟩)
  · exact Or.inl ⟨pinKnown, pinDER⟩

end QSB.DynamicDisclosureEvent
