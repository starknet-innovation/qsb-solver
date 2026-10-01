import QSB.CoreCheckedDynamic
import QSB.DynamicJointTransaction

/-!
Compose a checker-derived parameterized Config A run with the transaction-
dependent joint `H`/`R` source certificate.  This removes the separate
certificate-search premise at the source-model boundary.  Bitcoin Core
acceptance, real ECDSA/key parsing, the builder correspondence, and a quantum
query bound are not established here.
-/
namespace QSB.CoreCheckedJointTransaction
open ByteMachine

/-- One truthy checker-derived transaction run forces two strict-DER SHA256
key-puzzle outputs and both fixed ALL signature checks on their respective
reached scriptCodes.  The two keys may be equal and share one `H` oracle. -/
theorem checked_run_two_key_joint_hit
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (final : CoreCheckedStep.State) (records : List Bool)
    (run : CoreCheckedStep.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.wire lock) validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    ∃ (firstRound : Bool) (sourceFinal : CoreOpcodeStep.State)
      (pinKey finalKey : Bytes)
      (beforePin beforeCheck : CoreOpcodeStep.State),
      DynamicCheckedCertificate.search
        (JointSourceChecks.hashes functions) lock stack validKey
        (JointSourceChecks.checker functions tx selected ecdsa) =
          some (firstRound, sourceFinal) ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 2)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforePin ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      DynamicJointTransaction.reachedPinSignature beforePin = lock.pin ∧
      DynamicJointTransaction.reachedPinKey beforePin = pinKey ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some finalKey ∧
      DERSyntax.valid (functions.H pinKey) = true ∧
      DERSyntax.valid (functions.H finalKey) = true ∧
      selected < tx.inputs.length ∧
      ecdsa lock.pin.dropLast pinKey
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (DynamicJointTransaction.reachedPinScriptCode lock beforePin)))) =
        true ∧
      ecdsa lock.nonce1.dropLast finalKey
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨firstRound, sourceFinal, found⟩ :=
    CoreCheckedDynamic.checked_run_search_succeeds
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      final records run accepted
  obtain ⟨pinKey, finalKey, beforePin, beforeCheck,
    pinReached, finalReached, fixedPin, pinKeyAt, nonceSlot,
    finalKeyAt, pinDER, finalDER, inputValid, pinVerified,
    nonceVerified⟩ :=
    DynamicJointTransaction.search_two_key_joint_hit
      functions tx selected lock secondWidth stack validKey ecdsa
      firstRound sourceFinal found pinAll nonceAll
  exact ⟨firstRound, sourceFinal, pinKey, finalKey, beforePin,
    beforeCheck, found, pinReached, finalReached, fixedPin,
    pinKeyAt, nonceSlot, finalKeyAt, pinDER, finalDER,
    inputValid, pinVerified, nonceVerified⟩

/-- On a good setup, the same checker-derived run fixes seven opened
`R(H(opening))` commitments, two other distinct positions, and the final
DER/ALL puzzle.  This is a deterministic joint-oracle event, not its quantum
probability bound. -/
theorem checked_run_good_setup_joint_final_event
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
    (final : CoreCheckedStep.State) (records : List Bool)
    (run : CoreCheckedStep.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.wire lock) validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false)
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    ∃ (firstRound : Bool) (sourceFinal : CoreOpcodeStep.State)
      (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : CoreOpcodeStep.State) (key : Bytes),
      DynamicCheckedCertificate.search
        (JointSourceChecks.hashes functions) lock stack validKey
        (JointSourceChecks.checker functions tx selected ecdsa) =
          some (firstRound, sourceFinal) ∧
      DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions)
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment)
        ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace,
        functions.R (functions.H p.2) = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      DERSyntax.valid (functions.H key) = true ∧
      selected < tx.inputs.length ∧
      ecdsa lock.nonce1.dropLast key
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨firstRound, sourceFinal, found⟩ :=
    CoreCheckedDynamic.checked_run_search_succeeds
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      final records run accepted
  obtain ⟨trace, a, b, beforeCheck, key, extracted, seven,
    hits, distinct, count, reached, der, inputValid, verified⟩ :=
    DynamicJointTransaction.search_good_setup_joint_final_event
      functions tx selected lock firstWidth secondWidth pinShort
      nonce0Short nonce1Short stack validKey ecdsa firstRound
      sourceFinal found noCommitmentDER nonceAll
  exact ⟨firstRound, sourceFinal, trace, a, b, beforeCheck,
    key, found, extracted, seven, hits, distinct, count,
    reached, der, inputValid, verified⟩

end QSB.CoreCheckedJointTransaction
