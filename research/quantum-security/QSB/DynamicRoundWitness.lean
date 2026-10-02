import QSB.CoreCheckedWire
import QSB.FinalRoundWitness

/-!
Build the abstract final-round witness from a returned parameterized checked
certificate. The seven opening pairs come from the executable dynamic trace;
the two bonus indices are decoded from the reached dummy signature bytes,
and the key comes from the reached tenth final multisignature key slot.
This is a Lean source-model extractor, not compiled-Core transaction parsing.
-/
namespace QSB.DynamicRoundWitness
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def extract (hashes : Hashes) (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) :
    Option (RoundWitness (Fin 150) Bytes Bytes) := do
  let found ← DynamicCheckedCertificate.search hashes lock stack validKey verify
  let firstRound := found.1
  let trace ← DynamicWholeSource.extractTrace hashes
    (DynamicFullSerialized.priorOps lock.pin lock.nonce0
      lock.firstCommitment)
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩
  let beforeCheck ← CoreStructuralRun.run hashes
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    (DynamicCheckedCertificate.initial stack firstRound)
  let aByte ← beforeCheck.stack.reverse[13]?
  let bByte ← beforeCheck.stack.reverse[12]?
  let a ← FinalRoundWitness.findDummy aByte
  let b ← FinalRoundWitness.findDummy bByte
  let key ← CoreMultisigStack.keyAt beforeCheck.stack 9
  some (FinalRoundWitness.witnessFromTrace trace a b key)

/-- A good-setup certificate computes a complete shaped final-round witness.
Its key is the reached tenth key, and that same key hashes to a strict-DER
late puzzle signature. No transaction or Core acceptance premise is inferred. -/
theorem search_good_setup_extracts (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search hashes lock stack validKey verify =
      some (firstRound, final))
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false) :
    ∃ w : RoundWitness (Fin 150) Bytes Bytes,
      extract hashes lock stack validKey verify = some w ∧
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 lock.secondCommitment w.signed w.opening ∧
      DERSyntax.valid (hashes.h256 w.key) = true ∧
      ∃ beforeCheck : CoreOpcodeStep.State,
        CoreStructuralRun.run hashes
          (DynamicCheckedCertificate.beforeFinalProgram lock)
          (DynamicCheckedCertificate.initial stack firstRound) =
            some beforeCheck ∧
        CoreMultisigStack.keyAt beforeCheck.stack 9 = some w.key := by
  obtain ⟨trace, a, b, beforeCheck, reached, slotB, slotA,
    _signedSlots, _nonceSlot, seven, hits, distinct, extracted⟩ :=
    DynamicCheckedCertificate.search_good_setup_reached_final_slots
      hashes lock stack validKey verify firstRound final found
      secondWidth noCommitmentDER
  obtain ⟨key, _beforeLate, beforeFromPuzzle, _lateReached,
    puzzleReached, _puzzleSig, keyAt, der⟩ :=
    DynamicCheckedCertificate.search_late_puzzle_final_key_der
      hashes lock stack validKey verify firstRound final found
  have sameBefore : beforeCheck = beforeFromPuzzle :=
    Option.some.inj (reached.symm.trans puzzleReached)
  subst beforeFromPuzzle
  let w := FinalRoundWitness.witnessFromTrace trace a b key
  have computed : extract hashes lock stack validKey verify = some w := by
    simp [extract, found, extracted, reached, slotA, slotB,
      FinalRoundWitness.findDummy_exact, keyAt, w]
  obtain ⟨shape, openings⟩ :=
    FinalRoundWitness.witnessFromTrace_shape_and_openings_for
      hashes.h160 lock.secondCommitment trace a b key seven distinct hits
  refine ⟨w, computed, shape, openings, ?_, beforeCheck, reached, ?_⟩
  · simpa [w, FinalRoundWitness.witnessFromTrace] using der
  · simpa [w, FinalRoundWitness.witnessFromTrace] using keyAt

/-- From one truthy validated supplied-wire run, construct the executable
final-round witness and retain the final ALL verifier call for its reached
key. The ECDSA function and Bitcoin Core acceptance are still external. -/
theorem wire_good_setup_round_and_final_all
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (supplied : Bytes)
    (wireMatched : CoreCheckedWire.matchesWire supplied lock = true)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedWire.run (JointSourceChecks.hashes functions)
      lock supplied stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    ∃ (firstRound : Bool) (sourceFinal : CoreOpcodeStep.State)
      (w : RoundWitness (Fin 150) Bytes Bytes)
      (beforeCheck : CoreOpcodeStep.State),
      DynamicCheckedCertificate.search
        (JointSourceChecks.hashes functions) lock stack validKey
        (JointSourceChecks.checker functions tx selected ecdsa) =
          some (firstRound, sourceFinal) ∧
      extract (JointSourceChecks.hashes functions) lock stack validKey
        (JointSourceChecks.checker functions tx selected ecdsa) = some w ∧
      FinalRoundShape w ∧
      OpeningsValid (fun opening => functions.R (functions.H opening))
        lock.secondCommitment w.signed w.opening ∧
      DERSyntax.valid (functions.H w.key) = true ∧
      selected < tx.inputs.length ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some w.key ∧
      ecdsa lock.nonce1.dropLast w.key
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨firstRound, sourceFinal, found⟩ :=
    CoreCheckedWire.run_search_succeeds
      (JointSourceChecks.hashes functions) lock supplied wireMatched
      firstWidth secondWidth pinShort nonce0Short nonce1Short
      stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      final records success accepted
  obtain ⟨w, computed, shape, openings, der, beforeWitness,
    reachedWitness, witnessKey⟩ :=
    search_good_setup_extracts (JointSourceChecks.hashes functions)
      lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound sourceFinal found secondWidth noCommitmentDER
  obtain ⟨_beforeLate, beforeFinal, key, _lateReached,
    reachedFinal, _puzzleSig, _nonceSlot, finalKey,
    _derFinal, inputValid, verified⟩ :=
    DynamicJointTransaction.search_final_nonce_joint_hit
      functions tx selected lock secondWidth stack validKey ecdsa
      firstRound sourceFinal found nonceAll
  have sameBefore : beforeWitness = beforeFinal :=
    Option.some.inj (reachedWitness.symm.trans reachedFinal)
  subst beforeFinal
  have sameKey : w.key = key :=
    Option.some.inj (witnessKey.symm.trans finalKey)
  rw [← sameKey] at verified
  refine ⟨firstRound, sourceFinal, w, beforeWitness, found, computed,
    shape, ?_, ?_, inputValid, reachedWitness, witnessKey, verified⟩
  · simpa [JointSourceChecks.hashes] using openings
  · simpa [JointSourceChecks.hashes] using der

/-- The same executable witness and certificate also retain the pin key's
strict-DER hit and its fixed ALL call. Key equality is allowed: no independent
hash-hit or quantum-query assertion is made. -/
theorem wire_good_setup_two_puzzles_round_witness
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (supplied : Bytes)
    (wireMatched : CoreCheckedWire.matchesWire supplied lock = true)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedWire.run (JointSourceChecks.hashes functions)
      lock supplied stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    ∃ (w : RoundWitness (Fin 150) Bytes Bytes)
      (pinKey : Bytes) (beforePin beforeCheck : CoreOpcodeStep.State),
      extract (JointSourceChecks.hashes functions) lock stack validKey
        (JointSourceChecks.checker functions tx selected ecdsa) = some w ∧
      FinalRoundShape w ∧
      OpeningsValid (fun opening => functions.R (functions.H opening))
        lock.secondCommitment w.signed w.opening ∧
      DynamicJointTransaction.reachedPinSignature beforePin = lock.pin ∧
      DynamicJointTransaction.reachedPinKey beforePin = pinKey ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some w.key ∧
      DERSyntax.valid (functions.H pinKey) = true ∧
      DERSyntax.valid (functions.H w.key) = true ∧
      selected < tx.inputs.length ∧
      ecdsa lock.pin.dropLast pinKey
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (DynamicJointTransaction.reachedPinScriptCode lock beforePin)))) =
        true ∧
      ecdsa lock.nonce1.dropLast w.key
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨firstRound, sourceFinal, w, beforeCheck, found,
    computed, shape, openings, finalDER, inputValid,
    reachedCheck, wKey, finalVerified⟩ :=
    wire_good_setup_round_and_final_all functions tx selected lock
      supplied wireMatched firstWidth secondWidth pinShort nonce0Short
      nonce1Short stack validKey ecdsa final records success accepted
      noCommitmentDER nonceAll
  obtain ⟨pinKey, _finalKey, beforePin, beforeFromPin,
    _reachedPin, pinCheckReached, fixedPin, reachedPinKey,
    _nonceSlot, _finalKeyAt, pinDER, _otherFinalDER,
    _otherInputValid, pinVerified, _otherFinalVerified⟩ :=
    DynamicJointTransaction.search_two_key_joint_hit functions tx selected
      lock secondWidth stack validKey ecdsa firstRound sourceFinal found
      pinAll nonceAll
  have sameBefore : beforeCheck = beforeFromPin :=
    Option.some.inj (reachedCheck.symm.trans pinCheckReached)
  subst beforeFromPin
  refine ⟨w, pinKey, beforePin, beforeCheck, computed, shape,
    openings, fixedPin, reachedPinKey, wKey, pinDER, finalDER,
    inputValid, pinVerified, finalVerified⟩

end QSB.DynamicRoundWitness
