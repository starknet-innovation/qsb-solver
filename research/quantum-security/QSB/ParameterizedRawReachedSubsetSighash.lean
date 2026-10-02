import QSB.ParameterizedReachedSubsetSighash
import QSB.RawReachedSubsetSighash

/-!
Carry the parameterized good-setup final-preimage classification through the
raw-byte source frontend. Each transaction and initial stack comes from the
same successful `prepare` call. The transaction parser, arbitrary scriptSig
evaluator, and checked lock are source models, not compiled Core semantics.
-/
namespace QSB.ParameterizedRawReachedSubsetSighash
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- For two parameterized raw source attempts, equality of their reached
final ALL preimages is exactly equality of their selected dummy-position
sets. Parsing, scriptSig evaluation, checked execution and the reached final
slots are all tied to each submitted raw attempt within the Lean source
model. The good-setup and wire-width premises are explicit; no compiled-Core
or quantum probability conclusion follows. -/
theorem accepted_raw_pair_preimage_classification
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (leftRaw rightRaw : DynamicRawSource.RawAttempt)
    (leftAccepted : DynamicRawSource.sourceAccepted functions lock
      validKey ecdsa evalScriptSig leftRaw)
    (rightAccepted : DynamicRawSource.sourceAccepted functions lock
      validKey ecdsa evalScriptSig rightRaw)
    (sameSelected : leftRaw.selected = rightRaw.selected)
    (sameErased : RawReachedSubsetSighash.erasedFields leftRaw =
      RawReachedSubsetSighash.erasedFields rightRaw)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false) :
    ∃ (leftAttempt rightAttempt : DynamicSourceGame.Attempt),
      DynamicRawSource.prepare evalScriptSig leftRaw = some leftAttempt ∧
      DynamicRawSource.prepare evalScriptSig rightRaw = some rightAttempt ∧
      leftAttempt.selected = rightAttempt.selected ∧
      ∃ (leftRound rightRound : Bool)
        (leftBefore rightBefore : CoreOpcodeStep.State)
        (left right : ParameterizedReachedSubsetSighash.Reached lock.nonce1),
        CoreStructuralRun.run (JointSourceChecks.hashes functions)
          (DynamicCheckedCertificate.beforeFinalProgram lock)
          (DynamicCheckedCertificate.initial leftAttempt.stack leftRound) =
            some leftBefore ∧
        CoreStructuralRun.run (JointSourceChecks.hashes functions)
          (DynamicCheckedCertificate.beforeFinalProgram lock)
          (DynamicCheckedCertificate.initial rightAttempt.stack rightRound) =
            some rightBefore ∧
        left.stack = leftBefore.stack.reverse ∧
        right.stack = rightBefore.stack.reverse ∧
        (ParameterizedReachedSubsetSighash.selectedIds left).Nodup ∧
        (ParameterizedReachedSubsetSighash.selectedIds right).Nodup ∧
        (SighashAllWire.sourceAllPreimage leftAttempt.tx
            leftAttempt.selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              leftBefore.stack.reverse 10 10) =
          SighashAllWire.sourceAllPreimage rightAttempt.tx
            rightAttempt.selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              rightBefore.stack.reverse 10 10) ↔
          (ParameterizedReachedSubsetSighash.selectedIds left).toFinset =
            (ParameterizedReachedSubsetSighash.selectedIds right).toFinset) := by
  obtain ⟨leftAttempt, leftPrepared, leftSource⟩ := leftAccepted
  obtain ⟨rightAttempt, rightPrepared, rightSource⟩ := rightAccepted
  obtain ⟨leftValid, leftMatched, leftFinal, leftRecords,
    leftRun, leftTruth⟩ := leftSource
  obtain ⟨_rightValid, rightMatched, rightFinal, rightRecords,
    rightRun, rightTruth⟩ := rightSource
  obtain ⟨leftEnvelope, _leftSig, leftDecoded, leftTx, leftSelected,
    _leftSupplied, _leftSigAt, _leftEvaluated, _leftRawBytes⟩ :=
    DynamicRawSource.prepare_provenance evalScriptSig leftRaw
      leftAttempt leftPrepared
  obtain ⟨rightEnvelope, _rightSig, rightDecoded, rightTx,
    rightSelected, _rightSupplied, _rightSigAt, _rightEvaluated,
    _rightRawBytes⟩ :=
    DynamicRawSource.prepare_provenance evalScriptSig rightRaw
      rightAttempt rightPrepared
  have selectedEq : leftAttempt.selected = rightAttempt.selected := by
    calc
      leftAttempt.selected = leftRaw.selected := leftSelected
      _ = rightRaw.selected := sameSelected
      _ = rightAttempt.selected := rightSelected.symm
  have erasedEq :
      ScriptSigSighash.eraseScripts leftAttempt.tx =
        ScriptSigSighash.eraseScripts rightAttempt.tx := by
    have h := sameErased
    simp only [RawReachedSubsetSighash.erasedFields,
      leftDecoded, rightDecoded, Option.map_some] at h
    simpa [leftTx, rightTx] using h
  have selectedValid :
      leftAttempt.selected < leftAttempt.tx.inputs.length := by
    simpa [leftSelected] using
      DynamicRawSource.prepare_selected_input evalScriptSig leftRaw
        leftAttempt leftPrepared
  obtain ⟨leftRound, leftSourceFinal, leftFound⟩ :=
    CoreCheckedWire.run_search_succeeds
      (JointSourceChecks.hashes functions) lock leftAttempt.supplied
      leftMatched firstWidth secondWidth pinShort nonce0Short nonce1Short
      leftAttempt.stack validKey
      (JointSourceChecks.checker functions leftAttempt.tx
        leftAttempt.selected ecdsa)
      leftFinal leftRecords leftRun leftTruth
  obtain ⟨rightRound, rightSourceFinal, rightFound⟩ :=
    CoreCheckedWire.run_search_succeeds
      (JointSourceChecks.hashes functions) lock rightAttempt.supplied
      rightMatched firstWidth secondWidth pinShort nonce0Short nonce1Short
      rightAttempt.stack validKey
      (JointSourceChecks.checker functions rightAttempt.tx
        rightAttempt.selected ecdsa)
      rightFinal rightRecords rightRun rightTruth
  obtain ⟨leftBefore, rightBefore, left, right, leftReached,
    rightReached, leftStackEq, rightStackEq, leftDistinct,
    rightDistinct, classification⟩ :=
    ParameterizedReachedSubsetSighash.checked_search_pair_all_preimage_classification
      (JointSourceChecks.hashes functions) lock
      leftAttempt.stack rightAttempt.stack validKey validKey
      (JointSourceChecks.checker functions leftAttempt.tx
        leftAttempt.selected ecdsa)
      (JointSourceChecks.checker functions rightAttempt.tx
        rightAttempt.selected ecdsa)
      leftRound rightRound leftSourceFinal rightSourceFinal
      leftFound rightFound firstWidth secondWidth pinShort
      nonce0Short nonce1Short nonceAll noCommitmentDER
      leftAttempt.tx rightAttempt.tx leftAttempt.selected
      leftValid selectedValid erasedEq
  refine ⟨leftAttempt, rightAttempt, leftPrepared, rightPrepared,
    selectedEq, leftRound, rightRound, leftBefore, rightBefore,
    left, right, leftReached, rightReached, leftStackEq, rightStackEq,
    leftDistinct, rightDistinct, ?_⟩
  simpa only [selectedEq] using classification

end QSB.ParameterizedRawReachedSubsetSighash
