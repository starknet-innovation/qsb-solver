import QSB.CoreCheckedJointTransaction

/-!
Execute the checked Config A source model from its serialized lock bytes.
The parser and checker are Lean source-shaped models. This bridges the
parameterized wire and opcode theorems without claiming that the Python
builder or compiled Bitcoin Core refines either model.
-/
namespace QSB.CoreCheckedWire
open ByteMachine

def chunkCount (lock : DynamicCheckedCertificate.Lock) : Nat :=
  (DynamicWireSource.fullChunks
    (DynamicFullSerialized.priorChunks lock.pin lock.nonce0
      lock.firstCommitment) lock.nonce1 lock.secondCommitment).length

/-- Decode the actual modeled wire before running the checked source model. -/
def run (hashes : Hashes) (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) :
    Option (CoreCheckedStep.State × List Bool) := do
  let ops ← DynamicSerializedRound.parseCoreOps
    (chunkCount lock) (DynamicCheckedCertificate.wire lock)
  CoreCheckedStep.run hashes (DynamicCheckedCertificate.wire lock)
    validKey verify ops ⟨stack.reverse, 0⟩

/-- On the admitted fixed-signature/commitment widths, decoding the modeled
wire produces exactly the program used by the checker-derived extraction. -/
theorem run_eq_model (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) :
    run hashes lock stack validKey verify =
      CoreCheckedStep.run hashes (DynamicCheckedCertificate.wire lock)
        validKey verify (DynamicCheckedCertificate.program lock)
        ⟨stack.reverse, 0⟩ := by
  have parsed := DynamicFullSerialized.full_wire_decodes
    lock.pin lock.nonce0 lock.nonce1 lock.firstCommitment
    lock.secondCommitment firstWidth secondWidth pinShort
    nonce0Short nonce1Short
  simpa [run, chunkCount, DynamicCheckedCertificate.wire,
    DynamicCheckedCertificate.program, DynamicFullSerialized.fullWire]
    using congrArg
      (fun parsedOps => parsedOps.bind fun ops =>
        CoreCheckedStep.run hashes
          (DynamicCheckedCertificate.wire lock) validKey verify ops
          ⟨stack.reverse, 0⟩) parsed

/-- A truthy wire-decoded run yields the same executable certificate search
without a caller-supplied opcode program or signature-result list. -/
theorem run_search_succeeds (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : run hashes lock stack validKey verify =
      some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ firstRound sourceFinal,
      DynamicCheckedCertificate.search hashes lock stack validKey verify =
        some (firstRound, sourceFinal) := by
  rw [run_eq_model hashes lock firstWidth secondWidth pinShort
    nonce0Short nonce1Short stack validKey verify] at success
  exact CoreCheckedDynamic.checked_run_search_succeeds hashes lock
    stack validKey verify final records success accepted

/-- A wire-decoded, truthy transaction run forces the two strict-DER key
hits and fixed pin/final ALL checker calls in one shared H/R world. This is
still conditional on the source-shaped checker and its external ECDSA. -/
theorem run_two_key_joint_hit
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
    (success : run (JointSourceChecks.hashes functions) lock stack
      validKey (JointSourceChecks.checker functions tx selected ecdsa) =
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
  rw [run_eq_model (JointSourceChecks.hashes functions) lock
    firstWidth secondWidth pinShort nonce0Short nonce1Short
    stack validKey (JointSourceChecks.checker functions tx selected ecdsa)]
    at success
  exact CoreCheckedJointTransaction.checked_run_two_key_joint_hit
    functions tx selected lock secondWidth stack validKey ecdsa
    final records success accepted pinAll nonceAll

/-- Off the explicit DER-shaped-commitment setup exception, the same
wire-decoded run yields seven reached HORS equations, nine distinct positions,
and the final DER/ALL event. This remains a source-model implication. -/
theorem run_good_setup_joint_final_event
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
    (success : run (JointSourceChecks.hashes functions) lock stack
      validKey (JointSourceChecks.checker functions tx selected ecdsa) =
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
  rw [run_eq_model (JointSourceChecks.hashes functions) lock
    firstWidth secondWidth pinShort nonce0Short nonce1Short
    stack validKey (JointSourceChecks.checker functions tx selected ecdsa)]
    at success
  exact CoreCheckedJointTransaction.checked_run_good_setup_joint_final_event
    functions tx selected lock firstWidth secondWidth pinShort nonce0Short
    nonce1Short stack validKey ecdsa final records success accepted
    noCommitmentDER nonceAll

end QSB.CoreCheckedWire
