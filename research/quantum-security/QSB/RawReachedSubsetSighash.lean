import QSB.DynamicRawSource
import QSB.ReachedSubsetSighash

/-!
Carry the literal final ALL-preimage selected-set classification through the
raw-byte source frontend. The source transaction and initial lock stack now
come from one successful `prepare` call per raw attempt, including its
transaction-dependent arbitrary-scriptSig evaluator. This is still a Lean
source-model result; compiled Core parsing and execution are external.
-/
namespace QSB.RawReachedSubsetSighash
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Compare the committed source transaction fields of two raw submissions
after removing every original scriptSig. A strict decode failure gives none.
This is not a Bitcoin Core raw-transaction parser. -/
def erasedFields (raw : DynamicRawSource.RawAttempt) :
    Option SighashAllWire.TxFields :=
  (TransactionEnvelopeWire.decodeStrict raw.rawTx).map fun envelope =>
    ScriptSigSighash.eraseScripts
      (TransactionEnvelopeWire.fields envelope)

/-- If two raw submissions both satisfy the literal checked-source acceptance
predicate, select the same input, and parse to equal fields after original
scriptSig erasure, their reached final source-shaped ALL preimages have exactly
the equality classes of their nine selected dummy positions. The initial
stacks are the values returned by the supplied scriptSig evaluator on each
parsed transaction. That evaluator, key parser, and ECDSA function remain
external; this is not a compiled-Core acceptance implication. -/
theorem accepted_raw_pair_preimage_classification
    (functions : JointSourceChecks.Functions)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (leftRaw rightRaw : DynamicRawSource.RawAttempt)
    (leftAccepted : DynamicRawSource.sourceAccepted functions
      CoreCheckedWire.literalLock validKey ecdsa evalScriptSig leftRaw)
    (rightAccepted : DynamicRawSource.sourceAccepted functions
      CoreCheckedWire.literalLock validKey ecdsa evalScriptSig rightRaw)
    (sameSelected : leftRaw.selected = rightRaw.selected)
    (sameErased : erasedFields leftRaw = erasedFields rightRaw) :
    ∃ (leftAttempt rightAttempt : DynamicSourceGame.Attempt),
      DynamicRawSource.prepare evalScriptSig leftRaw = some leftAttempt ∧
      DynamicRawSource.prepare evalScriptSig rightRaw = some rightAttempt ∧
      leftAttempt.selected = rightAttempt.selected ∧
      ∃ (leftRecords rightRecords : List Bool)
        (leftTrace rightTrace : List (Fin 150 × Bytes))
        (leftA leftB rightA rightB : Fin 150)
        (leftBefore rightBefore : ByteMachine.State),
        ByteMachine.run (JointSourceChecks.hashes functions)
          (ByteLayout.program.take 879)
          ⟨leftAttempt.stack, leftRecords, 0⟩ = some leftBefore ∧
        ByteMachine.run (JointSourceChecks.hashes functions)
          (ByteLayout.program.take 879)
          ⟨rightAttempt.stack, rightRecords, 0⟩ = some rightBefore ∧
        (leftA :: leftB :: leftTrace.map Prod.fst).Nodup ∧
        (rightA :: rightB :: rightTrace.map Prod.fst).Nodup ∧
        (leftA :: leftB :: leftTrace.map Prod.fst).toFinset.card = 9 ∧
        (rightA :: rightB :: rightTrace.map Prod.fst).toFinset.card = 9 ∧
        (SighashAllWire.sourceAllPreimage leftAttempt.tx
          leftAttempt.selected
          (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
            leftBefore.stack 10 10) =
         SighashAllWire.sourceAllPreimage rightAttempt.tx
          rightAttempt.selected
          (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
            rightBefore.stack 10 10) ↔
         (leftA :: leftB :: leftTrace.map Prod.fst).toFinset =
           (rightA :: rightB :: rightTrace.map Prod.fst).toFinset) := by
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
    simp only [erasedFields, leftDecoded, rightDecoded, Option.map_some]
      at h
    simpa [leftTx, rightTx] using h
  have selectedValid :
      leftAttempt.selected < leftAttempt.tx.inputs.length := by
    simpa [leftSelected] using
      DynamicRawSource.prepare_selected_input evalScriptSig leftRaw
        leftAttempt leftPrepared
  obtain ⟨leftTrace, rightTrace, leftA, leftB, rightA, rightB,
    leftBefore, rightBefore, leftReached, rightReached,
    leftNodup, rightNodup, leftCard, rightCard, classification⟩ :=
      ReachedSubsetSighash.validated_runs_erased_scriptSig_classification
        (JointSourceChecks.hashes functions)
        leftAttempt.tx rightAttempt.tx leftAttempt.selected
        leftValid selectedValid erasedEq
        leftAttempt.supplied rightAttempt.supplied
        leftMatched rightMatched leftAttempt.stack rightAttempt.stack
        validKey
        (JointSourceChecks.checker functions leftAttempt.tx
          leftAttempt.selected ecdsa)
        (JointSourceChecks.checker functions rightAttempt.tx
          rightAttempt.selected ecdsa)
        leftFinal rightFinal leftRecords rightRecords
        leftRun rightRun leftTruth rightTruth
  refine ⟨leftAttempt, rightAttempt, leftPrepared, rightPrepared,
    selectedEq, leftRecords, rightRecords, leftTrace, rightTrace,
    leftA, leftB, rightA, rightB, leftBefore, rightBefore,
    leftReached, rightReached, leftNodup, rightNodup,
    leftCard, rightCard, ?_⟩
  simpa only [selectedEq] using classification

end QSB.RawReachedSubsetSighash
