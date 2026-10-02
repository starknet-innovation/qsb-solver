import QSB.LedgerBoundRawSource
import QSB.DynamicRetarget

/-!
Carry the good-setup public-history event from one truthy checked-source run
to the raw transaction and ledger-bound frontend. The arbitrary scriptSig
evaluator and the implication from compiled Core acceptance to this source
predicate remain external. No oracle-query probability is asserted.
-/
namespace QSB.RawPublicHistoryEvent
open ByteMachine

/-- One source attempt's extracted event. Both reached calls, the seven HORS
equations, and the two bonus positions are in one H/R world and one selected
raw transaction. The public-key set and approved-call history are supplied. -/
def GoodSetupEvent
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List
      (DynamicRetarget.ReleasedAllCall functions ecdsa ledger authorized))
    (publicKeys : Set Bytes)
    (attempt : DynamicSourceGame.Attempt) : Prop :=
  ∃ (firstRound : Bool) (sourceFinal : CoreOpcodeStep.State)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
    (pinKey finalKey : Bytes)
    (beforePin beforeCheck : CoreOpcodeStep.State),
    DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock attempt.stack validKey
      (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa) =
        some (firstRound, sourceFinal) ∧
    DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions)
      (DynamicFullSerialized.priorOps lock.pin lock.nonce0
        lock.firstCommitment)
      ⟨attempt.stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
        some trace ∧
    trace.length = 7 ∧
    (∀ p ∈ trace,
      functions.R (functions.H p.2) = lock.secondCommitment p.1) ∧
    (a :: b :: trace.map Prod.fst).Nodup ∧
    (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
    CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 2)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) =
        some beforePin ∧
    CoreStructuralRun.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) =
        some beforeCheck ∧
    DynamicJointTransaction.reachedPinSignature beforePin = lock.pin ∧
    DynamicJointTransaction.reachedPinKey beforePin = pinKey ∧
    CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
      some lock.nonce1 ∧
    CoreMultisigStack.keyAt beforeCheck.stack 9 = some finalKey ∧
    DynamicRetarget.PublicHistoryCallEvent functions ecdsa contract
      ledger authorized history publicKeys lock.pin.dropLast pinKey
      attempt.tx attempt.selected
      (DynamicJointTransaction.reachedPinScriptCode lock beforePin) ∧
    DynamicRetarget.PublicHistoryCallEvent functions ecdsa contract
      ledger authorized history publicKeys lock.nonce1.dropLast finalKey
      attempt.tx attempt.selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicCheckedCertificate.wire lock)
        beforeCheck.stack.reverse 10 10)

/-- Source acceptance supplies the earlier search certificate, so the
joint public-history event follows on a good setup and forbidden projection.
This theorem does not start from actual Core acceptance. -/
theorem source_accepted_good_setup_event
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List
      (DynamicRetarget.ReleasedAllCall functions ecdsa ledger authorized))
    (publicKeys : Set Bytes)
    (attempt : DynamicSourceGame.Attempt)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (accepted : DynamicSourceGame.sourceAccepted functions lock validKey
      ecdsa attempt)
    (forbidden : DynamicSourceGame.sourceProjection ledger attempt ∉
      authorized) :
    GoodSetupEvent functions lock validKey ecdsa contract ledger authorized
      history publicKeys attempt := by
  obtain ⟨txValid, wireMatched, final, records, success, truth⟩ := accepted
  obtain ⟨firstRound, sourceFinal, found⟩ :=
    CoreCheckedWire.run_search_succeeds
      (JointSourceChecks.hashes functions) lock attempt.supplied
      wireMatched firstWidth secondWidth pinShort nonce0Short nonce1Short
      attempt.stack validKey
      (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa)
      final records success truth
  obtain ⟨trace, a, b, pinKey, finalKey, beforePin, beforeCheck,
    extracted, seven, hits, distinct, count, pinReached, checkReached,
    pinSig, pinKeyAt, nonceSig, finalKeyAt, pinCase, finalCase⟩ :=
      DynamicRetarget.search_good_setup_joint_public_history_event
        functions attempt.tx attempt.selected lock firstWidth secondWidth
        pinShort nonce0Short nonce1Short attempt.stack validKey ecdsa
        contract firstRound sourceFinal found noCommitmentDER pinAll nonceAll
        ledger authorized history publicKeys txValid forbidden
  exact ⟨firstRound, sourceFinal, trace, a, b, pinKey, finalKey,
    beforePin, beforeCheck, found, extracted, seven, hits, distinct, count,
    pinReached, checkReached, pinSig, pinKeyAt, nonceSig, finalKeyAt,
    pinCase, finalCase⟩

/-- The submitted bytes select the scriptSig, transaction fields, target
prevout, and ledger script. Only the checked-source acceptance predicate is
used; the evaluator and compiled-Core refinement are still outstanding. -/
theorem raw_source_accepted_good_setup_event
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (authorized : Set Game.Projection)
    (history : List
      (DynamicRetarget.ReleasedAllCall functions ecdsa ledger authorized))
    (publicKeys : Set Bytes)
    (raw : LedgerBoundRawSource.Submission)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (accepted : LedgerBoundRawSource.sourceAccepted functions lock validKey
      ecdsa evalScriptSig ledger target raw)
    (forbidden : LedgerBoundRawSource.projection ledger raw ∉ authorized) :
    ∃ bound attempt,
      LedgerBoundRawSource.bindRaw ledger target raw = some bound ∧
      DynamicRawSource.prepare evalScriptSig bound = some attempt ∧
      LedgerBoundRawSource.spendsTarget target raw ∧
      GoodSetupEvent functions lock validKey ecdsa contract ledger authorized
        history publicKeys attempt := by
  obtain ⟨bound, boundEq, attempt, prepared, source⟩ := accepted
  have targetSpent : LedgerBoundRawSource.spendsTarget target raw :=
    LedgerBoundRawSource.accepted_spends_target functions lock validKey
      ecdsa evalScriptSig ledger target raw
      ⟨bound, boundEq, attempt, prepared, source⟩
  have projectionEq : LedgerBoundRawSource.projection ledger raw =
      DynamicSourceGame.sourceProjection ledger attempt := by
    rw [LedgerBoundRawSource.projection_eq_bound ledger target raw
      bound boundEq,
      DynamicRawSource.prepare_projection evalScriptSig ledger bound
        attempt prepared]
  have forbiddenAttempt :
      DynamicSourceGame.sourceProjection ledger attempt ∉ authorized := by
    rw [projectionEq] at forbidden
    exact forbidden
  exact ⟨bound, attempt, boundEq, prepared, targetSpent,
    source_accepted_good_setup_event functions lock validKey ecdsa contract
      ledger authorized history publicKeys attempt firstWidth secondWidth
      pinShort nonce0Short nonce1Short noCommitmentDER pinAll nonceAll
      source forbiddenAttempt⟩

end QSB.RawPublicHistoryEvent
