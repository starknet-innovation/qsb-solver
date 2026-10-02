import QSB.DynamicRawSource

/-!
Bind the source-model spent script to the selected prevout in one fixed ledger
resolution function. The submitted bytes no longer carry a separately chosen
locking script. This is still not a compiled-Core transaction parser,
scriptSig evaluator, UTXO membership check, or consensus acceptance proof.
-/
namespace QSB.LedgerBoundRawSource
open ByteMachine

structure Submission where
  rawTx : Bytes
  selected : Nat

/-- Resolve the selected input from the strict source transaction parser and
require that it names the target outpoint. The same ledger function used for
the authorization projection supplies the spent output's script bytes. -/
def bindRaw (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission) :
    Option DynamicRawSource.RawAttempt := do
  let envelope ← TransactionEnvelopeWire.decodeStrict raw.rawTx
  let tx := TransactionEnvelopeWire.fields envelope
  let input ← tx.inputs[raw.selected]?
  if (SighashAllWire.inputReference input).1 = target then
    some ⟨raw.rawTx, raw.selected, (ledger target).script⟩
  else none

theorem bindRaw_sound (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission)
    (bound : DynamicRawSource.RawAttempt)
    (found : bindRaw ledger target raw = some bound) :
    ∃ envelope input,
      TransactionEnvelopeWire.decodeStrict raw.rawTx = some envelope ∧
      (TransactionEnvelopeWire.fields envelope).inputs[raw.selected]? =
        some input ∧
      (SighashAllWire.inputReference input).1 = target ∧
      bound.rawTx = raw.rawTx ∧
      bound.selected = raw.selected ∧
      bound.spentScript = (ledger target).script := by
  unfold bindRaw at found
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => simp [decoded] at found
  | some envelope =>
      cases selectedInput :
          (TransactionEnvelopeWire.fields envelope).inputs[raw.selected]? with
      | none => simp [decoded, selectedInput] at found
      | some input =>
          by_cases same : (SighashAllWire.inputReference input).1 = target
          · simp [decoded, selectedInput, same] at found
            subst bound
            exact ⟨envelope, input, rfl, selectedInput, same,
              rfl, rfl, rfl⟩
          · simp [decoded, selectedInput, same] at found

/-- The selected prevout in the strict raw transaction names the target.
This is a transaction-byte predicate rather than an always-true placeholder. -/
def spendsTarget (target : Game.Outpoint) (raw : Submission) : Prop :=
  ∃ envelope input,
    TransactionEnvelopeWire.decodeStrict raw.rawTx = some envelope ∧
    (TransactionEnvelopeWire.fields envelope).inputs[raw.selected]? =
      some input ∧
    (SighashAllWire.inputReference input).1 = target

def sourceAccepted (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission) : Prop :=
  ∃ bound, bindRaw ledger target raw = some bound ∧
    DynamicRawSource.sourceAccepted functions lock validKey ecdsa
      evalScriptSig bound

theorem accepted_spends_target
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission)
    (accepted : sourceAccepted functions lock validKey ecdsa
      evalScriptSig ledger target raw) :
    spendsTarget target raw := by
  obtain ⟨bound, boundEq, _checked⟩ := accepted
  obtain ⟨envelope, input, decoded, selectedInput, targetEq,
    _rawEq, _selectedEq, _scriptEq⟩ :=
    bindRaw_sound ledger target raw bound boundEq
  exact ⟨envelope, input, decoded, selectedInput, targetEq⟩

/-- A truthy validated source run can only use the script attached to the
target prevout by the fixed ledger resolution. This removes the independently
supplied `spentScript` from the raw-source acceptance premise. -/
theorem accepted_target_script_matches
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission)
    (accepted : sourceAccepted functions lock validKey ecdsa
      evalScriptSig ledger target raw) :
    ∃ envelope input,
      TransactionEnvelopeWire.decodeStrict raw.rawTx = some envelope ∧
      (TransactionEnvelopeWire.fields envelope).inputs[raw.selected]? =
        some input ∧
      (SighashAllWire.inputReference input).1 = target ∧
      (ledger target).script = DynamicCheckedCertificate.wire lock := by
  obtain ⟨bound, boundEq, attempt, prepared, source⟩ := accepted
  obtain ⟨envelope, input, decoded, selectedInput, targetEq,
    _rawEq, _selectedEq, scriptEq⟩ :=
    bindRaw_sound ledger target raw bound boundEq
  obtain ⟨_valid, matched, _final, _records, _run, _truth⟩ := source
  obtain ⟨_envelope, _scriptSig, _decoded, _txEq, _selected,
    suppliedEq, _scriptAt, _evaluated, _rawBytes⟩ :=
    DynamicRawSource.prepare_provenance evalScriptSig bound
      attempt prepared
  have wireEq := CoreCheckedWire.matchesWire_sound attempt.supplied lock matched
  refine ⟨envelope, input, decoded, selectedInput, targetEq, ?_⟩
  calc
    (ledger target).script = bound.spentScript := scriptEq.symm
    _ = attempt.supplied := suppliedEq.symm
    _ = DynamicCheckedCertificate.wire lock := wireEq

theorem rejects_other_target_script
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission)
    (different : (ledger target).script ≠
      DynamicCheckedCertificate.wire lock) :
    ¬sourceAccepted functions lock validKey ecdsa
      evalScriptSig ledger target raw := by
  intro accepted
  obtain ⟨_envelope, _input, _decoded, _selectedInput,
    _targetEq, same⟩ :=
    accepted_target_script_matches functions lock validKey ecdsa
      evalScriptSig ledger target raw accepted
  exact different same

def extractor (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission) :
    Option (Bytes × RoundWitness (Fin 150) Bytes Bytes) := do
  let bound ← bindRaw ledger target raw
  DynamicRawSource.extractor functions lock validKey ecdsa
    evalScriptSig bound

def pinRelation (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission) (key : Bytes) : Prop :=
  ∃ bound, bindRaw ledger target raw = some bound ∧
    DynamicRawSource.pinRelation functions lock validKey ecdsa
      evalScriptSig bound key

def roundRelation (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission)
    (positions : Finset (Fin 150)) (key : Bytes) : Prop :=
  ∃ bound, bindRaw ledger target raw = some bound ∧
    DynamicRawSource.roundRelation functions lock validKey ecdsa
      evalScriptSig bound positions key

/-- The ledger-bound raw source model inherits extraction without giving the
attacker an independent scriptPubKey input. Its remaining evaluator and
Core-refinement premises are unchanged. -/
theorem source_extraction
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    SourceExtraction
      (sourceAccepted functions lock validKey ecdsa evalScriptSig
        ledger target)
      (spendsTarget target)
      (extractor functions lock validKey ecdsa evalScriptSig ledger target)
      (fun opening => functions.R (functions.H opening))
      lock.secondCommitment
      (pinRelation functions lock validKey ecdsa evalScriptSig ledger target)
      (roundRelation functions lock validKey ecdsa evalScriptSig ledger target)
      functions.H JointOracleReduction.strictDERTarget := by
  intro raw accepted _
  obtain ⟨bound, boundEq, checked⟩ := accepted
  obtain ⟨pinKey, w, extracted, shape, pin, round⟩ :=
    DynamicRawSource.source_extraction functions lock validKey ecdsa
      evalScriptSig firstWidth secondWidth pinShort nonce0Short nonce1Short
      noCommitmentDER pinAll nonceAll bound checked trivial
  refine ⟨pinKey, w, ?_, shape, ?_, ?_⟩
  · simpa [extractor, boundEq] using extracted
  · exact ⟨⟨bound, boundEq, pin.nonceBound⟩, pin.puzzle⟩
  · exact ⟨round.openings,
      ⟨bound, boundEq, round.nonceBound⟩, round.puzzle⟩

/-- The projection reuses the same ledger resolution as `bindRaw`. The dummy
script argument here is ignored by the raw projection function. -/
def projection (ledger : Game.Outpoint → Game.Output)
    (raw : Submission) : Game.Projection :=
  DynamicRawSource.projection ledger
    ⟨raw.rawTx, raw.selected, []⟩

theorem projection_eq_bound (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint) (raw : Submission)
    (bound : DynamicRawSource.RawAttempt)
    (found : bindRaw ledger target raw = some bound) :
    projection ledger raw = DynamicRawSource.projection ledger bound := by
  obtain ⟨_envelope, _input, _decoded, _selectedInput,
    _targetEq, rawEq, _selectedEq, _scriptEq⟩ :=
    bindRaw_sound ledger target raw bound found
  simp [projection, DynamicRawSource.projection, rawEq]

def sourceJointFailure (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (authorized : Set Game.Projection) (released : Set Submission)
    (disclosed : Finset (Fin 150)) (raw : Submission) : Prop :=
  FreshFailure
      (extractor functions lock validKey ecdsa evalScriptSig ledger target)
      (fun opening => functions.R (functions.H opening))
      lock.secondCommitment
      (ForbiddenMessage (projection ledger) authorized) disclosed raw ∨
    TwoPuzzleFailure
      (extractor functions lock validKey ecdsa evalScriptSig ledger target)
      (pinRelation functions lock validKey ecdsa evalScriptSig ledger target)
      (roundRelation functions lock validKey ecdsa evalScriptSig ledger target)
      functions.H JointOracleReduction.strictDERTarget
      (ForbiddenMessage (projection ledger) authorized)
      released disclosed raw

/-- An owner-forbidden accepted source-model submission against the ledger's
target script yields one joint failure event, or the explicit DER-shaped
commitment setup exception. The actual chain UTXO predicate, compiled Core
acceptance, and shared-query QROM probability bound remain outside. -/
theorem source_unauthorized_joint_or_bad_setup
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (authorized : Set Game.Projection) (released : Set Submission)
    (disclosed : Finset (Fin 150)) (raw : Submission)
    (honest : AuthorizedRelease (projection ledger) authorized released)
    (bad : Game.Unauthorized
      (sourceAccepted functions lock validKey ecdsa evalScriptSig
        ledger target)
      (spendsTarget target) (projection ledger) authorized raw) :
    sourceJointFailure functions lock validKey ecdsa evalScriptSig
      ledger target authorized released disclosed raw ∨
      DynamicSourceGame.badSetup lock := by
  classical
  by_cases good : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false
  · exact Or.inl (unauthorized_under_source_extraction honest
      (source_extraction functions lock validKey ecdsa evalScriptSig
        ledger target firstWidth secondWidth pinShort nonce0Short
        nonce1Short good pinAll nonceAll) bad)
  · obtain ⟨i, hit⟩ := not_forall.mp good
    have valid : DERSyntax.valid (lock.secondCommitment i) = true := by
      cases h : DERSyntax.valid (lock.secondCommitment i) <;> simp_all
    exact Or.inr ⟨i, valid⟩

end QSB.LedgerBoundRawSource
