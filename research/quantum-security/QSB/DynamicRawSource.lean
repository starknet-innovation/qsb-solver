import QSB.DynamicSourceGame
import QSB.TransactionEnvelopeWire

/-!
Raw-byte frontend for the checked source game. The transaction envelope and
selected scriptSig are parsed from the submitted raw bytes. `EvalScriptSig` is
an explicit external function: arbitrary bare scriptSig programs may contain
non-push opcodes and signature checks, so a push-only parser would be unsound.
This module does not equate the Lean parser or evaluator with compiled Core.
-/
namespace QSB.DynamicRawSource
open ByteMachine

structure RawAttempt where
  rawTx : Bytes
  selected : Nat
  spentScript : Bytes

/-- The evaluator may depend on the entire parsed transaction and selected
input, as Core's scriptSig signature checks can. Its output is the bottom-first
stack at entry to the bare locking script. -/
abbrev EvalScriptSig :=
  SighashAllWire.TxFields → Nat → Bytes → Option (List Bytes)

def scriptSigAt (tx : SighashAllWire.TxFields) (selected : Nat) :
    Option Bytes := do
  let input ← tx.inputs[selected]?
  some input.2.2.1

theorem scriptSigAt_some_selected_valid
    (tx : SighashAllWire.TxFields) (selected : Nat) (scriptSig : Bytes)
    (found : scriptSigAt tx selected = some scriptSig) :
    selected < tx.inputs.length := by
  unfold scriptSigAt at found
  cases inputAt : tx.inputs[selected]? with
  | none => simp [inputAt] at found
  | some input => exact (List.getElem?_eq_some_iff.mp inputAt).1

/-- Build a checked-source attempt from one complete raw transaction. The
spent-output script is supplied separately because it is not serialized in
the spending transaction. -/
def prepare (evalScriptSig : EvalScriptSig) (raw : RawAttempt) :
    Option DynamicSourceGame.Attempt := do
  let envelope ← TransactionEnvelopeWire.decodeStrict raw.rawTx
  let tx := TransactionEnvelopeWire.fields envelope
  let scriptSig ← scriptSigAt tx raw.selected
  let stack ← evalScriptSig tx raw.selected scriptSig
  some ⟨tx, raw.selected, raw.spentScript, stack⟩

/-- No transaction fields or scriptSig bytes can be chosen independently of
the parsed raw envelope. This is a Lean parser provenance theorem. -/
theorem prepare_provenance (evalScriptSig : EvalScriptSig)
    (raw : RawAttempt) (attempt : DynamicSourceGame.Attempt)
    (prepared : prepare evalScriptSig raw = some attempt) :
    ∃ envelope scriptSig,
      TransactionEnvelopeWire.decodeStrict raw.rawTx = some envelope ∧
      attempt.tx = TransactionEnvelopeWire.fields envelope ∧
      attempt.selected = raw.selected ∧
      attempt.supplied = raw.spentScript ∧
      scriptSigAt attempt.tx raw.selected = some scriptSig ∧
      evalScriptSig attempt.tx raw.selected scriptSig =
        some attempt.stack ∧
      raw.rawTx = TransactionEnvelopeWire.encode envelope := by
  unfold prepare at prepared
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => simp [decoded] at prepared
  | some envelope =>
    cases selectedSig : scriptSigAt
        (TransactionEnvelopeWire.fields envelope) raw.selected with
    | none => simp [decoded, selectedSig] at prepared
    | some scriptSig =>
      cases evaluated : evalScriptSig
          (TransactionEnvelopeWire.fields envelope) raw.selected scriptSig with
      | none => simp [decoded, selectedSig, evaluated] at prepared
      | some stack =>
        have same :
            (⟨TransactionEnvelopeWire.fields envelope, raw.selected,
              raw.spentScript, stack⟩ : DynamicSourceGame.Attempt) =
              attempt := by
          simpa [decoded, selectedSig, evaluated] using prepared
        subst attempt
        exact ⟨envelope, scriptSig, rfl, rfl, rfl, rfl,
          selectedSig, evaluated,
          TransactionEnvelopeWire.decodeStrict_sound
            raw.rawTx envelope decoded⟩

/-- A prepared attempt necessarily selects a real input of the parsed raw
transaction, even if the scriptSig evaluator is otherwise arbitrary. -/
theorem prepare_selected_input (evalScriptSig : EvalScriptSig)
    (raw : RawAttempt) (attempt : DynamicSourceGame.Attempt)
    (prepared : prepare evalScriptSig raw = some attempt) :
    raw.selected < attempt.tx.inputs.length := by
  obtain ⟨_envelope, scriptSig, _decoded, _txEq, _selected,
    _supplied, selectedSig, _evaluated, _rawEq⟩ :=
    prepare_provenance evalScriptSig raw attempt prepared
  exact scriptSigAt_some_selected_valid attempt.tx raw.selected
    scriptSig selectedSig

private def emptyProjection : Game.Projection :=
  { version := 0, inputs := [], sequences := [], locktime := 0,
    outputs := [], previousOutputs := [] }

/-- Total projection for the game interface. Its empty fallback is reached
only when the raw parser fails; such an attempt cannot satisfy
`sourceAccepted`. -/
def projection (ledger : Game.Outpoint → Game.Output)
    (raw : RawAttempt) : Game.Projection :=
  match TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => emptyProjection
  | some envelope => SighashAllWire.projectionWithLedger ledger
      (TransactionEnvelopeWire.fields envelope)

theorem prepare_projection (evalScriptSig : EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (raw : RawAttempt) (attempt : DynamicSourceGame.Attempt)
    (prepared : prepare evalScriptSig raw = some attempt) :
    projection ledger raw = DynamicSourceGame.sourceProjection ledger attempt := by
  obtain ⟨envelope, _script, decoded, txEq, _selected,
    _supplied, _scriptAt, _evaluated, _rawEq⟩ :=
    prepare_provenance evalScriptSig raw attempt prepared
  simp [projection, decoded, DynamicSourceGame.sourceProjection, txEq]

/-- The raw extractor uses submitted raw bytes, the separately supplied spent
script, lock/checker functions, and the scriptSig evaluator. It has no explicit
secret-map argument; the supplied evaluator's independence and query cost are
not established here. -/
def extractor (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig) (raw : RawAttempt) :
    Option (Bytes × RoundWitness (Fin 150) Bytes Bytes) := do
  let attempt ← prepare evalScriptSig raw
  DynamicSourceGame.extractor functions lock validKey ecdsa attempt

def sourceAccepted (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig) (raw : RawAttempt) : Prop :=
  ∃ attempt, prepare evalScriptSig raw = some attempt ∧
    DynamicSourceGame.sourceAccepted functions lock validKey ecdsa attempt

def pinRelation (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig)
    (raw : RawAttempt) (key : Bytes) : Prop :=
  ∃ attempt, prepare evalScriptSig raw = some attempt ∧
    DynamicSourceGame.pinRelation functions lock validKey ecdsa attempt key

def roundRelation (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig)
    (raw : RawAttempt) (positions : Finset (Fin 150)) (key : Bytes) : Prop :=
  ∃ attempt, prepare evalScriptSig raw = some attempt ∧
    DynamicSourceGame.roundRelation functions lock validKey ecdsa
      attempt positions key

/-- One joint event on the raw attempt. The same functions H and R feed
commitment checks, key puzzles, and source-shaped SHA256d calls. -/
def sourceJointFailure (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) (released : Set RawAttempt)
    (disclosed : Finset (Fin 150)) (raw : RawAttempt) : Prop :=
  FreshFailure (extractor functions lock validKey ecdsa evalScriptSig)
      (fun opening => functions.R (functions.H opening))
      lock.secondCommitment
      (ForbiddenMessage (projection ledger) authorized) disclosed raw ∨
    TwoPuzzleFailure (extractor functions lock validKey ecdsa evalScriptSig)
      (pinRelation functions lock validKey ecdsa evalScriptSig)
      (roundRelation functions lock validKey ecdsa evalScriptSig)
      functions.H JointOracleReduction.strictDERTarget
      (ForbiddenMessage (projection ledger) authorized)
      released disclosed raw

/-- The abstract game extraction premise is discharged for the raw-byte
*source-model* acceptance predicate. The only evaluator premise is hidden in
that predicate's actual successful `prepare` result, not an existential
selection of challenger secrets. A real Core acceptance refinement is open. -/
theorem source_extraction
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig)
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
      (sourceAccepted functions lock validKey ecdsa evalScriptSig)
      (fun _ : RawAttempt => True)
      (extractor functions lock validKey ecdsa evalScriptSig)
      (fun opening => functions.R (functions.H opening))
      lock.secondCommitment
      (pinRelation functions lock validKey ecdsa evalScriptSig)
      (roundRelation functions lock validKey ecdsa evalScriptSig)
      functions.H JointOracleReduction.strictDERTarget := by
  intro raw accepted _
  obtain ⟨attempt, prepared, checked⟩ := accepted
  obtain ⟨pinKey, w, extracted, shape, pin, round⟩ :=
    DynamicSourceGame.source_extraction functions lock validKey ecdsa
      firstWidth secondWidth pinShort nonce0Short nonce1Short
      noCommitmentDER pinAll nonceAll attempt checked trivial
  refine ⟨pinKey, w, ?_, shape, ?_, ?_⟩
  · simpa [extractor, prepared] using extracted
  · exact ⟨⟨attempt, prepared, pin.nonceBound⟩, pin.puzzle⟩
  · exact ⟨round.openings,
      ⟨attempt, prepared, round.nonceBound⟩, round.puzzle⟩

/-- The raw-byte checked-source game has no internal extraction gap on a good
setup, even though actual Core-to-Lean acceptance refinement is unproved. -/
theorem source_unauthorized_fresh_or_two_puzzle
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) (released : Set RawAttempt)
    (disclosed : Finset (Fin 150)) (raw : RawAttempt)
    (honest : AuthorizedRelease (projection ledger) authorized released)
    (bad : Game.Unauthorized
      (sourceAccepted functions lock validKey ecdsa evalScriptSig)
      (fun _ : RawAttempt => True) (projection ledger) authorized raw) :
    sourceJointFailure functions lock validKey ecdsa evalScriptSig ledger
      authorized released disclosed raw := by
  exact unauthorized_under_source_extraction honest
    (source_extraction functions lock validKey ecdsa evalScriptSig
      firstWidth secondWidth pinShort nonce0Short nonce1Short
      noCommitmentDER pinAll nonceAll) bad

/-- A failed good-setup condition stays visible as the DER-shaped commitment
alternative; no setup probability or quantum-query bound is inferred. -/
theorem source_unauthorized_joint_or_bad_setup
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) (released : Set RawAttempt)
    (disclosed : Finset (Fin 150)) (raw : RawAttempt)
    (honest : AuthorizedRelease (projection ledger) authorized released)
    (bad : Game.Unauthorized
      (sourceAccepted functions lock validKey ecdsa evalScriptSig)
      (fun _ : RawAttempt => True) (projection ledger) authorized raw) :
    sourceJointFailure functions lock validKey ecdsa evalScriptSig ledger
      authorized released disclosed raw ∨
      DynamicSourceGame.badSetup lock := by
  classical
  by_cases good : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false
  · exact Or.inl (source_unauthorized_fresh_or_two_puzzle functions lock
      validKey ecdsa evalScriptSig firstWidth secondWidth pinShort
      nonce0Short nonce1Short good pinAll nonceAll ledger authorized
      released disclosed raw honest bad)
  · obtain ⟨i, hit⟩ := not_forall.mp good
    have valid : DERSyntax.valid (lock.secondCommitment i) = true := by
      cases h : DERSyntax.valid (lock.secondCommitment i) <;> simp_all
    exact Or.inr ⟨i, valid⟩

/-- This is the exact raw-byte source-model event for one H/R world when the
second-round commitment pool was generated from that world's secret map. The
extractor has no explicit `secrets` argument. Proving that its supplied
evaluator has only permitted oracle access, and counting its and the
adversary's coherent queries, remains a separate QROM task. -/
theorem source_unauthorized_oracle_joint_or_bad_setup
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (secrets : Fin 150 → Bytes)
    (setup : ∀ i, lock.secondCommitment i =
      functions.R (functions.H (secrets i)))
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : EvalScriptSig)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) (released : Set RawAttempt)
    (disclosed : Finset (Fin 150)) (raw : RawAttempt)
    (honest : AuthorizedRelease (projection ledger) authorized released)
    (bad : Game.Unauthorized
      (sourceAccepted functions lock validKey ecdsa evalScriptSig)
      (fun _ : RawAttempt => True) (projection ledger) authorized raw) :
    (FreshFailure (extractor functions lock validKey ecdsa evalScriptSig)
      (fun opening => functions.R (functions.H opening))
      (fun i => functions.R (functions.H (secrets i)))
      (ForbiddenMessage (projection ledger) authorized) disclosed raw ∨
    TwoPuzzleFailure (extractor functions lock validKey ecdsa evalScriptSig)
      (pinRelation functions lock validKey ecdsa evalScriptSig)
      (roundRelation functions lock validKey ecdsa evalScriptSig)
      functions.H JointOracleReduction.strictDERTarget
      (ForbiddenMessage (projection ledger) authorized)
      released disclosed raw) ∨ DynamicSourceGame.badSetup lock := by
  have commitmentEq : lock.secondCommitment =
      fun i => functions.R (functions.H (secrets i)) := funext setup
  simpa only [sourceJointFailure, commitmentEq] using
    source_unauthorized_joint_or_bad_setup functions lock validKey ecdsa
      evalScriptSig firstWidth secondWidth pinShort nonce0Short nonce1Short
      pinAll nonceAll ledger authorized released disclosed raw honest bad

end QSB.DynamicRawSource
