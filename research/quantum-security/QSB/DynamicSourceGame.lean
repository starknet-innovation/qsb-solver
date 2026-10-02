import QSB.DynamicRoundWitness
import QSB.JointOracleReduction

/-!
Connect the checked parameterized source model to the abstract extraction
game. An attempt contains already-decoded initial stack cells and source-shaped
transaction fields. It is not a raw Bitcoin transaction or a compiled-Core
acceptance judgment. Both game relations below retain their actual reached
fixed-signature ALL calls under one shared H, and the final relation identifies
the nine selected positions returned by the executable source extractor.
-/
namespace QSB.DynamicSourceGame
open ByteMachine

structure Attempt where
  tx : SighashAllWire.TxFields
  selected : Nat
  supplied : Bytes
  stack : List Bytes

private def checker (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool) (attempt : Attempt) :
    CoreChecksigEval.VerifyECDSA :=
  JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa

private def search (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) (attempt : Attempt) :=
  DynamicCheckedCertificate.search (JointSourceChecks.hashes functions)
    lock attempt.stack validKey (checker functions ecdsa attempt)

/-- The game extractor reads only the submitted source-model attempt and the
public lock and checker functions. It does not receive setup secrets. -/
def extractor (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) (attempt : Attempt) :
    Option (Bytes × RoundWitness (Fin 150) Bytes Bytes) := do
  let found ← search functions lock validKey ecdsa attempt
  let beforePin ← CoreStructuralRun.run (JointSourceChecks.hashes functions)
    ((DynamicCheckedCertificate.program lock).take 2)
    (DynamicCheckedCertificate.initial attempt.stack found.1)
  let w ← DynamicRoundWitness.extract (JointSourceChecks.hashes functions)
    lock attempt.stack validKey (checker functions ecdsa attempt)
  some (DynamicJointTransaction.reachedPinKey beforePin, w)

/-- The pin relation retains the reached pin key and its actual ALL call. -/
def pinRelation (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : Attempt) (key : Bytes) : Prop :=
  ∃ firstRound sourceFinal beforePin,
    search functions lock validKey ecdsa attempt =
      some (firstRound, sourceFinal) ∧
    CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 2)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) =
        some beforePin ∧
    DynamicJointTransaction.reachedPinKey beforePin = key ∧
    ecdsa lock.pin.dropLast key
      (functions.H (functions.H
        (SighashAllWire.sourceAllPreimage attempt.tx attempt.selected
          (DynamicJointTransaction.reachedPinScriptCode lock beforePin)))) = true

/-- The final relation records the source-selected nine positions, reached
tenth key, and fixed final ALL call. It uses the same deterministic source
witness as `extractor`, not a private challenger witness. -/
def roundRelation (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : Attempt) (positions : Finset (Fin 150)) (key : Bytes) : Prop :=
  ∃ firstRound sourceFinal beforeCheck,
    ∃ w : RoundWitness (Fin 150) Bytes Bytes,
    search functions lock validKey ecdsa attempt =
      some (firstRound, sourceFinal) ∧
    CoreStructuralRun.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) =
        some beforeCheck ∧
    DynamicRoundWitness.extract (JointSourceChecks.hashes functions)
      lock attempt.stack validKey (checker functions ecdsa attempt) = some w ∧
    positions = w.signed ∪ w.bonus ∧
    key = w.key ∧
    CoreMultisigStack.keyAt beforeCheck.stack 9 = some key ∧
    ecdsa lock.nonce1.dropLast key
      (functions.H (functions.H
        (SighashAllWire.sourceAllPreimage attempt.tx attempt.selected
          (CoreMultisigSourceScan.deletedScript
            (DynamicCheckedCertificate.wire lock)
            beforeCheck.stack.reverse 10 10)))) = true

/-- Acceptance here is exactly the truthy checked *source model*, guarded by
the executable equality test on supplied lock bytes. -/
def sourceAccepted (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) (attempt : Attempt) : Prop :=
  SighashAllWire.valid attempt.tx ∧
  CoreCheckedWire.matchesWire attempt.supplied lock = true ∧
  ∃ final records,
    CoreCheckedWire.run (JointSourceChecks.hashes functions) lock
      attempt.supplied attempt.stack validKey
      (checker functions ecdsa attempt) = some (final, records) ∧
    CoreFinalTruth.castToBool (final.stack.getLast?.getD []) = true

/-- The owner-facing projection is built from the attempt's source-shaped
transaction fields and one fixed ledger context. -/
def sourceProjection (ledger : Game.Outpoint → Game.Output)
    (attempt : Attempt) : Game.Projection :=
  SighashAllWire.projectionWithLedger ledger attempt.tx

def badSetup (lock : DynamicCheckedCertificate.Lock) : Prop :=
  ∃ i : Fin 150, DERSyntax.valid (lock.secondCommitment i) = true

/-- One deterministic event on the same H/R functions and the same submitted
attempt. Its probability still requires a shared-budget QROM argument. -/
def sourceJointFailure (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) (released : Set Attempt)
    (disclosed : Finset (Fin 150)) (attempt : Attempt) : Prop :=
  FreshFailure (extractor functions lock validKey ecdsa)
      (fun opening => functions.R (functions.H opening))
      lock.secondCommitment
      (ForbiddenMessage (sourceProjection ledger) authorized)
      disclosed attempt ∨
    TwoPuzzleFailure (extractor functions lock validKey ecdsa)
      (pinRelation functions lock validKey ecdsa)
      (roundRelation functions lock validKey ecdsa)
      functions.H JointOracleReduction.strictDERTarget
      (ForbiddenMessage (sourceProjection ledger) authorized)
      released disclosed attempt

/-- The game evidence is computed for every good-setup truthy checked-source
attempt. The only global assumptions are lock shape and the two fixed ALL
hash-type bytes; there is no Core-acceptance or QROM conclusion. -/
theorem source_extraction
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
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
      (sourceAccepted functions lock validKey ecdsa) (fun _ : Attempt => True)
      (extractor functions lock validKey ecdsa)
      (fun opening => functions.R (functions.H opening))
      lock.secondCommitment
      (pinRelation functions lock validKey ecdsa)
      (roundRelation functions lock validKey ecdsa)
      functions.H JointOracleReduction.strictDERTarget := by
  intro attempt accepted _
  obtain ⟨_validTx, wireMatched, final, records, success, truth⟩ := accepted
  obtain ⟨w, pinKey, beforePin, beforeCheck, firstRound, sourceFinal,
    found, pinRun, finalRun, computed, shape, openings, _pinSig,
    pinKeyAt, finalKeyAt, pinDER, finalDER, _input,
    pinVerified, finalVerified⟩ :=
    DynamicRoundWitness.wire_good_setup_two_puzzles_round_witness
      functions attempt.tx attempt.selected lock attempt.supplied
      wireMatched firstWidth secondWidth pinShort nonce0Short nonce1Short
      attempt.stack validKey ecdsa final records success truth
      noCommitmentDER pinAll nonceAll
  have extracted : extractor functions lock validKey ecdsa attempt =
      some (pinKey, w) := by
    simp [extractor, search, checker, found, pinRun, computed, pinKeyAt]
  refine ⟨pinKey, w, extracted, shape, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact ⟨firstRound, sourceFinal, beforePin,
        by simpa [search, checker] using found,
        pinRun, pinKeyAt, pinVerified⟩
    · simpa [JointOracleReduction.strictDERTarget] using pinDER
  · refine ⟨openings, ?_, ?_⟩
    · exact ⟨firstRound, sourceFinal, beforeCheck, w,
        by simpa [search, checker] using found,
        finalRun, computed, rfl, rfl, finalKeyAt, finalVerified⟩
    · simpa [JointOracleReduction.strictDERTarget] using finalDER

/-- The abstract fresh-opening-or-two-puzzle disjunction now has no extraction
gap for this checked source model. Core consensus acceptance, transaction-byte
stack parsing, and a quantum event bound remain outside this statement. -/
theorem source_unauthorized_fresh_or_two_puzzle
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
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
    (authorized : Set Game.Projection) (released : Set Attempt)
    (disclosed : Finset (Fin 150)) (attempt : Attempt)
    (honest : AuthorizedRelease (sourceProjection ledger) authorized released)
    (bad : Game.Unauthorized
      (sourceAccepted functions lock validKey ecdsa)
      (fun _ : Attempt => True) (sourceProjection ledger) authorized attempt) :
    sourceJointFailure functions lock validKey ecdsa ledger authorized
      released disclosed attempt := by
  exact unauthorized_under_source_extraction honest
    (source_extraction functions lock validKey ecdsa firstWidth secondWidth
      pinShort nonce0Short nonce1Short noCommitmentDER pinAll nonceAll) bad

/-- The DER-shaped commitment branch is a visible setup exception rather than
an implicit shape premise. Its separate uniform-setup count is established in
`DynamicBonusProbability`; no quantum bound follows here. -/
theorem source_unauthorized_joint_or_bad_setup
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) (released : Set Attempt)
    (disclosed : Finset (Fin 150)) (attempt : Attempt)
    (honest : AuthorizedRelease (sourceProjection ledger) authorized released)
    (bad : Game.Unauthorized
      (sourceAccepted functions lock validKey ecdsa)
      (fun _ : Attempt => True) (sourceProjection ledger) authorized attempt) :
    sourceJointFailure functions lock validKey ecdsa ledger authorized
      released disclosed attempt ∨ badSetup lock := by
  classical
  by_cases good : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false
  · exact Or.inl (source_unauthorized_fresh_or_two_puzzle functions lock
      validKey ecdsa firstWidth secondWidth pinShort nonce0Short nonce1Short
      good pinAll nonceAll ledger authorized released disclosed attempt
      honest bad)
  · obtain ⟨i, hit⟩ := not_forall.mp good
    have valid : DERSyntax.valid (lock.secondCommitment i) = true := by
      cases h : DERSyntax.valid (lock.secondCommitment i) <;> simp_all
    exact Or.inr ⟨i, valid⟩

/-- The source event can be stated against actual HORS setup values from the
same H and R used by its key puzzles and SHA256d calls. The setup equality is
explicit and the extractor does not receive the secret map. This remains a
pointwise statement, not a query-success bound. -/
theorem source_unauthorized_oracle_joint_or_bad_setup
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (secrets : Fin 150 → Bytes)
    (setup : ∀ i, lock.secondCommitment i =
      functions.R (functions.H (secrets i)))
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) (released : Set Attempt)
    (disclosed : Finset (Fin 150)) (attempt : Attempt)
    (honest : AuthorizedRelease (sourceProjection ledger) authorized released)
    (bad : Game.Unauthorized
      (sourceAccepted functions lock validKey ecdsa)
      (fun _ : Attempt => True) (sourceProjection ledger) authorized attempt) :
    (FreshFailure (extractor functions lock validKey ecdsa)
      (fun opening => functions.R (functions.H opening))
      (fun i => functions.R (functions.H (secrets i)))
      (ForbiddenMessage (sourceProjection ledger) authorized)
      disclosed attempt ∨
    TwoPuzzleFailure (extractor functions lock validKey ecdsa)
      (pinRelation functions lock validKey ecdsa)
      (roundRelation functions lock validKey ecdsa)
      functions.H JointOracleReduction.strictDERTarget
      (ForbiddenMessage (sourceProjection ledger) authorized)
      released disclosed attempt) ∨ badSetup lock := by
  have commitmentEq : lock.secondCommitment =
      fun i => functions.R (functions.H (secrets i)) := funext setup
  simpa only [sourceJointFailure, commitmentEq] using
    source_unauthorized_joint_or_bad_setup functions lock validKey ecdsa
      firstWidth secondWidth pinShort nonce0Short nonce1Short pinAll
      nonceAll ledger authorized released disclosed attempt honest bad

end QSB.DynamicSourceGame
