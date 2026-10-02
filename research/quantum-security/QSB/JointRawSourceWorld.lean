import QSB.LedgerBoundRawSource

/-!
Instantiate the one-world joint-oracle reduction with the ledger-bound raw
source game. All transaction, ledger, checker, disclosure, and output data may
depend on the same sampled H/R world. This is still a source-model game:
arbitrary scriptSig evaluation, real ECDSA, compiled Core acceptance, and a
shared coherent-query bound remain outside this theorem.
-/
namespace QSB.JointRawSourceWorld
open ByteMachine
open MeasureTheory

variable {Ω : Type*}

structure World (Ω : Type*) where
  functions : Ω → JointSourceChecks.Functions
  secrets : Ω → Fin 150 → Bytes
  lock : Ω → DynamicCheckedCertificate.Lock
  validKey : Ω → Bytes → Bool
  ecdsa : Ω → Bytes → Bytes → Bytes → Bool
  evalScriptSig : Ω → DynamicRawSource.EvalScriptSig
  ledger : Ω → Game.Outpoint → Game.Output
  target : Ω → Game.Outpoint
  authorized : Ω → Set Game.Projection
  released : Ω → Set LedgerBoundRawSource.Submission
  disclosed : Ω → Finset (Fin 150)
  output : Ω → LedgerBoundRawSource.Submission

def experiment (w : World Ω) :
    JointOracleReduction.Experiment Ω (Fin 150)
      LedgerBoundRawSource.Submission where
  functions := w.functions
  secrets := w.secrets
  accepted := fun ω => LedgerBoundRawSource.sourceAccepted
    (w.functions ω) (w.lock ω) (w.validKey ω) (w.ecdsa ω)
    (w.evalScriptSig ω) (w.ledger ω) (w.target ω)
  spendsTarget := fun ω => LedgerBoundRawSource.spendsTarget (w.target ω)
  projection := fun ω => LedgerBoundRawSource.projection (w.ledger ω)
  authorized := w.authorized
  extractor := fun ω => LedgerBoundRawSource.extractor
    (w.functions ω) (w.lock ω) (w.validKey ω) (w.ecdsa ω)
    (w.evalScriptSig ω) (w.ledger ω) (w.target ω)
  pinRelation := fun ω => LedgerBoundRawSource.pinRelation
    (w.functions ω) (w.lock ω) (w.validKey ω) (w.ecdsa ω)
    (w.evalScriptSig ω) (w.ledger ω) (w.target ω)
  roundRelation := fun ω => LedgerBoundRawSource.roundRelation
    (w.functions ω) (w.lock ω) (w.validKey ω) (w.ecdsa ω)
    (w.evalScriptSig ω) (w.ledger ω) (w.target ω)
  output := w.output
  released := w.released
  disclosed := w.disclosed

/-- The lock's public second-round commitments are the same-world oracle
images of the sampled secrets. This equality cannot be dropped when the
generic game's commitments are substituted for those checked by the script. -/
def SetupMatches (w : World Ω) : Prop :=
  ∀ ω i, (w.lock ω).secondCommitment i =
    (w.functions ω).R ((w.functions ω).H (w.secrets ω i))

theorem commitments_eq_lock (w : World Ω) (setupEq : SetupMatches w)
    (ω : Ω) :
    JointOracleReduction.commitments (experiment w) ω =
      (w.lock ω).secondCommitment := by
  funext i
  exact (setupEq ω i).symm

/-- The generic terminal event is exactly the concrete raw-source event,
including the ledger-derived projection for this same world. -/
theorem jointFailure_iff_source (w : World Ω)
    (setupEq : SetupMatches w) (ω : Ω) :
    JointOracleReduction.jointFailure (experiment w) ω ↔
      LedgerBoundRawSource.sourceJointFailure (w.functions ω) (w.lock ω)
        (w.validKey ω) (w.ecdsa ω) (w.evalScriptSig ω)
        (w.ledger ω) (w.target ω) (w.authorized ω)
        (w.released ω) (w.disclosed ω) (w.output ω) := by
  rw [JointOracleReduction.jointFailure,
    commitments_eq_lock w setupEq ω]
  rfl

/-- Every unauthorized accepted source-model raw submission lies in the
single joint event or in the DER-shaped setup exception. The proof does not
replace source acceptance with consensus acceptance. -/
theorem unauthorized_joint_or_bad_setup (w : World Ω)
    (setupEq : SetupMatches w) (ω : Ω)
    (firstWidth : ∀ i, ((w.lock ω).firstCommitment i).length = 20)
    (secondWidth : ∀ i, ((w.lock ω).secondCommitment i).length = 20)
    (pinShort : (w.lock ω).pin.length < 76)
    (nonce0Short : (w.lock ω).nonce0.length < 76)
    (nonce1Short : (w.lock ω).nonce1.length < 76)
    (pinAll : (w.lock ω).pin.getLast? = some 0x01)
    (nonceAll : (w.lock ω).nonce1.getLast? = some 0x01)
    (honest : AuthorizedRelease
      (LedgerBoundRawSource.projection (w.ledger ω))
      (w.authorized ω) (w.released ω))
    (bad : JointOracleReduction.unauthorized (experiment w) ω) :
    JointOracleReduction.jointFailure (experiment w) ω ∨
      DynamicSourceGame.badSetup (w.lock ω) := by
  have sourceBad : Game.Unauthorized
      (LedgerBoundRawSource.sourceAccepted (w.functions ω) (w.lock ω)
        (w.validKey ω) (w.ecdsa ω) (w.evalScriptSig ω)
        (w.ledger ω) (w.target ω))
      (LedgerBoundRawSource.spendsTarget (w.target ω))
      (LedgerBoundRawSource.projection (w.ledger ω))
      (w.authorized ω) (w.output ω) := by
    simpa [JointOracleReduction.unauthorized, experiment] using bad
  rcases LedgerBoundRawSource.source_unauthorized_joint_or_bad_setup
      (w.functions ω) (w.lock ω) (w.validKey ω) (w.ecdsa ω)
      (w.evalScriptSig ω) (w.ledger ω) (w.target ω)
      firstWidth secondWidth pinShort nonce0Short nonce1Short
      pinAll nonceAll (w.authorized ω) (w.released ω)
      (w.disclosed ω) (w.output ω) honest sourceBad with hit | badSetup
  · exact Or.inl ((jointFailure_iff_source w setupEq ω).2 hit)
  · exact Or.inr badSetup

/-- A single bound on the same-world joint event plus a bound on the setup
exception suffices for this raw *source-model* game. Neither bound is supplied
here: in particular, `εjoint` is not split into independent query budgets. -/
theorem unauthorized_measure_bound [MeasurableSpace Ω]
    (w : World Ω) (μ : Measure Ω)
    (setupEq : SetupMatches w)
    (firstWidth : ∀ ω i, ((w.lock ω).firstCommitment i).length = 20)
    (secondWidth : ∀ ω i, ((w.lock ω).secondCommitment i).length = 20)
    (pinShort : ∀ ω, (w.lock ω).pin.length < 76)
    (nonce0Short : ∀ ω, (w.lock ω).nonce0.length < 76)
    (nonce1Short : ∀ ω, (w.lock ω).nonce1.length < 76)
    (pinAll : ∀ ω, (w.lock ω).pin.getLast? = some 0x01)
    (nonceAll : ∀ ω, (w.lock ω).nonce1.getLast? = some 0x01)
    (honest : ∀ ω, AuthorizedRelease
      (LedgerBoundRawSource.projection (w.ledger ω))
      (w.authorized ω) (w.released ω))
    (εjoint εsetup : ENNReal)
    (jointBound : μ {ω | JointOracleReduction.jointFailure
      (experiment w) ω} ≤ εjoint)
    (setupBound : μ {ω | DynamicSourceGame.badSetup (w.lock ω)} ≤
      εsetup) :
    μ {ω | JointOracleReduction.unauthorized (experiment w) ω} ≤
      εjoint + εsetup := by
  have cover :
      {ω | JointOracleReduction.unauthorized (experiment w) ω} ⊆
        {ω | JointOracleReduction.jointFailure (experiment w) ω} ∪
          {ω | DynamicSourceGame.badSetup (w.lock ω)} := by
    intro ω bad
    exact unauthorized_joint_or_bad_setup w setupEq ω
      (firstWidth ω) (secondWidth ω) (pinShort ω)
      (nonce0Short ω) (nonce1Short ω) (pinAll ω) (nonceAll ω)
      (honest ω) bad
  exact (measure_mono cover).trans
    ((measure_union_le _ _).trans (add_le_add jointBound setupBound))

/-- This event uses an external predicate for consensus acceptance of the
selected target input. Target identification and authorization projection are
the source-model functions below. A real Core-to-Lean theorem must relate all
three to the same transaction and ledger state. -/
def coreUnauthorized (w : World Ω)
    (coreAcceptedTarget : Ω → LedgerBoundRawSource.Submission → Prop)
    (ω : Ω) : Prop :=
  Game.Unauthorized (coreAcceptedTarget ω)
    (LedgerBoundRawSource.spendsTarget (w.target ω))
    (LedgerBoundRawSource.projection (w.ledger ω))
    (w.authorized ω) (w.output ω)

/-- Once actual selected-target consensus acceptance is shown to imply the
checked raw-source run for the same bytes, selected input, ledger, and oracle
world, the source measure bound transfers without a separate probability
loss. This theorem does not identify the source-defined target/projection
functions with Core's consensus and UTXO state; that belongs in `coreRefines`
and the chosen external acceptance predicate. The joint-query bound is also
an explicit premise. -/
theorem core_unauthorized_measure_bound [MeasurableSpace Ω]
    (w : World Ω) (μ : Measure Ω)
    (coreAcceptedTarget : Ω → LedgerBoundRawSource.Submission → Prop)
    (coreRefines : ∀ ω raw, coreAcceptedTarget ω raw →
      LedgerBoundRawSource.sourceAccepted (w.functions ω) (w.lock ω)
        (w.validKey ω) (w.ecdsa ω) (w.evalScriptSig ω)
        (w.ledger ω) (w.target ω) raw)
    (setupEq : SetupMatches w)
    (firstWidth : ∀ ω i, ((w.lock ω).firstCommitment i).length = 20)
    (secondWidth : ∀ ω i, ((w.lock ω).secondCommitment i).length = 20)
    (pinShort : ∀ ω, (w.lock ω).pin.length < 76)
    (nonce0Short : ∀ ω, (w.lock ω).nonce0.length < 76)
    (nonce1Short : ∀ ω, (w.lock ω).nonce1.length < 76)
    (pinAll : ∀ ω, (w.lock ω).pin.getLast? = some 0x01)
    (nonceAll : ∀ ω, (w.lock ω).nonce1.getLast? = some 0x01)
    (honest : ∀ ω, AuthorizedRelease
      (LedgerBoundRawSource.projection (w.ledger ω))
      (w.authorized ω) (w.released ω))
    (εjoint εsetup : ENNReal)
    (jointBound : μ {ω | JointOracleReduction.jointFailure
      (experiment w) ω} ≤ εjoint)
    (setupBound : μ {ω | DynamicSourceGame.badSetup (w.lock ω)} ≤
      εsetup) :
    μ {ω | coreUnauthorized w coreAcceptedTarget ω} ≤
      εjoint + εsetup := by
  have inclusion :
      {ω | coreUnauthorized w coreAcceptedTarget ω} ⊆
        {ω | JointOracleReduction.unauthorized (experiment w) ω} := by
    intro ω bad
    exact ⟨coreRefines ω (w.output ω) bad.1, bad.2.1, bad.2.2⟩
  exact (measure_mono inclusion).trans
    (unauthorized_measure_bound w μ setupEq firstWidth secondWidth
      pinShort nonce0Short nonce1Short pinAll nonceAll honest
      εjoint εsetup jointBound setupBound)

end QSB.JointRawSourceWorld
