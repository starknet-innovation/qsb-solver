import QSB.DynamicSourceExtractorCausality
import QSB.LedgerBoundRawSource

/-!
Lift the fixed-attempt source extractor dependency inventory through the raw
transaction frontend and the ledger-bound target selector. A failed parser,
scriptSig evaluator, or target binding has an empty downstream inventory.

The raw bytes, lock, evaluator, ledger, key validator, and ECDSA predicate are
held fixed across oracle worlds. `evalScriptSig` and the other supplied
functions may themselves inspect an oracle; their independence, internal query
cost, and correspondence to compiled Bitcoin Core are not established here.
These lists are analytic result dependencies, not operational query traces.
-/
namespace QSB.DynamicRawExtractorCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- Downstream H/R dependencies after the fixed raw parser and scriptSig
evaluator produce a source-model attempt. -/
def rawDependencies (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (raw : DynamicRawSource.RawAttempt) : List Query :=
  match DynamicRawSource.prepare evalScriptSig raw with
  | none => []
  | some attempt =>
      DynamicSourceExtractorCausality.extractorDependencies functions lock
        validKey ecdsa attempt

theorem rawDependencies_length_le_1295
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (raw : DynamicRawSource.RawAttempt) :
    (rawDependencies functions lock validKey ecdsa evalScriptSig raw).length ≤
      1295 := by
  unfold rawDependencies
  split
  · simp
  · exact DynamicSourceExtractorCausality.extractorDependencies_length_le_1295
      functions lock validKey ecdsa _

/-- Result causality of raw-source extraction after fixed preparation. This
does not charge or validate `evalScriptSig` itself. -/
theorem raw_extractor_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (raw : DynamicRawSource.RawAttempt)
    (agree : ∀ q ∈ rawDependencies functions lock validKey ecdsa
      evalScriptSig raw, answer functions' q = answer functions q) :
    DynamicRawSource.extractor functions' lock validKey ecdsa evalScriptSig
      raw =
    DynamicRawSource.extractor functions lock validKey ecdsa evalScriptSig
      raw := by
  unfold DynamicRawSource.extractor
  cases prepared : DynamicRawSource.prepare evalScriptSig raw with
  | none => simp
  | some attempt =>
      have localAgree : ∀ q ∈
          DynamicSourceExtractorCausality.extractorDependencies functions lock
            validKey ecdsa attempt,
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by simpa [rawDependencies, prepared] using mem)
      have extracted := DynamicSourceExtractorCausality.extractor_congr
        functions functions' lock validKey ecdsa attempt localAgree
      simp [extracted]

/-- Dependencies after binding the parsed selected input to one fixed target
outpoint and ledger-supplied locking script. -/
def ledgerDependencies (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output) (target : Game.Outpoint)
    (raw : LedgerBoundRawSource.Submission) : List Query :=
  match LedgerBoundRawSource.bindRaw ledger target raw with
  | none => []
  | some bound => rawDependencies functions lock validKey ecdsa evalScriptSig
      bound

theorem ledgerDependencies_length_le_1295
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output) (target : Game.Outpoint)
    (raw : LedgerBoundRawSource.Submission) :
    (ledgerDependencies functions lock validKey ecdsa evalScriptSig ledger
      target raw).length ≤ 1295 := by
  unfold ledgerDependencies
  split
  · simp
  · exact rawDependencies_length_le_1295 functions lock validKey ecdsa
      evalScriptSig _

/-- Fixed-ledger target binding adds no *modeled* H/R query. The ledger
function's own oracle behavior is an external obligation. -/
theorem ledger_extractor_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output) (target : Game.Outpoint)
    (raw : LedgerBoundRawSource.Submission)
    (agree : ∀ q ∈ ledgerDependencies functions lock validKey ecdsa
      evalScriptSig ledger target raw,
      answer functions' q = answer functions q) :
    LedgerBoundRawSource.extractor functions' lock validKey ecdsa
      evalScriptSig ledger target raw =
    LedgerBoundRawSource.extractor functions lock validKey ecdsa
      evalScriptSig ledger target raw := by
  unfold LedgerBoundRawSource.extractor
  cases bound : LedgerBoundRawSource.bindRaw ledger target raw with
  | none => simp
  | some attempt =>
      have localAgree : ∀ q ∈ rawDependencies functions lock validKey ecdsa
          evalScriptSig attempt,
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by simpa [ledgerDependencies, bound] using mem)
      have extracted := raw_extractor_congr functions functions' lock
        validKey ecdsa evalScriptSig attempt localAgree
      simp [extracted]

end QSB.DynamicRawExtractorCausality
