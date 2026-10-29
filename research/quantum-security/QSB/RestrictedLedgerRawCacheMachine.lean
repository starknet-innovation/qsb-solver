import QSB.LedgerBoundRawCacheMachine
import QSB.RestrictedRawCacheMachine

/-!
Fixed-ledger specialization of the classical raw cache machine to the
restricted one-cell direct-push HASH160 scriptSig evaluator. A failed target
binding makes no H/R request. After successful binding, the exact restricted
ledger-bound source extractor result is computed with at most 1297 explicit
classical H/R requests, including raw parser and evaluator failure outcomes.

The submission, ledger, lock, and callbacks are fixed while H/R functions
vary and may carry oracle advice. This is a source-model result for the narrow
scriptSig fragment, not a general QSB spend, compiled Core refinement, or
coherent-query/QROM bound. Callback and setup costs are not charged here.
-/
namespace QSB.RestrictedLedgerRawCacheMachine
open ByteMachine

/-- The generic ledger machine with the concrete restricted scriptSig
contract supplied in its fixed input. -/
def fixedInput (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission) :
    LedgerBoundRawCacheMachine.FixedInput where
  contract := RestrictedScriptSigHash160.contract
  lock := lock
  validKey := validKey
  ecdsa := ecdsa
  ledger := ledger
  target := target
  submission := submission

def machine (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission) :=
  LedgerBoundRawCacheMachine.machine
    (fixedInput lock validKey ecdsa ledger target submission)

def ledgerResult (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission) :=
  LedgerBoundRawSource.extractor functions lock validKey ecdsa
    (RestrictedScriptSigHash160.eval functions) ledger target submission

/-- Rejected ledger target binding halts before the restricted scriptSig or
raw extractor is invoked, at every budget and from every initial cache. -/
theorem bind_failure_zero_queries
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission)
    (functions : JointSourceChecks.Functions)
    (failed : LedgerBoundRawSource.bindRaw ledger target submission = none)
    (budget : Nat) (cache : CheckedRunCacheMachine.Cache) :
    CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions budget cache = (some none, []) := by
  exact LedgerBoundRawCacheMachine.bind_failure_zero_queries
    (fixedInput lock validKey ecdsa ledger target submission)
    functions failed budget cache

/-- A successful fixed-ledger bind reuses the restricted 1297-request raw
machine and returns the exact ledger-bound source extractor result. -/
theorem bind_success_1297_correct
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission)
    (functions : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt)
    (bound : LedgerBoundRawSource.bindRaw ledger target submission =
      some raw) :
    (CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions 1297 []).1 =
        some (ledgerResult functions lock validKey ecdsa ledger target
          submission) ∧
    (CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions 1297 []).2.length ≤ 1297 := by
  have machineEq :
      machine lock validKey ecdsa ledger target submission =
        WorldIndexedRawCacheMachine.machine
          (RestrictedRawCacheMachine.fixedInput lock validKey ecdsa raw) := by
    simpa [machine, fixedInput, LedgerBoundRawCacheMachine.rawInput,
      RestrictedRawCacheMachine.fixedInput] using
      (LedgerBoundRawCacheMachine.bind_success_machine_eq
        (fixedInput lock validKey ecdsa ledger target submission) raw bound)
  have resultEq :
      ledgerResult functions lock validKey ecdsa ledger target submission =
        DynamicRawSource.extractor functions lock validKey ecdsa
          (RestrictedScriptSigHash160.eval functions) raw := by
    simp [ledgerResult, LedgerBoundRawSource.extractor, bound]
  simpa only [machineEq, resultEq] using
    (RestrictedRawCacheMachine.run_1297_correct
      lock validKey ecdsa raw functions)

/-- Both target-binding outcomes return the exact restricted ledger-bound
result within 1297 actual classical H/R requests. -/
theorem run_1297_correct
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission)
    (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions 1297 []).1 =
        some (ledgerResult functions lock validKey ecdsa ledger target
          submission) ∧
    (CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions 1297 []).2.length ≤ 1297 := by
  cases bound : LedgerBoundRawSource.bindRaw ledger target submission with
  | none =>
      have runEq := bind_failure_zero_queries lock validKey ecdsa ledger
        target submission functions bound 1297 []
      have resultEq : ledgerResult functions lock validKey ecdsa ledger
          target submission = none := by
        simp [ledgerResult, LedgerBoundRawSource.extractor, bound]
      exact ⟨by simp [runEq, resultEq], by simp [runEq]⟩
  | some raw =>
      exact bind_success_1297_correct lock validKey ecdsa ledger target
        submission functions raw bound

end QSB.RestrictedLedgerRawCacheMachine
