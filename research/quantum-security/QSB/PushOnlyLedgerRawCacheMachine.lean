import QSB.LedgerBoundRawCacheMachine
import QSB.PushOnlyRawCacheMachine

/-!
Fixed-ledger specialization of the classical raw response cache to the
query-free push-only scriptSig evaluator. A failed target bind makes no H/R
request. A successful bind computes the exact optional ledger-bound source
extractor result within 1295 explicit classical H/R requests, including raw
parser and scriptSig failures.

The submission, ledger, lock, and callbacks stay fixed while H/R vary and may
contain oracle advice. The push-only grammar excludes arbitrary scriptSig and
signature opcodes. No compiled-Core refinement, hidden callback/setup charge,
coherent-query bound, or full QSB security result follows.
-/
namespace QSB.PushOnlyLedgerRawCacheMachine
open ByteMachine

/-- Fixed ledger input with the concrete push-only scriptSig contract. -/
def fixedInput (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission) :
    LedgerBoundRawCacheMachine.FixedInput where
  contract := PushOnlyScriptSig.contract
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
    PushOnlyScriptSig.eval ledger target submission

/-- Rejected target binding halts before the push-only scriptSig or raw
extractor, at every budget and from every initial cache. -/
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

/-- A successful fixed-ledger bind reuses the push-only 1295-request raw
machine and returns the exact ledger-bound source extractor result. -/
theorem bind_success_1295_correct
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
      functions 1295 []).1 =
        some (ledgerResult functions lock validKey ecdsa ledger target
          submission) ∧
    (CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions 1295 []).2.length ≤ 1295 := by
  have machineEq :
      machine lock validKey ecdsa ledger target submission =
        WorldIndexedRawCacheMachine.machine
          (PushOnlyRawCacheMachine.fixedInput lock validKey ecdsa raw) := by
    simpa [machine, fixedInput, LedgerBoundRawCacheMachine.rawInput,
      PushOnlyRawCacheMachine.fixedInput] using
      (LedgerBoundRawCacheMachine.bind_success_machine_eq
        (fixedInput lock validKey ecdsa ledger target submission) raw bound)
  have resultEq :
      ledgerResult functions lock validKey ecdsa ledger target submission =
        DynamicRawSource.extractor functions lock validKey ecdsa
          PushOnlyScriptSig.eval raw := by
    simp [ledgerResult, LedgerBoundRawSource.extractor, bound]
  simpa only [machineEq, resultEq] using
    (PushOnlyRawCacheMachine.run_1295_correct
      lock validKey ecdsa raw functions)

/-- Both target-binding outcomes return the exact push-only ledger-bound
result within 1295 actual classical H/R requests. -/
theorem run_1295_correct
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (submission : LedgerBoundRawSource.Submission)
    (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions 1295 []).1 =
        some (ledgerResult functions lock validKey ecdsa ledger target
          submission) ∧
    (CausalQueryAlgorithm.run
      (machine lock validKey ecdsa ledger target submission)
      functions 1295 []).2.length ≤ 1295 := by
  cases bound : LedgerBoundRawSource.bindRaw ledger target submission with
  | none =>
      have runEq := bind_failure_zero_queries lock validKey ecdsa ledger
        target submission functions bound 1295 []
      have resultEq : ledgerResult functions lock validKey ecdsa ledger
          target submission = none := by
        simp [ledgerResult, LedgerBoundRawSource.extractor, bound]
      exact ⟨by simp [runEq, resultEq], by simp [runEq]⟩
  | some raw =>
      exact bind_success_1295_correct lock validKey ecdsa ledger target
        submission functions raw bound

end QSB.PushOnlyLedgerRawCacheMachine
