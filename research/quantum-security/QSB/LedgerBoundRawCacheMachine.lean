import QSB.WorldIndexedRawCacheMachine
import QSB.LedgerBoundRawSource

/-!
Lift the conditional world-indexed raw extractor cache machine through fixed
ledger target binding. The strict raw parser, selected input, target outpoint,
and ledger decide `bindRaw` without an H/R argument. A failed binding halts
with no request; a successful binding reuses the raw extractor cache machine.

The scriptSig charged-trace contract is assumed, not concretely witnessed.
The raw submission, ledger, target, lock, validKey, ECDSA predicate, and
contract stay fixed across oracle worlds and may carry oracle advice. The
≤1697 bound counts explicit classical H/R requests by this machine; costs
hidden in fixed callbacks, ledger resolution, lock construction, scriptSig
implementation, and compiled Bitcoin Core are not established. There is no
coherent-query/QROM claim.
-/
namespace QSB.LedgerBoundRawCacheMachine
open ByteMachine

/-- Fixed external inputs and the assumed all-run scriptSig trace contract. -/
structure FixedInput where
  contract : ScriptSigBoundedCausalContract.Contract
  lock : DynamicCheckedCertificate.Lock
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool
  ledger : Game.Outpoint → Game.Output
  target : Game.Outpoint
  submission : LedgerBoundRawSource.Submission

def rawInput (p : FixedInput) (raw : DynamicRawSource.RawAttempt) :
    WorldIndexedRawCacheMachine.FixedInput where
  contract := p.contract
  lock := p.lock
  validKey := p.validKey
  ecdsa := p.ecdsa
  raw := raw

def ledgerResult (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    Option (Bytes × RoundWitness (Fin 150) Bytes Bytes) :=
  LedgerBoundRawSource.extractor functions p.lock p.validKey p.ecdsa
    (p.contract.eval functions) p.ledger p.target p.submission

/-- Binding failure halts immediately; successful binding delegates to the
already proved raw source cache machine. -/
def machine (p : FixedInput) :
    CausalQueryAlgorithm.Machine CheckedRunCacheMachine.Cache
      (Option (Bytes × RoundWitness (Fin 150) Bytes Bytes)) :=
  match LedgerBoundRawSource.bindRaw p.ledger p.target p.submission with
  | none =>
      { step := fun _ => .inl none
        resume := fun cache _ => cache }
  | some raw => WorldIndexedRawCacheMachine.machine (rawInput p raw)

/-- A failed target binding returns `none` with an empty recorded H/R trace
at every budget and from every initial cache. -/
theorem bind_failure_zero_queries
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (failed : LedgerBoundRawSource.bindRaw p.ledger p.target
      p.submission = none)
    (budget : Nat) (cache : CheckedRunCacheMachine.Cache) :
    CausalQueryAlgorithm.run (machine p) functions budget cache =
      (some none, []) := by
  cases budget <;>
    simp [CausalQueryAlgorithm.run, machine, failed]

/-- A successful target binding uses exactly the raw source cache machine
on the bound spent script and selected raw transaction. -/
theorem bind_success_machine_eq
    (p : FixedInput) (raw : DynamicRawSource.RawAttempt)
    (bound : LedgerBoundRawSource.bindRaw p.ledger p.target p.submission =
      some raw) :
    machine p = WorldIndexedRawCacheMachine.machine (rawInput p raw) := by
  simp [machine, bound]

/-- For fixed ledger binding and an assumed all-run scriptSig contract, the
classical cache machine returns the exact ledger-bound source extractor result
within 1697 explicit H/R requests. A failed binding makes zero requests. -/
theorem run_1697_correct
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run (machine p) functions 1697 []).1 =
        some (ledgerResult p functions) ∧
      (CausalQueryAlgorithm.run (machine p) functions 1697 []).2.length ≤
        1697 := by
  cases bound : LedgerBoundRawSource.bindRaw p.ledger p.target
      p.submission with
  | none =>
      have runEq := bind_failure_zero_queries p functions bound 1697 []
      have resultEq : ledgerResult p functions = none := by
        simp [ledgerResult, LedgerBoundRawSource.extractor, bound]
      exact ⟨by simp [runEq, resultEq], by simp [runEq]⟩
  | some raw =>
      have machineEq := bind_success_machine_eq p raw bound
      have resultEq : ledgerResult p functions =
          WorldIndexedRawCacheMachine.rawResult (rawInput p raw)
            functions := by
        simp [ledgerResult, LedgerBoundRawSource.extractor, bound,
          WorldIndexedRawCacheMachine.rawResult, rawInput]
      rw [machineEq, resultEq]
      exact WorldIndexedRawCacheMachine.run_1697_correct
        (rawInput p raw) functions

end QSB.LedgerBoundRawCacheMachine
