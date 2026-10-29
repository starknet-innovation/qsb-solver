import QSB.PushOnlyScriptSig
import QSB.WorldIndexedRawCacheMachine

/-!
Specialize the conditional raw source response cache to the concrete
`PushOnlyScriptSig` evaluator. Strict parsing and selected-input lookup either
skip scriptSig or invoke an evaluator with no H/R dependencies. The fixed
attempt extractor contributes at most 1295 analytic dependencies, so one
cache machine returns the exact optional raw extractor result within 1295
actual classical H/R requests on every outcome.

The raw bytes, lock, key validator, and ECDSA predicate stay fixed across
oracle worlds and may contain oracle advice. This push-only grammar excludes
signature checks and arbitrary scriptSig opcodes; no compiled Bitcoin Core
refinement, hidden callback/setup query charge, coherent-query budget, or QROM
security claim follows.
-/
namespace QSB.PushOnlyRawCacheMachine
open ByteMachine

/-- Fixed raw input with the concrete, query-free push-only scriptSig
contract. -/
def fixedInput (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt) :
    WorldIndexedRawCacheMachine.FixedInput where
  contract := PushOnlyScriptSig.contract
  lock := lock
  validKey := validKey
  ecdsa := ecdsa
  raw := raw

/-- The selected scriptSig contributes no attributed H/R dependency,
including when strict parsing, input selection, or push-only execution fails. -/
theorem scriptSigDependencies_nil
    (functions : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt) :
    WorldIndexedScriptSigExtractor.scriptSigDependencies
      PushOnlyScriptSig.contract.toContract functions raw = [] := by
  unfold WorldIndexedScriptSigExtractor.scriptSigDependencies
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => rfl
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      cases selectedSig : DynamicRawSource.scriptSigAt tx raw.selected with
      | none => simp [tx, selectedSig]
      | some scriptSig =>
          simpa [PushOnlyScriptSig.contract, tx, selectedSig] using
            PushOnlyScriptSig.queries_reached_nil scriptSig

/-- The complete raw inventory has only the downstream 1295-entry allowance. -/
theorem trace_length_le_1295
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt)
    (functions : JointSourceChecks.Functions) :
    (WorldIndexedRawCacheMachine.trace
      (fixedInput lock validKey ecdsa raw) functions).length ≤ 1295 := by
  have first := scriptSigDependencies_nil functions raw
  have second := ScriptSigAllRunRawBound.downstreamDependencies_length_le_1295
    PushOnlyScriptSig.contract functions lock validKey ecdsa raw
  change (WorldIndexedScriptSigExtractor.combinedDependencies
    PushOnlyScriptSig.contract.toContract functions lock validKey ecdsa raw).length
      ≤ 1295
  simpa [WorldIndexedScriptSigExtractor.combinedDependencies, first] using
    second

/-- The concrete push-only evaluator's exact optional raw extractor result
is returned within 1295 actual classical H/R requests. -/
theorem run_1295_correct
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt)
    (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run
      (WorldIndexedRawCacheMachine.machine
        (fixedInput lock validKey ecdsa raw)) functions 1295 []).1 =
      some (DynamicRawSource.extractor functions lock validKey ecdsa
        PushOnlyScriptSig.eval raw) ∧
    (CausalQueryAlgorithm.run
      (WorldIndexedRawCacheMachine.machine
        (fixedInput lock validKey ecdsa raw)) functions 1295 []).2.length ≤
      1295 := by
  let p := fixedInput lock validKey ecdsa raw
  obtain ⟨out, halted⟩ :=
    WorldIndexedRawCacheMachine.run_halts_of_enough p functions 1295 []
      (WorldIndexedRawCacheMachine.goodCache_nil p functions) (by
        simpa [p] using trace_length_le_1295 lock validKey ecdsa raw functions)
  have correct := WorldIndexedRawCacheMachine.halted_result_correct p
    functions 1295 [] out (by simp [CheckedRunCacheMachine.CacheSound])
      halted
  have resultEq : WorldIndexedRawCacheMachine.rawResult p functions =
      DynamicRawSource.extractor functions lock validKey ecdsa
        PushOnlyScriptSig.eval raw := rfl
  exact ⟨by simpa [p, resultEq, correct] using halted,
    CausalQueryAlgorithm.run_length_le
      (WorldIndexedRawCacheMachine.machine p) functions 1295 []⟩

end QSB.PushOnlyRawCacheMachine
