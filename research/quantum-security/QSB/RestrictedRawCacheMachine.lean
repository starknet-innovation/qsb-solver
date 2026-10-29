import QSB.RestrictedScriptSigHash160
import QSB.WorldIndexedRawCacheMachine

/-!
Specialize the conditional raw source cache to the concrete, narrow
`RestrictedScriptSigHash160` evaluator. A parsed selected scriptSig contributes
either zero H/R dependencies (no valid direct-push/HASH160 prefix) or exactly
H(opening) followed by R(H(opening)); the fixed-attempt extractor contributes
at most 1295 more. The resulting machine computes the exact restricted raw
extractor result with at most 1297 explicit classical H/R requests on every
outcome, including parser and evaluator failure.

The raw bytes, lock, key validator, and ECDSA predicate stay fixed across
oracle worlds and may carry oracle advice. The restricted evaluator returns
only a one-cell stack and is not an implementation of arbitrary bare scriptSig
or the QSB unlocking program. This result does not establish compiled Bitcoin
Core behavior, hidden callback costs, or coherent-query/QROM accounting.
-/
namespace QSB.RestrictedRawCacheMachine
open ByteMachine

/-- Fixed raw input with the concrete restricted scriptSig contract. -/
def fixedInput (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt) :
    WorldIndexedRawCacheMachine.FixedInput where
  contract := RestrictedScriptSigHash160.contract
  lock := lock
  validKey := validKey
  ecdsa := ecdsa
  raw := raw

/-- Strict decoding and selected-input lookup expose either no scriptSig
queries or the restricted evaluator's two adaptive hash queries. -/
theorem scriptSigDependencies_length_le_2
    (functions : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt) :
    (WorldIndexedScriptSigExtractor.scriptSigDependencies
      RestrictedScriptSigHash160.contract.toContract functions raw).length ≤
      2 := by
  unfold WorldIndexedScriptSigExtractor.scriptSigDependencies
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => simp
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      cases selectedSig : DynamicRawSource.scriptSigAt tx raw.selected with
      | none => simp [tx, selectedSig]
      | some scriptSig =>
          cases foundPrefix : RestrictedScriptSigHash160.hashPrefix scriptSig with
          | none =>
              simp [RestrictedScriptSigHash160.contract,
                RestrictedScriptSigHash160.queries_reached,
                tx, selectedSig, foundPrefix]
          | some pair =>
              obtain ⟨opening, rest⟩ := pair
              simp [RestrictedScriptSigHash160.contract,
                RestrictedScriptSigHash160.queries_reached,
                tx, selectedSig, foundPrefix]

/-- Two scriptSig requests plus the existing 1295-entry downstream inventory. -/
theorem trace_length_le_1297
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt)
    (functions : JointSourceChecks.Functions) :
    (WorldIndexedRawCacheMachine.trace
      (fixedInput lock validKey ecdsa raw) functions).length ≤ 1297 := by
  have first := scriptSigDependencies_length_le_2 functions raw
  have second := ScriptSigAllRunRawBound.downstreamDependencies_length_le_1295
    RestrictedScriptSigHash160.contract functions lock validKey ecdsa raw
  change (WorldIndexedScriptSigExtractor.combinedDependencies
    RestrictedScriptSigHash160.contract.toContract functions lock validKey
      ecdsa raw).length ≤ 1297
  simp only [WorldIndexedScriptSigExtractor.combinedDependencies,
    List.length_append]
  omega

/-- The concrete restricted evaluator's raw extractor result is returned by
one response-cache run within 1297 explicit classical H/R requests. -/
theorem run_1297_correct
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt)
    (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run
      (WorldIndexedRawCacheMachine.machine
        (fixedInput lock validKey ecdsa raw)) functions 1297 []).1 =
      some (DynamicRawSource.extractor functions lock validKey ecdsa
        (RestrictedScriptSigHash160.eval functions) raw) ∧
    (CausalQueryAlgorithm.run
      (WorldIndexedRawCacheMachine.machine
        (fixedInput lock validKey ecdsa raw)) functions 1297 []).2.length ≤
      1297 := by
  let p := fixedInput lock validKey ecdsa raw
  obtain ⟨out, halted⟩ :=
    WorldIndexedRawCacheMachine.run_halts_of_enough p functions 1297 []
      (WorldIndexedRawCacheMachine.goodCache_nil p functions) (by
        simpa [p] using trace_length_le_1297 lock validKey ecdsa raw functions)
  have correct := WorldIndexedRawCacheMachine.halted_result_correct p
    functions 1297 [] out (by simp [CheckedRunCacheMachine.CacheSound])
      halted
  have resultEq : WorldIndexedRawCacheMachine.rawResult p functions =
      DynamicRawSource.extractor functions lock validKey ecdsa
        (RestrictedScriptSigHash160.eval functions) raw := rfl
  exact ⟨by simpa [p, resultEq, correct] using halted,
    CausalQueryAlgorithm.run_length_le
      (WorldIndexedRawCacheMachine.machine p) functions 1297 []⟩

end QSB.RestrictedRawCacheMachine
