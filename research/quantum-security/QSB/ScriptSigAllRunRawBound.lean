import QSB.ScriptSigBoundedCausalContract
import QSB.WorldIndexedScriptSigExtractor
import QSB.DynamicSourceExtractorCacheMachine

/-!
Lift the all-run supplied scriptSig event-list cost assumption through strict raw
preparation and the already bounded fixed-attempt extractor inventory. This
gives an unconditional length bound on an analytic H/R dependency list,
including failed scriptSig evaluations. It does not establish a concrete
evaluator, actual oracle requests, or compiled-Core behavior.
-/
namespace QSB.ScriptSigAllRunRawBound
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- The strict parser and selected-input lookup either skip scriptSig
evaluation or expose the charged-prefix trace, bounded on every result. -/
theorem scriptSigDependencies_length_le_402
    (contract : ScriptSigBoundedCausalContract.Contract)
    (functions : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt) :
    (WorldIndexedScriptSigExtractor.scriptSigDependencies
      contract.toContract functions raw).length ≤ 402 := by
  unfold WorldIndexedScriptSigExtractor.scriptSigDependencies
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => simp
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      cases selectedSig : DynamicRawSource.scriptSigAt tx raw.selected with
      | none => simp [tx, selectedSig]
      | some scriptSig =>
          have bound := ScriptSigBoundedCausalContract.trace_length_le_402
            contract functions tx raw.selected scriptSig
          simpa [ScriptSigBoundedCausalContract.trace, tx, selectedSig]
            using bound

/-- The fixed raw parser and input selection preserve the scriptSig trace's
one-step prefix causality, including parser failures. -/
theorem scriptSigDependencies_prefix
    (contract : ScriptSigBoundedCausalContract.Contract)
    (functions functions' : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt) (k : Nat)
    (within : k < (WorldIndexedScriptSigExtractor.scriptSigDependencies
      contract.toContract functions raw).length)
    (agree : ∀ q ∈ (WorldIndexedScriptSigExtractor.scriptSigDependencies
      contract.toContract functions raw).take k,
      answer functions' q = answer functions q) :
    (WorldIndexedScriptSigExtractor.scriptSigDependencies
      contract.toContract functions' raw).take (k + 1) =
    (WorldIndexedScriptSigExtractor.scriptSigDependencies
      contract.toContract functions raw).take (k + 1) := by
  unfold WorldIndexedScriptSigExtractor.scriptSigDependencies at within agree ⊢
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => simp [decoded] at within
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      cases selectedSig : DynamicRawSource.scriptSigAt tx raw.selected with
      | none => simp [tx, selectedSig]
      | some scriptSig =>
          have localWithin : k <
              (ScriptSigBoundedCausalContract.trace contract.toContract
                functions tx raw.selected scriptSig).length := by
            simpa [ScriptSigBoundedCausalContract.trace, decoded, tx,
              selectedSig]
              using within
          have localAgree : ∀ q ∈
              (ScriptSigBoundedCausalContract.trace contract.toContract
                functions tx raw.selected scriptSig).take k,
              answer functions' q = answer functions q := by
            intro q mem
            exact agree q (by
              simpa [ScriptSigBoundedCausalContract.trace, decoded, tx,
                selectedSig]
                using mem)
          have samePrefix := ScriptSigBoundedCausalContract.trace_prefix
            contract functions functions' tx raw.selected scriptSig k
            localWithin localAgree
          simpa [ScriptSigBoundedCausalContract.trace, decoded, tx,
            selectedSig]
            using samePrefix

/-- The downstream extractor is skipped when raw preparation fails; otherwise
its fixed-attempt inventory contributes at most 1295 entries. -/
theorem downstreamDependencies_length_le_1295
    (contract : ScriptSigBoundedCausalContract.Contract)
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt) :
    (WorldIndexedScriptSigExtractor.downstreamDependencies
      contract.toContract functions lock validKey ecdsa raw).length ≤ 1295 := by
  unfold WorldIndexedScriptSigExtractor.downstreamDependencies
  cases prepared : DynamicRawSource.prepare (contract.eval functions) raw with
  | none => simp
  | some attempt =>
      simpa [prepared] using
        (DynamicSourceExtractorCausality.extractorDependencies_length_le_1295
          functions lock validKey ecdsa attempt)

/-- Every raw submission's analytic inventory has at most 1697 H/R entries,
regardless of parser, evaluator, or downstream extraction failure. -/
theorem combinedDependencies_length_le_1697
    (contract : ScriptSigBoundedCausalContract.Contract)
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt) :
    (WorldIndexedScriptSigExtractor.combinedDependencies
      contract.toContract functions lock validKey ecdsa raw).length ≤ 1697 := by
  have first := scriptSigDependencies_length_le_402 contract functions raw
  have second := downstreamDependencies_length_le_1295 contract functions
    lock validKey ecdsa raw
  simp only [WorldIndexedScriptSigExtractor.combinedDependencies,
    List.length_append]
  omega

/-- The concatenated raw inventory is prefix-causal: the first segment fixes
raw preparation, after which the fixed-attempt extractor prefix theorem
applies. This still describes an analytic dependency list. -/
theorem combinedDependencies_prefix
    (contract : ScriptSigBoundedCausalContract.Contract)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt) :
    FullCheckedRunPrefixCausality.PrefixCausal (fun functions =>
      WorldIndexedScriptSigExtractor.combinedDependencies
        contract.toContract functions lock validKey ecdsa raw) := by
  let head : JointSourceChecks.Functions → List Query := fun functions =>
    WorldIndexedScriptSigExtractor.scriptSigDependencies
      contract.toContract functions raw
  let tail : JointSourceChecks.Functions → List Query := fun functions =>
    WorldIndexedScriptSigExtractor.downstreamDependencies
      contract.toContract functions lock validKey ecdsa raw
  have headPrefix : FullCheckedRunPrefixCausality.PrefixCausal head := by
    intro functions functions' k within agree
    exact scriptSigDependencies_prefix contract functions functions' raw k
      (by simpa [head] using within)
      (by simpa [head] using agree)
  have headCongr : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      head functions' = head functions := by
    intro functions functions' agree
    exact WorldIndexedScriptSigExtractor.scriptSigDependencies_congr
      contract.toContract functions functions' raw
      (by simpa [head] using agree)
  have tailPrefix : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      ∀ k, k < (tail functions).length →
        (∀ q ∈ (tail functions).take k,
          answer functions' q = answer functions q) →
        (tail functions').take (k + 1) =
          (tail functions).take (k + 1) := by
    intro functions functions' headAgree k within agree
    have preparedEq := WorldIndexedScriptSigExtractor.prepare_congr
      contract.toContract functions functions' raw
      (by simpa [head] using headAgree)
    cases prepared : DynamicRawSource.prepare (contract.eval functions) raw with
    | none =>
        have prepared' : DynamicRawSource.prepare
            (contract.eval functions') raw = none := by
          rw [preparedEq, prepared]
        simp [tail, WorldIndexedScriptSigExtractor.downstreamDependencies,
          prepared] at within
    | some attempt =>
        have prepared' : DynamicRawSource.prepare
            (contract.eval functions') raw = some attempt := by
          rw [preparedEq, prepared]
        have localWithin : k <
            (DynamicSourceExtractorCausality.extractorDependencies functions
              lock validKey ecdsa attempt).length := by
          simpa [tail, WorldIndexedScriptSigExtractor.downstreamDependencies,
            prepared] using within
        have localAgree : ∀ q ∈
            (DynamicSourceExtractorCausality.extractorDependencies functions
              lock validKey ecdsa attempt).take k,
            answer functions' q = answer functions q := by
          intro q mem
          exact agree q (by
            simpa [tail,
              WorldIndexedScriptSigExtractor.downstreamDependencies,
              prepared] using mem)
        have samePrefix :=
          DynamicSourceExtractorCacheMachine.extractorDependencies_prefix
            lock validKey ecdsa attempt functions functions' k localWithin
            localAgree
        simpa [tail, WorldIndexedScriptSigExtractor.downstreamDependencies,
          prepared, prepared'] using samePrefix
  have combined := FullCheckedRunPrefixCausality.append_prefix head tail
    headPrefix headCongr tailPrefix
  simpa [head, tail, WorldIndexedScriptSigExtractor.combinedDependencies]
    using combined

end QSB.ScriptSigAllRunRawBound
