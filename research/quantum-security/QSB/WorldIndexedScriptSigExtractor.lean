import QSB.ScriptSigTraceContract
import QSB.DynamicSourceExtractorCausality

/-!
Compose an explicitly functions-indexed scriptSig evaluator contract with the
fixed-attempt source extractor. The submitted raw bytes select the parsed
transaction and scriptSig; a successful evaluator supplies the lock-entry
stack. The trace is an analytic H/R dependency inventory, not an effectful
oracle machine or compiled Bitcoin Core refinement.

The locking script, key validator, and ECDSA predicate are fixed across
functions. The scriptSig contract must separately establish trace completeness,
its own causal behavior, and the successful 201-opcode cap. Its current cap
does not cover failed evaluations, so the 1697 bound below requires successful
raw preparation. External predicate internals and lock construction remain
unaccounted.
-/
namespace QSB.WorldIndexedScriptSigExtractor
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- Queries attributed to the selected scriptSig after strict transaction
decoding. A parser or selected-input failure does not call the evaluator. -/
def scriptSigDependencies (contract : ScriptSigTraceContract.Contract)
    (functions : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt) : List Query :=
  match TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => []
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      match DynamicRawSource.scriptSigAt tx raw.selected with
      | none => []
      | some scriptSig =>
          ScriptSigTraceContract.queries
            (contract.reached functions tx raw.selected scriptSig)

/-- Oracle agreement on the attributed scriptSig queries preserves the
evaluator's optional stack and therefore the prepared source attempt. -/
theorem prepare_congr
    (contract : ScriptSigTraceContract.Contract)
    (functions functions' : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt)
    (agree : ∀ q ∈ scriptSigDependencies contract functions raw,
      answer functions' q = answer functions q) :
    DynamicRawSource.prepare (contract.eval functions') raw =
    DynamicRawSource.prepare (contract.eval functions) raw := by
  unfold DynamicRawSource.prepare
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => simp
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      cases selectedSig : DynamicRawSource.scriptSigAt tx raw.selected with
      | none =>
          have selectedSig' : DynamicRawSource.scriptSigAt
              (TransactionEnvelopeWire.fields envelope) raw.selected = none :=
            by simpa [tx] using selectedSig
          simp [selectedSig']
      | some scriptSig =>
          have localAgree : ∀ q ∈ ScriptSigTraceContract.queries
              (contract.reached functions tx raw.selected scriptSig),
              answer functions' q = answer functions q := by
            intro q mem
            exact agree q (by
              simpa [scriptSigDependencies, decoded, tx, selectedSig]
                using mem)
          have evalEq := contract.resultCongr functions functions' tx
            raw.selected scriptSig localAgree
          simp [tx, selectedSig, evalEq]

/-- The selected scriptSig's adaptive query list is itself stable under
agreement on its attributed oracle replies. -/
theorem scriptSigDependencies_congr
    (contract : ScriptSigTraceContract.Contract)
    (functions functions' : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt)
    (agree : ∀ q ∈ scriptSigDependencies contract functions raw,
      answer functions' q = answer functions q) :
    scriptSigDependencies contract functions' raw =
      scriptSigDependencies contract functions raw := by
  unfold scriptSigDependencies
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => rfl
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      cases selectedSig : DynamicRawSource.scriptSigAt tx raw.selected with
      | none =>
          have selectedSig' : DynamicRawSource.scriptSigAt
              (TransactionEnvelopeWire.fields envelope) raw.selected = none :=
            by simpa [tx] using selectedSig
          simp [selectedSig']
      | some scriptSig =>
          have selectedSig' : DynamicRawSource.scriptSigAt
              (TransactionEnvelopeWire.fields envelope) raw.selected =
                some scriptSig := by simpa [tx] using selectedSig
          have localAgree : ∀ q ∈ ScriptSigTraceContract.queries
              (contract.reached functions tx raw.selected scriptSig),
              answer functions' q = answer functions q := by
            intro q mem
            exact agree q (by
              simpa [scriptSigDependencies, decoded, tx, selectedSig]
                using mem)
          simpa [selectedSig'] using
            (contract.queriesCongr functions functions' tx raw.selected
              scriptSig localAgree)

/-- Downstream extraction runs only after a concrete prepared attempt exists. -/
def downstreamDependencies (contract : ScriptSigTraceContract.Contract)
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt) : List Query :=
  match DynamicRawSource.prepare (contract.eval functions) raw with
  | none => []
  | some attempt =>
      DynamicSourceExtractorCausality.extractorDependencies functions lock
        validKey ecdsa attempt

def combinedDependencies (contract : ScriptSigTraceContract.Contract)
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt) : List Query :=
  scriptSigDependencies contract functions raw ++
    downstreamDependencies contract functions lock validKey ecdsa raw

/-- On a failed preparation there is no downstream extractor work. The
scriptSig segment can still be arbitrarily long if the evaluator itself fails. -/
theorem combined_eq_scriptSig_of_prepare_none
    (contract : ScriptSigTraceContract.Contract)
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt)
    (failed : DynamicRawSource.prepare (contract.eval functions) raw = none) :
    combinedDependencies contract functions lock validKey ecdsa raw =
      scriptSigDependencies contract functions raw := by
  simp [combinedDependencies, downstreamDependencies, failed]

/-- A successful preparation reveals the evaluator's successful return on
the selected parsed scriptSig, so its segment costs at most 402 H/R entries. -/
theorem scriptSigDependencies_length_le_402_of_prepared
    (contract : ScriptSigTraceContract.Contract)
    (functions : JointSourceChecks.Functions)
    (raw : DynamicRawSource.RawAttempt)
    (attempt : DynamicSourceGame.Attempt)
    (prepared : DynamicRawSource.prepare (contract.eval functions) raw =
      some attempt) :
    (scriptSigDependencies contract functions raw).length ≤ 402 := by
  unfold DynamicRawSource.prepare at prepared
  cases decoded : TransactionEnvelopeWire.decodeStrict raw.rawTx with
  | none => simp [decoded] at prepared
  | some envelope =>
      let tx := TransactionEnvelopeWire.fields envelope
      cases selectedSig : DynamicRawSource.scriptSigAt tx raw.selected with
      | none => simp [decoded, tx, selectedSig] at prepared
      | some scriptSig =>
          cases evaluated : contract.eval functions tx raw.selected
              scriptSig with
          | none => simp [decoded, tx, selectedSig, evaluated] at prepared
          | some stack =>
              have bound := ScriptSigTraceContract.successful_eval_queries_le_402
                contract functions tx raw.selected scriptSig stack evaluated
              simpa [scriptSigDependencies, decoded, tx, selectedSig]
                using bound

/-- The 402 successful scriptSig entries plus at most 1295 downstream
extractor entries give a conditional 1697-entry inventory. -/
theorem combinedDependencies_length_le_1697_of_prepared
    (contract : ScriptSigTraceContract.Contract)
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt)
    (attempt : DynamicSourceGame.Attempt)
    (prepared : DynamicRawSource.prepare (contract.eval functions) raw =
      some attempt) :
    (combinedDependencies contract functions lock validKey ecdsa raw).length
      ≤ 1697 := by
  have scriptBound := scriptSigDependencies_length_le_402_of_prepared
    contract functions raw attempt prepared
  have sourceBound := DynamicSourceExtractorCausality.extractorDependencies_length_le_1295
    functions lock validKey ecdsa attempt
  simp only [combinedDependencies, downstreamDependencies, prepared,
    List.length_append]
  omega

/-- Agreement on the combined inventory preserves the functions-indexed raw
extractor's optional result, even when preparation or extraction fails. -/
theorem raw_extractor_congr
    (contract : ScriptSigTraceContract.Contract)
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (raw : DynamicRawSource.RawAttempt)
    (agree : ∀ q ∈ combinedDependencies contract functions lock validKey
      ecdsa raw, answer functions' q = answer functions q) :
    DynamicRawSource.extractor functions' lock validKey ecdsa
      (contract.eval functions') raw =
    DynamicRawSource.extractor functions lock validKey ecdsa
      (contract.eval functions) raw := by
  have scriptAgree : ∀ q ∈ scriptSigDependencies contract functions raw,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [combinedDependencies, mem])
  have downstreamAgree : ∀ q ∈ downstreamDependencies contract functions
      lock validKey ecdsa raw,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [combinedDependencies, mem])
  have preparedEq := prepare_congr contract functions functions' raw
    scriptAgree
  unfold DynamicRawSource.extractor
  rw [preparedEq]
  cases prepared : DynamicRawSource.prepare (contract.eval functions) raw with
  | none => simp
  | some attempt =>
      have sourceAgree : ∀ q ∈
          DynamicSourceExtractorCausality.extractorDependencies functions lock
            validKey ecdsa attempt,
          answer functions' q = answer functions q := by
        intro q mem
        exact downstreamAgree q (by
          simpa [downstreamDependencies, prepared] using mem)
      have extracted := DynamicSourceExtractorCausality.extractor_congr
        functions functions' lock validKey ecdsa attempt sourceAgree
      simp [extracted]

end QSB.WorldIndexedScriptSigExtractor
