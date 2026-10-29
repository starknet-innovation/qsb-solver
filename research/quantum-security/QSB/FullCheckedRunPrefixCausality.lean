import QSB.FullCheckedRunCausality

/-!
Prefix causality for source-model H/R dependency lists. Before an adaptive
query is selected, only answers to earlier listed queries may affect its
input. The lock, transaction, selected input, key validator, and ECDSA
predicate stay fixed across worlds. This is a pure Lean trace property, not
an instrumented Bitcoin Core execution or a coherent-query theorem.
-/
namespace QSB.FullCheckedRunPrefixCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Agreement on the first `k` query answers fixes the first `k + 1` query
positions whenever the first trace has that next query. -/
def PrefixCausal (trace : JointSourceChecks.Functions → List Query) : Prop :=
  ∀ functions functions' k,
    k < (trace functions).length →
    (∀ q ∈ (trace functions).take k,
      answer functions' q = answer functions q) →
    (trace functions').take (k + 1) =
      (trace functions).take (k + 1)

/-- Composing a causal head and a tail selected by its answers preserves
prefix causality. The head equality premise is needed when the next query
lies in the tail. -/
theorem append_prefix
    (head tail : JointSourceChecks.Functions → List Query)
    (headPrefix : PrefixCausal head)
    (headCongr : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      head functions' = head functions)
    (tailPrefix : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      ∀ k, k < (tail functions).length →
        (∀ q ∈ (tail functions).take k,
          answer functions' q = answer functions q) →
        (tail functions').take (k + 1) =
          (tail functions).take (k + 1)) :
    PrefixCausal (fun functions => head functions ++ tail functions) := by
  intro functions functions' k available agree
  by_cases inHead : k < (head functions).length
  · have headAgree : ∀ q ∈ (head functions).take k,
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by
        rw [List.take_append_of_le_length (by omega :
          k ≤ (head functions).length)]
        exact mem)
    have sameHead := headPrefix functions functions' k inHead headAgree
    have headLength : k + 1 ≤ (head functions').length := by
      have lengths := congrArg List.length sameHead
      simp only [List.length_take] at lengths
      omega
    rw [List.take_append_of_le_length headLength,
      List.take_append_of_le_length (by omega :
        k + 1 ≤ (head functions).length)]
    exact sameHead
  · have pastHead : (head functions).length ≤ k := by omega
    have headAgree : ∀ q ∈ head functions,
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by
        rw [List.take_append,
          List.take_of_length_le pastHead]
        exact List.mem_append.mpr (Or.inl mem))
    have sameHead := headCongr functions functions' headAgree
    have tailAvailable : k - (head functions).length <
        (tail functions).length := by
      simp only [List.length_append] at available
      omega
    have tailAgree : ∀ q ∈
        (tail functions).take (k - (head functions).length),
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by
        rw [List.take_append,
          List.take_of_length_le pastHead]
        exact List.mem_append.mpr (Or.inr mem))
    have sameTail := tailPrefix functions functions' headAgree
      (k - (head functions).length) tailAvailable tailAgree
    rw [List.take_append, List.take_append, sameHead]
    rw [List.take_of_length_le (by omega :
      (head functions).length ≤ k + 1)]
    have index : k + 1 - (head functions).length =
        (k - (head functions).length) + 1 := by omega
    simp only [index, sameTail]

/-- An empty dependency list has no next-query obligation. -/
theorem empty_prefix : PrefixCausal (fun _ => []) := by
  intro functions functions' k available _
  simp at available

/-- A fixed dependency list is prefix-causal. -/
theorem constant_prefix (queries : List Query) :
    PrefixCausal (fun _ => queries) := by
  intro functions functions' k _ _
  rfl

/-- A two-query composition is prefix-causal when its second query input is
determined by the answer to the first query. -/
theorem two_stage_prefix
    (first : Query)
    (second : JointSourceChecks.Functions → Query)
    (secondCongr : ∀ functions functions',
      answer functions' first = answer functions first →
      second functions' = second functions) :
    PrefixCausal (fun functions => [first, second functions]) := by
  intro functions functions' k available agree
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero =>
          have firstAgree : answer functions' first = answer functions first :=
            agree first (by simp)
          simp [secondCongr functions functions' firstAgree]
      | succ k => simp at available

/-- The inner H answer selects the outer H query of one legacy digest. -/
theorem legacyDigestTrace_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat) :
    PrefixCausal (fun functions => JointLegacyDigestQueries.trace
      functions tx selected scriptCode hashType) := by
  intro functions functions' k available agree
  dsimp only at available agree ⊢
  by_cases valid : selected < tx.inputs.length
  · cases present : LegacySighashWire.sourcePreimage tx selected
        scriptCode hashType with
    | none =>
        rw [JointLegacyDigestQueries.trace_missing_preimage functions tx
          selected scriptCode hashType valid present] at available
        simp at available
    | some preimage =>
        have firstTrace := JointLegacyDigestQueries.trace_present_preimage
          functions tx selected scriptCode hashType preimage valid present
        have secondTrace := JointLegacyDigestQueries.trace_present_preimage
          functions' tx selected scriptCode hashType preimage valid present
        rw [firstTrace] at available agree ⊢
        rw [secondTrace]
        exact two_stage_prefix (.H preimage)
          (fun f => .H (f.H preimage))
          (by
            intro f g h
            simpa using congrArg Query.H h)
          functions functions' k available agree
  · have invalid : tx.inputs.length ≤ selected := Nat.le_of_not_gt valid
    rw [JointLegacyDigestQueries.trace_invalid_input functions tx selected
      scriptCode hashType invalid] at available
    simp at available

/-- A reached pair has the same two-stage prefix property after its fixed
last-byte and key-validity gates. -/
theorem pairDigestTrace_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool) (sig key scriptCode : Bytes) :
    PrefixCausal (fun functions => CheckedRunQueryTrace.pairDigestTrace
      functions tx selected validKey sig key scriptCode) := by
  intro functions functions' k available agree
  dsimp only at available agree ⊢
  cases last : sig.getLast? with
  | none =>
      simp [CheckedRunQueryTrace.pairDigestTrace, last] at available
  | some hashType =>
      by_cases keyValid : validKey key = true
      · have h := legacyDigestTrace_prefix tx selected scriptCode
          hashType.toNat functions functions' k
          (by simpa [CheckedRunQueryTrace.pairDigestTrace, last,
            keyValid] using available)
          (by
            intro q mem
            exact agree q (by simpa [CheckedRunQueryTrace.pairDigestTrace,
              last, keyValid] using mem))
        simpa [CheckedRunQueryTrace.pairDigestTrace, last,
          keyValid] using h
      · simp [CheckedRunQueryTrace.pairDigestTrace, last,
          keyValid] at available

/-- The single-signature entry's stack and DER gates leave the same
two-stage digest prefix when a pair is reached. -/
theorem checksigDigestTrace_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool) (script : Bytes)
    (s : CoreCheckedStep.State) :
    PrefixCausal (fun functions =>
      CheckedRunQueryTrace.checksigDigestTrace functions tx selected
        validKey script s) := by
  intro functions functions' k available agree
  dsimp only at available agree ⊢
  cases keyAt : s.stack.reverse[0]? with
  | none =>
      simp [CheckedRunQueryTrace.checksigDigestTrace,
        keyAt] at available
  | some key =>
      cases sigAt : s.stack.reverse[1]? with
      | none =>
          simp [CheckedRunQueryTrace.checksigDigestTrace,
            keyAt, sigAt] at available
      | some sig =>
          by_cases der : DERSyntax.verifyAllEncoding sig = true
          · have h := pairDigestTrace_prefix tx selected validKey sig key
              (CoreFindAndDelete.run 880 script
                (CorePushSerialize.pushPattern sig))
              functions functions' k
              (by simpa [CheckedRunQueryTrace.checksigDigestTrace,
                keyAt, sigAt, der] using available)
              (by
                intro q mem
                exact agree q (by simpa
                  [CheckedRunQueryTrace.checksigDigestTrace,
                    keyAt, sigAt, der] using mem))
            simpa [CheckedRunQueryTrace.checksigDigestTrace,
              keyAt, sigAt, der] using h
          · simp [CheckedRunQueryTrace.checksigDigestTrace,
              keyAt, sigAt, der] at available

/-- HASH160 queries H before using its answer as R's input; all other
opcode step query lists are fixed by their stack input. -/
theorem opcodeStepQueries_prefix (op : Op) (stack : List Bytes) :
    PrefixCausal (fun functions =>
      ByteMachineQueries.stepQueries functions op stack) := by
  by_cases hash160 : op = .hash160
  · subst op
    cases stack with
    | nil =>
        simpa [ByteMachineQueries.stepQueries] using empty_prefix
    | cons x xs =>
        simpa [ByteMachineQueries.stepQueries] using
          (two_stage_prefix (.H x) (fun functions => .R (functions.H x))
            (by
              intro functions functions' h
              simpa using congrArg Query.R h))
  · cases op <;> cases stack <;> simp_all [ByteMachineQueries.stepQueries,
      PrefixCausal]

/-- The multisignature scan's next digest query is selected by earlier H
answers and the fixed ECDSA predicate. This includes failed comparisons,
early false exits, and fatal DER gates. -/
theorem scanDigestTrace_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (encoding : Bytes → Bool) (scriptCode : Bytes) :
    ∀ (sigs keys : List Bytes),
      PrefixCausal (fun functions =>
        CheckedRunQueryTrace.scanDigestTrace functions tx selected
          validKey ecdsa encoding scriptCode sigs keys)
  | sigs, [] => by
      cases sigs <;> simp [CheckedRunQueryTrace.scanDigestTrace,
        PrefixCausal]
  | [], _ :: _ => by
      simp [CheckedRunQueryTrace.scanDigestTrace, PrefixCausal]
  | sig :: sigs, key :: keys => by
      by_cases impossible : (sig :: sigs).length > (key :: keys).length
      · have guard : keys.length < sigs.length := by
          simp only [List.length_cons] at impossible
          omega
        simp [CheckedRunQueryTrace.scanDigestTrace, guard,
          PrefixCausal]
      · by_cases encoded : encoding sig = true
        · have guard : ¬ keys.length < sigs.length := by
            simp only [List.length_cons] at impossible
            omega
          let head : JointSourceChecks.Functions → List Query :=
            fun functions => CheckedRunQueryTrace.pairDigestTrace
              functions tx selected validKey sig key scriptCode
          let tail : JointSourceChecks.Functions → List Query :=
            fun functions =>
              let verified := CoreMultisigEval.nonemptyVerify
                (CoreFinalChecksigEval.checker validKey
                  (JointSourceChecks.checker functions tx selected ecdsa))
                scriptCode sig key
              if verified then
                CheckedRunQueryTrace.scanDigestTrace functions tx selected
                  validKey ecdsa encoding scriptCode sigs keys
              else
                CheckedRunQueryTrace.scanDigestTrace functions tx selected
                  validKey ecdsa encoding scriptCode (sig :: sigs) keys
          have headPrefix : PrefixCausal head := by
            simpa [head] using pairDigestTrace_prefix tx selected
              validKey sig key scriptCode
          have headCongr : ∀ functions functions',
              (∀ q ∈ head functions,
                answer functions' q = answer functions q) →
              head functions' = head functions := by
            intro functions functions' agree
            exact CheckedRunQueryTrace.pairDigestTrace_congr
              functions functions' tx selected validKey sig key
              scriptCode agree
          have tailPrefix : ∀ functions functions',
              (∀ q ∈ head functions,
                answer functions' q = answer functions q) →
              ∀ k, k < (tail functions).length →
                (∀ q ∈ (tail functions).take k,
                  answer functions' q = answer functions q) →
                (tail functions').take (k + 1) =
                  (tail functions).take (k + 1) := by
            intro functions functions' headAgree
            have pairEq := CheckedRunQueryTrace.pair_checker_congr
              functions functions' tx selected validKey ecdsa sig key
              scriptCode headAgree
            have verifyEq :
                CoreMultisigEval.nonemptyVerify
                  (CoreFinalChecksigEval.checker validKey
                    (JointSourceChecks.checker functions' tx selected ecdsa))
                  scriptCode sig key =
                CoreMultisigEval.nonemptyVerify
                  (CoreFinalChecksigEval.checker validKey
                    (JointSourceChecks.checker functions tx selected ecdsa))
                  scriptCode sig key := by
              simp [CoreMultisigEval.nonemptyVerify, pairEq]
            dsimp [tail]
            rw [verifyEq]
            by_cases verified : CoreMultisigEval.nonemptyVerify
                (CoreFinalChecksigEval.checker validKey
                  (JointSourceChecks.checker functions tx selected ecdsa))
                scriptCode sig key = true
            · simp [verified]
              exact scanDigestTrace_prefix tx selected validKey ecdsa
                encoding scriptCode sigs keys functions functions'
            · simp [verified]
              exact scanDigestTrace_prefix tx selected validKey ecdsa
                encoding scriptCode (sig :: sigs) keys functions functions'
          have combined := append_prefix head tail headPrefix headCongr
            tailPrefix
          simpa [head, tail, CheckedRunQueryTrace.scanDigestTrace,
            guard, encoded] using combined
        · have guard : ¬ keys.length < sigs.length := by
            simp only [List.length_cons] at impossible
            omega
          simp [CheckedRunQueryTrace.scanDigestTrace, guard, encoded,
            PrefixCausal]

/-- Count parsing, capacity checks, and FindAndDelete are fixed before the
reached multisignature scan; they preserve its prefix causality. -/
theorem scanAtStackDigestTrace_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (bottom : List Bytes) :
    PrefixCausal (fun functions =>
      CheckedRunQueryTrace.scanAtStackDigestTrace functions tx selected
        validKey ecdsa script bottom) := by
  intro functions functions' k available agree
  dsimp only at available agree ⊢
  cases keys : CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none =>
      simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
        keys] at available
  | some n =>
      by_cases badN : n < 0 ∨ n > 20
      · simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
          keys, badN] at available
      · cases sigs : CoreMultisigCleanup.parseSourceCount bottom
            (n.toNat + 2) with
        | none =>
            simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
              keys, badN, sigs] at available
        | some m =>
            by_cases badM : m < 0 ∨ m > n
            · simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
                keys, badN, sigs, badM] at available
            · by_cases short : bottom.length < n.toNat + m.toNat + 3
              · simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
                  keys, badN, sigs, badM, short] at available
              · have h := scanDigestTrace_prefix tx selected validKey ecdsa
                  DERSyntax.verifyAllEncoding
                  (CoreMultisigSourceScan.deletedScript script
                    bottom.reverse n.toNat m.toNat)
                  (CoreMultisigSourceScan.reachedSignatures
                    bottom.reverse n.toNat m.toNat)
                  (CoreMultisigSourceScan.reachedKeys
                    bottom.reverse n.toNat)
                  functions functions' k
                  (by simpa [CheckedRunQueryTrace.scanAtStackDigestTrace,
                    keys, badN, sigs, badM, short] using available)
                  (by
                    intro q mem
                    exact agree q (by simpa
                      [CheckedRunQueryTrace.scanAtStackDigestTrace,
                        keys, badN, sigs, badM, short] using mem))
                simpa [CheckedRunQueryTrace.scanAtStackDigestTrace,
                  keys, badN, sigs, badM, short] using h

/-- Every checked step chooses its next H/R dependency from earlier answers
within that step's ordered list. -/
theorem stepQueries_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (s : CoreCheckedStep.State) :
    PrefixCausal (fun functions => FullCheckedRunQueries.stepQueries
      functions tx selected validKey ecdsa script op s) := by
  cases op <;>
    try (simpa [FullCheckedRunQueries.stepQueries] using
      (opcodeStepQueries_prefix _ s.stack.reverse))
  case checksigverify =>
    simpa [FullCheckedRunQueries.stepQueries] using
      checksigDigestTrace_prefix tx selected validKey script s
  case checkmultisig =>
    simpa [FullCheckedRunQueries.stepQueries] using
      scanAtStackDigestTrace_prefix tx selected validKey ecdsa
        script s.stack

/-- Prefix causality of one whole checked source run. Agreement on the
first `k` answers in the first run's dependency list fixes the first
`k + 1` query positions in the second run. -/
theorem runQueries_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) :
    ∀ (ops : List Op) (s : CoreCheckedStep.State),
      PrefixCausal (fun functions => FullCheckedRunQueries.runQueries
        functions tx selected validKey ecdsa script ops s)
  | [], s => by
      simpa [FullCheckedRunQueries.runQueries] using empty_prefix
  | op :: rest, s => by
      let head : JointSourceChecks.Functions → List Query :=
        fun functions => FullCheckedRunQueries.stepQueries functions tx
          selected validKey ecdsa script op s
      let tail : JointSourceChecks.Functions → List Query :=
        fun functions =>
          match CoreCheckedStep.step (JointSourceChecks.hashes functions)
              script validKey
              (JointSourceChecks.checker functions tx selected ecdsa)
              op s with
          | none => []
          | some (next, _) =>
              if next.stack.length > 1000 then []
              else FullCheckedRunQueries.runQueries functions tx selected
                validKey ecdsa script rest next
      have headPrefix : PrefixCausal head := by
        simpa [head] using stepQueries_prefix tx selected validKey
          ecdsa script op s
      have headCongr : ∀ functions functions',
          (∀ q ∈ head functions,
            answer functions' q = answer functions q) →
          head functions' = head functions := by
        intro functions functions' agree
        exact FullCheckedRunCausality.stepQueries_congr functions
          functions' tx selected validKey ecdsa script op s agree
      have tailPrefix : ∀ functions functions',
          (∀ q ∈ head functions,
            answer functions' q = answer functions q) →
          ∀ k, k < (tail functions).length →
            (∀ q ∈ (tail functions).take k,
              answer functions' q = answer functions q) →
            (tail functions').take (k + 1) =
              (tail functions).take (k + 1) := by
        intro functions functions' headAgree
        have stepEq := FullCheckedRunCausality.step_result_congr
          functions functions' tx selected validKey ecdsa script op s
          headAgree
        dsimp [tail]
        rw [stepEq]
        cases hstep : CoreCheckedStep.step
            (JointSourceChecks.hashes functions) script validKey
            (JointSourceChecks.checker functions tx selected ecdsa)
            op s with
        | none => simp
        | some pair =>
            obtain ⟨next, record⟩ := pair
            by_cases large : next.stack.length > 1000
            · simp [large]
            · simpa [large] using runQueries_prefix tx selected validKey
                ecdsa script rest next functions functions'
      have combined := append_prefix head tail headPrefix headCongr
        tailPrefix
      have traceEq :
          (fun functions => FullCheckedRunQueries.runQueries functions tx
            selected validKey ecdsa script (op :: rest) s) =
          (fun functions => head functions ++ tail functions) := by
        funext functions
        simp only [FullCheckedRunQueries.runQueries, head, tail]
        cases CoreCheckedStep.step (JointSourceChecks.hashes functions)
            script validKey
            (JointSourceChecks.checker functions tx selected ecdsa)
            op s with
        | none => simp
        | some pair =>
            obtain ⟨next, record⟩ := pair
            simp
            split_ifs <;> simp
      rw [traceEq]
      exact combined

/-- Specialization to every parameterized Config A checked lock. -/
theorem checked_lock_prefix_next
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (lock : DynamicCheckedCertificate.Lock)
    (s : CoreCheckedStep.State) (k : Nat)
    (available : k <
      (FullCheckedRunQueries.runQueries functions tx selected validKey
        ecdsa (DynamicCheckedCertificate.wire lock)
        (DynamicCheckedCertificate.program lock) s).length)
    (agree : ∀ q ∈
      (FullCheckedRunQueries.runQueries functions tx selected validKey
        ecdsa (DynamicCheckedCertificate.wire lock)
        (DynamicCheckedCertificate.program lock) s).take k,
      answer functions' q = answer functions q) :
    (FullCheckedRunQueries.runQueries functions' tx selected validKey
      ecdsa (DynamicCheckedCertificate.wire lock)
      (DynamicCheckedCertificate.program lock) s).take (k + 1) =
    (FullCheckedRunQueries.runQueries functions tx selected validKey
      ecdsa (DynamicCheckedCertificate.wire lock)
      (DynamicCheckedCertificate.program lock) s).take (k + 1) :=
  runQueries_prefix tx selected validKey ecdsa
    (DynamicCheckedCertificate.wire lock)
    (DynamicCheckedCertificate.program lock) s
    functions functions' k available agree

end QSB.FullCheckedRunPrefixCausality
