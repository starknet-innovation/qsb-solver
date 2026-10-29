import QSB.LockSignatureQueryBudget
import QSB.JointLegacyDigestQueries

/-!
Query accounting for successful source-shaped checked lock runs. The opcode
trace is inherited from the checked run's proved byte-machine replay. The
signature checker trace below covers only the explicit `legacyDigest` calls of
one source-shaped pair checker; the external key validator and ECDSA predicate
are fixed, uninstrumented functions. A combined checked-run trace still needs
the reached multisignature and CHECKSIGVERIFY call arguments in order.
-/
namespace QSB.CheckedRunQueryTrace
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- The hash-opcode calls of a checked run, replayed with its computed
signature-site results rather than caller-supplied Booleans. -/
def opcodeTrace (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (initial : CoreCheckedStep.State) (records : List Bool) : List Query :=
  ByteMachineQueries.runQueries functions
    (DynamicCheckedCertificate.program lock)
    ⟨initial.stack.reverse, records, initial.ops⟩

/-- A successful checked execution of any parameterized lock has exactly
18 H and 15 R hash-opcode calls. Its checker calls are outside this trace. -/
theorem checked_run_opcode_trace_exact
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records)) :
    (opcodeTrace functions lock initial records).length = 33 ∧
      ((opcodeTrace functions lock initial records).map
        ByteMachineQueries.hWeight).sum = 18 ∧
      ((opcodeTrace functions lock initial records).map
        ByteMachineQueries.rWeight).sum = 15 := by
  have replay := CoreCheckedStep.checked_run_refines_byte
    (JointSourceChecks.hashes functions) (DynamicCheckedCertificate.wire lock)
    validKey verify (DynamicCheckedCertificate.program lock)
    initial final records success
  exact ByteMachineQueries.lock_queries_exact_of_success functions lock
    ⟨initial.stack.reverse, records, initial.ops⟩
    ⟨final.stack.reverse, [], final.ops⟩ replay

/-- Explicit H queries of one reached source-shaped signature pair. The
`validKey` result is treated as fixed; an invalid key short-circuits the
modeled digest checker. -/
def pairDigestTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (sig key scriptCode : Bytes) : List Query :=
  match sig.getLast? with
  | none => []
  | some hashType =>
      if validKey key then
        JointLegacyDigestQueries.trace functions tx selected scriptCode
          hashType.toNat
      else []

/-- One reached pair's modeled digest needs at most two H queries. -/
theorem pairDigestTrace_length_le_two
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (sig key scriptCode : Bytes) :
    (pairDigestTrace functions tx selected validKey sig key scriptCode).length
      ≤ 2 := by
  unfold pairDigestTrace
  cases sig.getLast? with
  | none => simp
  | some hashType =>
      by_cases keyValid : validKey key = true
      · simpa [keyValid] using JointLegacyDigestQueries.trace_length_le_two
          functions tx selected scriptCode hashType.toNat
      · simp [keyValid]

/-- Agreement on the reached pair's recorded digest queries preserves the
source-shaped checker result, with the same external key and ECDSA functions
on both sides. -/
theorem pair_checker_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (sig key scriptCode : Bytes)
    (agree : ∀ q ∈ pairDigestTrace functions tx selected validKey
        sig key scriptCode,
      answer functions' q = answer functions q) :
    CoreFinalChecksigEval.checker validKey
      (JointSourceChecks.checker functions' tx selected ecdsa)
      sig key scriptCode =
    CoreFinalChecksigEval.checker validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      sig key scriptCode := by
  cases last : sig.getLast? with
  | none => simp [CoreFinalChecksigEval.checker, last]
  | some hashType =>
      by_cases keyValid : validKey key = true
      · have digestEq := JointLegacyDigestQueries.legacyDigest_congr
          functions functions' tx selected scriptCode hashType.toNat
          (fun q mem => agree q (by
            simpa [pairDigestTrace, last, keyValid] using mem))
        simp [CoreFinalChecksigEval.checker, last, keyValid,
          JointSourceChecks.checker, digestEq]
      · simp [CoreFinalChecksigEval.checker, last, keyValid]

/-- The same agreement also fixes the adaptive second query input. -/
theorem pairDigestTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (sig key scriptCode : Bytes)
    (agree : ∀ q ∈ pairDigestTrace functions tx selected validKey
        sig key scriptCode,
      answer functions' q = answer functions q) :
    pairDigestTrace functions' tx selected validKey sig key scriptCode =
      pairDigestTrace functions tx selected validKey sig key scriptCode := by
  cases last : sig.getLast? with
  | none => simp [pairDigestTrace, last]
  | some hashType =>
      by_cases keyValid : validKey key = true
      · have traceEq := JointLegacyDigestQueries.trace_congr
          functions functions' tx selected scriptCode hashType.toNat
          (fun q mem => agree q (by
            simpa [pairDigestTrace, last, keyValid] using mem))
        simpa [pairDigestTrace, last, keyValid] using traceEq
      · simp [pairDigestTrace, last, keyValid]

/-! ### The source-shaped multisignature pair scan -/

/-- Digest queries made by the source-shaped ordered pair scan. The scan
advances one key after every attempted pair. Empty signatures, invalid keys,
fatal DER failures, and the early impossible-to-match test contribute no
digest query at that point. -/
def scanDigestTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (encoding : Bytes → Bool) (scriptCode : Bytes) :
    List Bytes → List Bytes → List Query
  | [], _ => []
  | _ :: _, [] => []
  | sig :: sigs, key :: keys =>
      if (sig :: sigs).length > (key :: keys).length then []
      else if encoding sig then
        let current := pairDigestTrace functions tx selected validKey
          sig key scriptCode
        let verified := CoreMultisigEval.nonemptyVerify
          (CoreFinalChecksigEval.checker validKey
            (JointSourceChecks.checker functions tx selected ecdsa))
          scriptCode sig key
        current ++
          (if verified then
            scanDigestTrace functions tx selected validKey ecdsa encoding
              scriptCode sigs keys
          else
            scanDigestTrace functions tx selected validKey ecdsa encoding
              scriptCode (sig :: sigs) keys)
      else []

/-- The pair scan spends at most two H queries per reached key, regardless
of how signature matches and DER gates branch. -/
theorem scanDigestTrace_length_le (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (encoding : Bytes → Bool) (scriptCode : Bytes) :
    ∀ (sigs keys : List Bytes),
      (scanDigestTrace functions tx selected validKey ecdsa encoding
        scriptCode sigs keys).length ≤ 2 * keys.length
  | sigs, [] => by cases sigs <;> simp [scanDigestTrace]
  | [], _ :: _ => by simp [scanDigestTrace]
  | sig :: sigs, key :: keys => by
      have current := pairDigestTrace_length_le_two functions tx selected
        validKey sig key scriptCode
      have matched := scanDigestTrace_length_le functions tx selected
        validKey ecdsa encoding scriptCode sigs keys
      have unmatched := scanDigestTrace_length_le functions tx selected
        validKey ecdsa encoding scriptCode (sig :: sigs) keys
      simp only [scanDigestTrace]
      split_ifs <;> simp_all [List.length_append] <;> omega

/-- The scanner's Boolean result is causal in its recorded digest queries
when `validKey` and `ecdsa` are fixed across worlds. -/
theorem scan_result_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (encoding : Bytes → Bool) (scriptCode : Bytes) :
    ∀ (sigs keys : List Bytes),
      (∀ q ∈ scanDigestTrace functions tx selected validKey ecdsa
        encoding scriptCode sigs keys,
        answer functions' q = answer functions q) →
      CoreMultisigEval.scan encoding
          (CoreMultisigEval.nonemptyVerify
            (CoreFinalChecksigEval.checker validKey
              (JointSourceChecks.checker functions' tx selected ecdsa))
            scriptCode) sigs keys =
        CoreMultisigEval.scan encoding
          (CoreMultisigEval.nonemptyVerify
            (CoreFinalChecksigEval.checker validKey
              (JointSourceChecks.checker functions tx selected ecdsa))
            scriptCode) sigs keys
  | sigs, [] => by cases sigs <;> simp [CoreMultisigEval.scan]
  | [], _ :: _ => by simp [CoreMultisigEval.scan]
  | sig :: sigs, key :: keys => by
      intro agree
      by_cases impossible : (sig :: sigs).length > (key :: keys).length
      · have guard : keys.length < sigs.length := by
          simp only [List.length_cons] at impossible
          omega
        simp [CoreMultisigEval.scan, guard]
      · by_cases encoded : encoding sig = true
        · have currentAgree : ∀ q ∈ pairDigestTrace functions tx selected
              validKey sig key scriptCode,
              answer functions' q = answer functions q := by
            intro q mem
            have guard : ¬ keys.length < sigs.length := by
              simp only [List.length_cons] at impossible
              omega
            apply agree q
            simp [scanDigestTrace, guard, encoded, mem]
          have pairEq := pair_checker_congr functions functions' tx selected
            validKey ecdsa sig key scriptCode currentAgree
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
          by_cases verified : CoreMultisigEval.nonemptyVerify
              (CoreFinalChecksigEval.checker validKey
                (JointSourceChecks.checker functions tx selected ecdsa))
              scriptCode sig key = true
          · have tailAgree : ∀ q ∈ scanDigestTrace functions tx selected
                validKey ecdsa encoding scriptCode sigs keys,
                answer functions' q = answer functions q := by
              intro q mem
              have guard : ¬ keys.length < sigs.length := by
                simp only [List.length_cons] at impossible
                omega
              apply agree q
              simp [scanDigestTrace, guard, encoded, verified, mem]
            have tail := scan_result_congr functions functions' tx selected
              validKey ecdsa encoding scriptCode sigs keys tailAgree
            have guard : ¬ keys.length < sigs.length := by
              simp only [List.length_cons] at impossible
              omega
            simp [CoreMultisigEval.scan, guard, encoded,
              verifyEq, verified, tail]
          · have tailAgree : ∀ q ∈ scanDigestTrace functions tx selected
                validKey ecdsa encoding scriptCode (sig :: sigs) keys,
                answer functions' q = answer functions q := by
              intro q mem
              have guard : ¬ keys.length < sigs.length := by
                simp only [List.length_cons] at impossible
                omega
              apply agree q
              simp [scanDigestTrace, guard, encoded, verified, mem]
            have tail := scan_result_congr functions functions' tx selected
              validKey ecdsa encoding scriptCode (sig :: sigs) keys tailAgree
            have guard : ¬ keys.length < sigs.length := by
              simp only [List.length_cons] at impossible
              omega
            simp [CoreMultisigEval.scan, guard, encoded,
              verifyEq, verified, tail]
        · have guard : ¬ keys.length < sigs.length := by
            simp only [List.length_cons] at impossible
            omega
          simp [CoreMultisigEval.scan, guard, encoded]

/-! ### Reached CHECKMULTISIG stack -/

/-- Digest-query trace at the source-shaped multisignature entry point. It
uses the same count, capacity, and common FindAndDelete scriptCode as
`CoreMultisigSourceScan.scanAtStack`. -/
def scanAtStackDigestTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (bottom : List Bytes) : List Query :=
  match CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none => []
  | some n =>
      if n < 0 ∨ n > 20 then [] else
      match CoreMultisigCleanup.parseSourceCount bottom (n.toNat + 2) with
      | none => []
      | some m =>
          if m < 0 ∨ m > n then [] else
          let top := bottom.reverse
          if n.toNat + m.toNat + 3 > top.length then [] else
          scanDigestTrace functions tx selected validKey ecdsa
            DERSyntax.verifyAllEncoding
            (CoreMultisigSourceScan.deletedScript script top
              n.toNat m.toNat)
            (CoreMultisigSourceScan.reachedSignatures top
              n.toNat m.toNat)
            (CoreMultisigSourceScan.reachedKeys top n.toNat)

/-- A source scan whose reached key-count cell parses as ten makes at most
20 explicit H calls for legacy signature digests. The result may be false. -/
theorem scanAtStackDigestTrace_ten_le_20
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (bottom : List Bytes)
    (ten : CoreMultisigCleanup.parseSourceCount bottom 1 = some 10) :
    (scanAtStackDigestTrace functions tx selected validKey ecdsa
      script bottom).length ≤ 20 := by
  cases sigs : CoreMultisigCleanup.parseSourceCount bottom 12 with
  | none => simp [scanAtStackDigestTrace, ten, sigs]
  | some m =>
      by_cases badM : m < 0 ∨ m > (10 : Int)
      · simp [scanAtStackDigestTrace, ten, sigs, badM]
      · by_cases short : bottom.length < 10 + m.toNat + 3
        · simp [scanAtStackDigestTrace, ten, sigs, badM, short]
        · have h := scanDigestTrace_length_le functions tx selected
            validKey ecdsa DERSyntax.verifyAllEncoding
            (CoreMultisigSourceScan.deletedScript script bottom.reverse
              10 m.toNat)
            (CoreMultisigSourceScan.reachedSignatures bottom.reverse
              10 m.toNat)
            (CoreMultisigSourceScan.reachedKeys bottom.reverse 10)
          have keysLength :
              (CoreMultisigSourceScan.reachedKeys bottom.reverse 10).length
                ≤ 10 := by
            simp [CoreMultisigSourceScan.reachedKeys]
          have target :
              (scanDigestTrace functions tx selected validKey ecdsa
                DERSyntax.verifyAllEncoding
                (CoreMultisigSourceScan.deletedScript script bottom.reverse
                  10 m.toNat)
                (CoreMultisigSourceScan.reachedSignatures bottom.reverse
                  10 m.toNat)
                (CoreMultisigSourceScan.reachedKeys bottom.reverse 10)).length
                ≤ 20 := by omega
          simpa [scanAtStackDigestTrace, ten, sigs, badM, short]
            using target

/-- If two oracle worlds agree on the reached scan's digest queries, its
source-shaped Boolean or fatal result is the same. The external key and ECDSA
functions and the spent script are held fixed. -/
theorem scanAtStack_result_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (bottom : List Bytes)
    (agree : ∀ q ∈ scanAtStackDigestTrace functions tx selected validKey
        ecdsa script bottom,
      answer functions' q = answer functions q) :
    CoreMultisigSourceScan.scanAtStack script
      (CoreFinalChecksigEval.checker validKey
        (JointSourceChecks.checker functions' tx selected ecdsa)) bottom =
    CoreMultisigSourceScan.scanAtStack script
      (CoreFinalChecksigEval.checker validKey
        (JointSourceChecks.checker functions tx selected ecdsa)) bottom := by
  cases keys : CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none => simp [CoreMultisigSourceScan.scanAtStack, keys]
  | some n =>
      by_cases badN : n < 0 ∨ n > 20
      · simp [CoreMultisigSourceScan.scanAtStack, keys, badN]
      · cases sigs : CoreMultisigCleanup.parseSourceCount bottom
            (n.toNat + 2) with
        | none => simp [CoreMultisigSourceScan.scanAtStack,
            keys, badN, sigs]
        | some m =>
            by_cases badM : m < 0 ∨ m > n
            · simp [CoreMultisigSourceScan.scanAtStack,
                keys, badN, sigs, badM]
            · by_cases short : bottom.length < n.toNat + m.toNat + 3
              · simp [CoreMultisigSourceScan.scanAtStack,
                  keys, badN, sigs, badM, short]
              · have tailAgree : ∀ q ∈ scanDigestTrace functions tx selected
                    validKey ecdsa DERSyntax.verifyAllEncoding
                    (CoreMultisigSourceScan.deletedScript script
                      bottom.reverse n.toNat m.toNat)
                    (CoreMultisigSourceScan.reachedSignatures bottom.reverse
                      n.toNat m.toNat)
                    (CoreMultisigSourceScan.reachedKeys bottom.reverse
                      n.toNat),
                    answer functions' q = answer functions q := by
                  intro q mem
                  exact agree q (by
                    simpa [scanAtStackDigestTrace, keys, badN, sigs,
                      badM, short] using mem)
                have resultEq := scan_result_congr functions functions'
                  tx selected validKey ecdsa DERSyntax.verifyAllEncoding
                  (CoreMultisigSourceScan.deletedScript script
                    bottom.reverse n.toNat m.toNat)
                  (CoreMultisigSourceScan.reachedSignatures bottom.reverse
                    n.toNat m.toNat)
                  (CoreMultisigSourceScan.reachedKeys bottom.reverse
                    n.toNat) tailAgree
                simpa [CoreMultisigSourceScan.scanAtStack, keys,
                  badN, sigs, badM, short] using resultEq

/-! ### Reached CHECKSIGVERIFY -/

/-- The source-shaped CHECKSIGVERIFY digest trace after its actual
FindAndDelete scriptCode. A failing DER gate or missing stack operand makes
no digest query. -/
def checksigDigestTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (script : Bytes) (s : CoreCheckedStep.State) : List Query :=
  match s.stack.reverse[0]?, s.stack.reverse[1]? with
  | some key, some sig =>
      if DERSyntax.verifyAllEncoding sig then
        pairDigestTrace functions tx selected validKey sig key
          (CoreFindAndDelete.run 880 script
            (CorePushSerialize.pushPattern sig))
      else []
  | _, _ => []

theorem checksigDigestTrace_length_le_two
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (script : Bytes) (s : CoreCheckedStep.State) :
    (checksigDigestTrace functions tx selected validKey script s).length ≤ 2 := by
  unfold checksigDigestTrace
  cases hkey : s.stack.reverse[0]? with
  | none => simp
  | some key =>
      cases hsig : s.stack.reverse[1]? with
      | none => simp
      | some sig =>
          by_cases der : DERSyntax.verifyAllEncoding sig = true
          · simpa [der] using pairDigestTrace_length_le_two functions tx
              selected validKey sig key
              (CoreFindAndDelete.run 880 script
                (CorePushSerialize.pushPattern sig))
          · simp [der]

/-- One CHECKSIGVERIFY source evaluation is causal in its recorded digest
queries, with fixed key validation and ECDSA functions. -/
theorem checksig_eval_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script sig key : Bytes)
    (agree : ∀ q ∈ (if DERSyntax.verifyAllEncoding sig then
        pairDigestTrace functions tx selected validKey sig key
          (CoreFindAndDelete.run 880 script
            (CorePushSerialize.pushPattern sig)) else []),
      answer functions' q = answer functions q) :
    CoreChecksigEval.evalBaseVerifyAllCore 880 script sig key validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) =
    CoreChecksigEval.evalBaseVerifyAllCore 880 script sig key validKey
      (JointSourceChecks.checker functions tx selected ecdsa) := by
  by_cases der : DERSyntax.verifyAllEncoding sig = true
  · have pairAgree : ∀ q ∈ pairDigestTrace functions tx selected validKey
        sig key (CoreFindAndDelete.run 880 script
          (CorePushSerialize.pushPattern sig)),
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by simpa [der] using mem)
    have pairEq := pair_checker_congr functions functions' tx selected
      validKey ecdsa sig key
      (CoreFindAndDelete.run 880 script
        (CorePushSerialize.pushPattern sig)) pairAgree
    cases last : sig.getLast? with
    | none => simp [CoreChecksigEval.evalBaseVerifyAllCore, der, last]
    | some hashType =>
        simpa [CoreChecksigEval.evalBaseVerifyAllCore, der, last,
          CoreFinalChecksigEval.checker] using congrArg some pairEq
  · simp [CoreChecksigEval.evalBaseVerifyAllCore, der]

/-- The checked CHECKSIGVERIFY step has the same success or failure under
oracle agreement on its reached legacy-digest queries. -/
theorem checkedChecksig_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (s : CoreCheckedStep.State)
    (agree : ∀ q ∈ checksigDigestTrace functions tx selected validKey
        script s,
      answer functions' q = answer functions q) :
    CoreCheckedStep.checkedChecksig script validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) s =
    CoreCheckedStep.checkedChecksig script validKey
      (JointSourceChecks.checker functions tx selected ecdsa) s := by
  unfold CoreCheckedStep.checkedChecksig
  by_cases capExceeded : s.ops + 1 > 201
  · simp [capExceeded]
  · simp only [capExceeded, ↓reduceIte]
    cases keyAt : s.stack.reverse[0]? with
    | none => simp
    | some key =>
        cases sigAt : s.stack.reverse[1]? with
        | none => simp
        | some sig =>
            have evalEq := checksig_eval_congr functions functions' tx
              selected validKey ecdsa script sig key
              (fun q mem => agree q (by
                simpa [checksigDigestTrace, keyAt, sigAt] using mem))
            simp [evalEq]

/-- The checked CHECKMULTISIG transition is causal in the reached scan's
digest queries; its count parsing, stack cleanup, and Boolean record are
otherwise oracle-independent in the source model. -/
theorem checkedMultisig_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (s : CoreCheckedStep.State)
    (agree : ∀ q ∈ scanAtStackDigestTrace functions tx selected validKey
        ecdsa script s.stack,
      answer functions' q = answer functions q) :
    CoreCheckedStep.checkedMultisig script validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) s =
    CoreCheckedStep.checkedMultisig script validKey
      (JointSourceChecks.checker functions tx selected ecdsa) s := by
  have scanEq := scanAtStack_result_congr functions functions' tx selected
    validKey ecdsa script s.stack agree
  unfold CoreCheckedStep.checkedMultisig
  simp only [scanEq]

end QSB.CheckedRunQueryTrace
