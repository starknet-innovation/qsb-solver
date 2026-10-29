import QSB.FullCheckedRunQueries

/-!
Classical oracle-agreement causality for the ordered source-model checked-run
dependency trace. The lock, transaction, selected input, key validator, and
ECDSA predicate are fixed across the two worlds. This is a theorem about pure
Lean functions; it neither instruments compiled Bitcoin Core nor supplies a
coherent-query or quantum security bound. On failed runs the dependency trace
may conservatively include queries suppressed by an earlier guard.
-/
namespace QSB.FullCheckedRunCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Agreement on one source-shaped pair scan's recorded queries fixes the
adaptive order and inputs of all its digest queries. -/
theorem scanDigestTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (encoding : Bytes → Bool) (scriptCode : Bytes) :
    ∀ (sigs keys : List Bytes),
      (∀ q ∈ CheckedRunQueryTrace.scanDigestTrace functions tx selected
        validKey ecdsa encoding scriptCode sigs keys,
        answer functions' q = answer functions q) →
      CheckedRunQueryTrace.scanDigestTrace functions' tx selected validKey
        ecdsa encoding scriptCode sigs keys =
      CheckedRunQueryTrace.scanDigestTrace functions tx selected validKey
        ecdsa encoding scriptCode sigs keys
  | sigs, [] => by cases sigs <;> simp [CheckedRunQueryTrace.scanDigestTrace]
  | [], _ :: _ => by simp [CheckedRunQueryTrace.scanDigestTrace]
  | sig :: sigs, key :: keys => by
      intro agree
      by_cases impossible : (sig :: sigs).length > (key :: keys).length
      · have guard : keys.length < sigs.length := by
          simp only [List.length_cons] at impossible
          omega
        simp [CheckedRunQueryTrace.scanDigestTrace, guard]
      · by_cases encoded : encoding sig = true
        · have guard : ¬ keys.length < sigs.length := by
            simp only [List.length_cons] at impossible
            omega
          have currentAgree : ∀ q ∈
              CheckedRunQueryTrace.pairDigestTrace functions tx selected
                validKey sig key scriptCode,
              answer functions' q = answer functions q := by
            intro q mem
            exact agree q (by
              simp [CheckedRunQueryTrace.scanDigestTrace, guard,
                encoded, mem])
          have pairTraceEq := CheckedRunQueryTrace.pairDigestTrace_congr
            functions functions' tx selected validKey sig key scriptCode
            currentAgree
          have pairEq := CheckedRunQueryTrace.pair_checker_congr
            functions functions' tx selected validKey ecdsa sig key
            scriptCode currentAgree
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
          · have tailAgree : ∀ q ∈
                CheckedRunQueryTrace.scanDigestTrace functions tx selected
                  validKey ecdsa encoding scriptCode sigs keys,
                answer functions' q = answer functions q := by
              intro q mem
              exact agree q (by
                simp [CheckedRunQueryTrace.scanDigestTrace, guard,
                  encoded, verified, mem])
            have tailEq := scanDigestTrace_congr functions functions' tx
              selected validKey ecdsa encoding scriptCode sigs keys
              tailAgree
            simp [CheckedRunQueryTrace.scanDigestTrace, guard, encoded,
              verifyEq, verified, pairTraceEq, tailEq]
          · have tailAgree : ∀ q ∈
                CheckedRunQueryTrace.scanDigestTrace functions tx selected
                  validKey ecdsa encoding scriptCode (sig :: sigs) keys,
                answer functions' q = answer functions q := by
              intro q mem
              exact agree q (by
                simp [CheckedRunQueryTrace.scanDigestTrace, guard,
                  encoded, verified, mem])
            have tailEq := scanDigestTrace_congr functions functions' tx
              selected validKey ecdsa encoding scriptCode (sig :: sigs)
              keys tailAgree
            simp [CheckedRunQueryTrace.scanDigestTrace, guard, encoded,
              verifyEq, verified, pairTraceEq, tailEq]
        · have guard : ¬ keys.length < sigs.length := by
            simp only [List.length_cons] at impossible
            omega
          simp [CheckedRunQueryTrace.scanDigestTrace, guard, encoded]

/-- The source-shaped count parsing and FindAndDelete entry point add no
world dependence beyond the reached pair-scan trace. -/
theorem scanAtStackDigestTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (bottom : List Bytes)
    (agree : ∀ q ∈ CheckedRunQueryTrace.scanAtStackDigestTrace functions
      tx selected validKey ecdsa script bottom,
      answer functions' q = answer functions q) :
    CheckedRunQueryTrace.scanAtStackDigestTrace functions' tx selected
      validKey ecdsa script bottom =
    CheckedRunQueryTrace.scanAtStackDigestTrace functions tx selected
      validKey ecdsa script bottom := by
  cases keys : CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none => simp [CheckedRunQueryTrace.scanAtStackDigestTrace, keys]
  | some n =>
      by_cases badN : n < 0 ∨ n > 20
      · simp [CheckedRunQueryTrace.scanAtStackDigestTrace, keys, badN]
      · cases sigs : CoreMultisigCleanup.parseSourceCount bottom
            (n.toNat + 2) with
        | none => simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
            keys, badN, sigs]
        | some m =>
            by_cases badM : m < 0 ∨ m > n
            · simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
                keys, badN, sigs, badM]
            · by_cases short : bottom.length < n.toNat + m.toNat + 3
              · simp [CheckedRunQueryTrace.scanAtStackDigestTrace,
                  keys, badN, sigs, badM, short]
              · have scanAgree : ∀ q ∈
                    CheckedRunQueryTrace.scanDigestTrace functions tx
                      selected validKey ecdsa DERSyntax.verifyAllEncoding
                      (CoreMultisigSourceScan.deletedScript script
                        bottom.reverse n.toNat m.toNat)
                      (CoreMultisigSourceScan.reachedSignatures
                        bottom.reverse n.toNat m.toNat)
                      (CoreMultisigSourceScan.reachedKeys
                        bottom.reverse n.toNat),
                    answer functions' q = answer functions q := by
                  intro q mem
                  exact agree q (by
                    simpa [CheckedRunQueryTrace.scanAtStackDigestTrace,
                      keys, badN, sigs, badM, short] using mem)
                have scanEq := scanDigestTrace_congr functions functions'
                  tx selected validKey ecdsa DERSyntax.verifyAllEncoding
                  (CoreMultisigSourceScan.deletedScript script
                    bottom.reverse n.toNat m.toNat)
                  (CoreMultisigSourceScan.reachedSignatures
                    bottom.reverse n.toNat m.toNat)
                  (CoreMultisigSourceScan.reachedKeys bottom.reverse n.toNat)
                  scanAgree
                simpa [CheckedRunQueryTrace.scanAtStackDigestTrace,
                  keys, badN, sigs, badM, short] using scanEq

/-- A successful CHECKSIGVERIFY checker fixes the adaptive second digest
query input when the two worlds agree on its recorded queries. -/
theorem checksigDigestTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (script : Bytes) (s : CoreCheckedStep.State)
    (agree : ∀ q ∈ CheckedRunQueryTrace.checksigDigestTrace functions
      tx selected validKey script s,
      answer functions' q = answer functions q) :
    CheckedRunQueryTrace.checksigDigestTrace functions' tx selected
      validKey script s =
    CheckedRunQueryTrace.checksigDigestTrace functions tx selected
      validKey script s := by
  cases keyAt : s.stack.reverse[0]? with
  | none => simp [CheckedRunQueryTrace.checksigDigestTrace, keyAt]
  | some key =>
      cases sigAt : s.stack.reverse[1]? with
      | none => simp [CheckedRunQueryTrace.checksigDigestTrace,
          keyAt, sigAt]
      | some sig =>
          by_cases der : DERSyntax.verifyAllEncoding sig = true
          · have pairAgree : ∀ q ∈
                CheckedRunQueryTrace.pairDigestTrace functions tx selected
                  validKey sig key
                  (CoreFindAndDelete.run 880 script
                    (CorePushSerialize.pushPattern sig)),
                answer functions' q = answer functions q := by
              intro q mem
              exact agree q (by
                simpa [CheckedRunQueryTrace.checksigDigestTrace,
                  keyAt, sigAt, der] using mem)
            have pairEq := CheckedRunQueryTrace.pairDigestTrace_congr
              functions functions' tx selected validKey sig key
              (CoreFindAndDelete.run 880 script
                (CorePushSerialize.pushPattern sig)) pairAgree
            simpa [CheckedRunQueryTrace.checksigDigestTrace,
              keyAt, sigAt, der] using pairEq
          · simp [CheckedRunQueryTrace.checksigDigestTrace,
              keyAt, sigAt, der]

/-- The adaptive R input of HASH160 is fixed by agreement on its preceding
H query. All other opcode query lists are world-independent. -/
theorem opcodeStepQueries_congr
    (functions functions' : JointSourceChecks.Functions)
    (op : Op) (stack : List Bytes)
    (agree : ∀ q ∈ ByteMachineQueries.stepQueries functions op stack,
      answer functions' q = answer functions q) :
    ByteMachineQueries.stepQueries functions' op stack =
      ByteMachineQueries.stepQueries functions op stack := by
  by_cases hash160 : op = .hash160
  · subst op
    cases stack with
    | nil => rfl
    | cons x xs =>
        have first : functions'.H x = functions.H x :=
          agree (.H x) (by simp [ByteMachineQueries.stepQueries])
        simp [ByteMachineQueries.stepQueries, first]
  · cases op <;> cases stack <;>
      simp_all [ByteMachineQueries.stepQueries]

private theorem stepQueries_eq_opcode
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (s : CoreCheckedStep.State)
    (notSig : op ≠ .checksigverify)
    (notMulti : op ≠ .checkmultisig) :
    FullCheckedRunQueries.stepQueries functions tx selected validKey
      ecdsa script op s =
    ByteMachineQueries.stepQueries functions op s.stack.reverse := by
  cases op <;> simp_all [FullCheckedRunQueries.stepQueries]

/-- A checked step's dependency list has the same adaptive query inputs in
both worlds under agreement on the first world's list. -/
theorem stepQueries_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (s : CoreCheckedStep.State)
    (agree : ∀ q ∈ FullCheckedRunQueries.stepQueries functions tx
      selected validKey ecdsa script op s,
      answer functions' q = answer functions q) :
    FullCheckedRunQueries.stepQueries functions' tx selected validKey
      ecdsa script op s =
    FullCheckedRunQueries.stepQueries functions tx selected validKey
      ecdsa script op s := by
  by_cases sigOp : op = .checksigverify
  · subst op
    exact checksigDigestTrace_congr functions functions' tx selected
      validKey script s agree
  · by_cases multiOp : op = .checkmultisig
    · subst op
      exact scanAtStackDigestTrace_congr functions functions' tx selected
        validKey ecdsa script s.stack agree
    · have opcodeAgree : ∀ q ∈
          ByteMachineQueries.stepQueries functions op s.stack.reverse,
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by
          rw [stepQueries_eq_opcode functions tx selected validKey ecdsa
            script op s sigOp multiOp]
          exact mem)
      rw [stepQueries_eq_opcode functions' tx selected validKey ecdsa
        script op s sigOp multiOp,
        stepQueries_eq_opcode functions tx selected validKey ecdsa
          script op s sigOp multiOp]
      exact opcodeStepQueries_congr functions functions' op
        s.stack.reverse opcodeAgree

/-- An ordinary checked transition is causal in the byte opcode's H/R
queries, after reversing Core's bottom-first stack. -/
theorem ordinary_step_congr
    (functions functions' : JointSourceChecks.Functions)
    (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (op : Op) (s : CoreCheckedStep.State)
    (notSig : op ≠ .checksigverify)
    (notMulti : op ≠ .checkmultisig)
    (agree : ∀ q ∈ ByteMachineQueries.stepQueries functions op
      s.stack.reverse,
      answer functions' q = answer functions q) :
    CoreCheckedStep.step (JointSourceChecks.hashes functions') script
      validKey verify op s =
    CoreCheckedStep.step (JointSourceChecks.hashes functions) script
      validKey verify op s := by
  let bs : ByteMachine.State := ⟨s.stack.reverse, [], s.ops⟩
  have supported : CoreOpcodeStep.supported op = true := by
    cases op <;> simp_all [CoreOpcodeStep.supported]
  have byteEq := ByteMachineQueries.step_congr functions functions' op bs
    (by simpa [bs] using agree)
  have left := CoreOpcodeStep.step_eq_byte
    (JointSourceChecks.hashes functions') op bs supported
  have right := CoreOpcodeStep.step_eq_byte
    (JointSourceChecks.hashes functions) op bs supported
  have coreEq :
      CoreOpcodeStep.step (JointSourceChecks.hashes functions') op
        ⟨s.stack, [], s.ops⟩ =
      CoreOpcodeStep.step (JointSourceChecks.hashes functions) op
        ⟨s.stack, [], s.ops⟩ := by
    have mapped := congrArg (Option.map CoreOpcodeStep.ofByte) byteEq
    simpa [bs, CoreOpcodeStep.ofByte] using
      left.trans (mapped.trans right.symm)
  cases op <;> simp_all [CoreCheckedStep.step]

/-- Agreement on one checked step's H/R dependency list fixes its source
transition and computed signature result. -/
theorem step_result_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (s : CoreCheckedStep.State)
    (agree : ∀ q ∈ FullCheckedRunQueries.stepQueries functions tx
      selected validKey ecdsa script op s,
      answer functions' q = answer functions q) :
    CoreCheckedStep.step (JointSourceChecks.hashes functions') script
      validKey (JointSourceChecks.checker functions' tx selected ecdsa)
      op s =
    CoreCheckedStep.step (JointSourceChecks.hashes functions) script
      validKey (JointSourceChecks.checker functions tx selected ecdsa)
      op s := by
  by_cases sigOp : op = .checksigverify
  · subst op
    have same := CheckedRunQueryTrace.checkedChecksig_congr
      functions functions' tx selected validKey ecdsa script s agree
    simp [CoreCheckedStep.step, same]
  · by_cases multiOp : op = .checkmultisig
    · subst op
      have same := CheckedRunQueryTrace.checkedMultisig_congr
        functions functions' tx selected validKey ecdsa script s agree
      simp [CoreCheckedStep.step, same]
    · have opcodeAgree : ∀ q ∈
          ByteMachineQueries.stepQueries functions op s.stack.reverse,
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by
          rw [stepQueries_eq_opcode functions tx selected validKey ecdsa
            script op s sigOp multiOp]
          exact mem)
      have same := ordinary_step_congr functions functions' script
        validKey (JointSourceChecks.checker functions tx selected ecdsa)
        op s sigOp multiOp opcodeAgree
      cases op <;> simp_all [CoreCheckedStep.step]

private theorem stepQueries_mem_runQueries
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (rest : List Op)
    (s : CoreCheckedStep.State) (q : Query)
    (mem : q ∈ FullCheckedRunQueries.stepQueries functions tx selected
      validKey ecdsa script op s) :
    q ∈ FullCheckedRunQueries.runQueries functions tx selected validKey
      ecdsa script (op :: rest) s := by
  simp only [FullCheckedRunQueries.runQueries]
  cases CoreCheckedStep.step (JointSourceChecks.hashes functions) script
      validKey (JointSourceChecks.checker functions tx selected ecdsa)
      op s with
  | none => exact mem
  | some pair =>
      obtain ⟨next, record⟩ := pair
      by_cases large : next.stack.length > 1000 <;> simp [large, mem]

private theorem laterQueries_mem_runQueries
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (rest : List Op)
    (s next : CoreCheckedStep.State) (record : Option Bool) (q : Query)
    (hstep : CoreCheckedStep.step (JointSourceChecks.hashes functions)
      script validKey (JointSourceChecks.checker functions tx selected ecdsa)
      op s = some (next, record))
    (small : ¬ next.stack.length > 1000)
    (mem : q ∈ FullCheckedRunQueries.runQueries functions tx selected
      validKey ecdsa script rest next) :
    q ∈ FullCheckedRunQueries.runQueries functions tx selected validKey
      ecdsa script (op :: rest) s := by
  simp [FullCheckedRunQueries.runQueries, hstep, small, mem]

/-- Whole-run classical causality of the source-model dependency list. The
second pure H/R pair yields the same checked result and the same ordered
trace when it agrees on every query in the first run's list. -/
theorem run_and_queries_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) :
    ∀ (ops : List Op) (s : CoreCheckedStep.State),
      (∀ q ∈ FullCheckedRunQueries.runQueries functions tx selected
        validKey ecdsa script ops s,
        answer functions' q = answer functions q) →
      CoreCheckedStep.run (JointSourceChecks.hashes functions') script
          validKey (JointSourceChecks.checker functions' tx selected ecdsa)
          ops s =
        CoreCheckedStep.run (JointSourceChecks.hashes functions) script
          validKey (JointSourceChecks.checker functions tx selected ecdsa)
          ops s ∧
      FullCheckedRunQueries.runQueries functions' tx selected validKey
          ecdsa script ops s =
        FullCheckedRunQueries.runQueries functions tx selected validKey
          ecdsa script ops s
  | [], s, _ => by simp [CoreCheckedStep.run, FullCheckedRunQueries.runQueries]
  | op :: rest, s, agree => by
      have currentAgree : ∀ q ∈ FullCheckedRunQueries.stepQueries
          functions tx selected validKey ecdsa script op s,
          answer functions' q = answer functions q :=
        fun q mem => agree q (stepQueries_mem_runQueries functions tx
          selected validKey ecdsa script op rest s q mem)
      have sameStep := step_result_congr functions functions' tx selected
        validKey ecdsa script op s currentAgree
      have sameQueries := stepQueries_congr functions functions' tx
        selected validKey ecdsa script op s currentAgree
      simp only [CoreCheckedStep.run, FullCheckedRunQueries.runQueries,
        sameStep, sameQueries]
      cases hstep : CoreCheckedStep.step (JointSourceChecks.hashes functions)
          script validKey (JointSourceChecks.checker functions tx selected ecdsa)
          op s with
      | none => simp
      | some pair =>
          obtain ⟨next, record⟩ := pair
          by_cases large : next.stack.length > 1000
          · simp [large]
          · have tailAgree : ∀ q ∈ FullCheckedRunQueries.runQueries
                functions tx selected validKey ecdsa script rest next,
                answer functions' q = answer functions q :=
              fun q mem => agree q (laterQueries_mem_runQueries functions
                tx selected validKey ecdsa script op rest s next record q
                hstep large mem)
            have tail := run_and_queries_congr functions functions' tx
              selected validKey ecdsa script rest next tailAgree
            simp [large, tail.1, tail.2]

/-- The parameterized checked lock is causal in its one ordered source-model
dependency list, with fixed script, transaction, selected input, key parser,
and ECDSA predicate. This does not charge their construction or internals. -/
theorem checked_lock_run_and_queries_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (lock : DynamicCheckedCertificate.Lock)
    (s : CoreCheckedStep.State)
    (agree : ∀ q ∈ FullCheckedRunQueries.runQueries functions tx selected
      validKey ecdsa (DynamicCheckedCertificate.wire lock)
      (DynamicCheckedCertificate.program lock) s,
      answer functions' q = answer functions q) :
    CoreCheckedStep.run (JointSourceChecks.hashes functions')
        (DynamicCheckedCertificate.wire lock) validKey
        (JointSourceChecks.checker functions' tx selected ecdsa)
        (DynamicCheckedCertificate.program lock) s =
      CoreCheckedStep.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.wire lock) validKey
        (JointSourceChecks.checker functions tx selected ecdsa)
        (DynamicCheckedCertificate.program lock) s ∧
    FullCheckedRunQueries.runQueries functions' tx selected validKey ecdsa
        (DynamicCheckedCertificate.wire lock)
        (DynamicCheckedCertificate.program lock) s =
      FullCheckedRunQueries.runQueries functions tx selected validKey ecdsa
        (DynamicCheckedCertificate.wire lock)
        (DynamicCheckedCertificate.program lock) s :=
  run_and_queries_congr functions functions' tx selected validKey ecdsa
    (DynamicCheckedCertificate.wire lock)
    (DynamicCheckedCertificate.program lock) s agree

end QSB.FullCheckedRunCausality
