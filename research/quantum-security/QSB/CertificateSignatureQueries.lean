import QSB.FullCheckedRunCausality

/-!
Local H/R dependency traces for the source certificate's direct-push
CHECKSIGVERIFY evaluator and the final ten-key multisignature evaluator.
These are source-model statements with the transaction, script, key validator,
and ECDSA predicate fixed. They do not cover the rest of the certificate
search, external function internals, scriptSig, or compiled Core.
-/
namespace QSB.CertificateSignatureQueries
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- The reached digest queries of the source-side direct-push CHECKSIGVERIFY
check. Invalid DER exits before any modeled digest query. -/
def sourceChecksigTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool) (script sig key : Bytes) : List Query :=
  if DERSyntax.verifyAllEncoding sig then
    CheckedRunQueryTrace.pairDigestTrace functions tx selected validKey
      sig key (CoreFindAndDelete.run 880 script
        (CorePushSerialize.pushPattern sig))
  else []

theorem sourceChecksigTrace_length_le_two
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool) (script sig key : Bytes) :
    (sourceChecksigTrace functions tx selected validKey
      script sig key).length ≤ 2 := by
  unfold sourceChecksigTrace
  split_ifs
  · exact CheckedRunQueryTrace.pairDigestTrace_length_le_two
      functions tx selected validKey sig key
        (CoreFindAndDelete.run 880 script
          (CorePushSerialize.pushPattern sig))
  · simp

theorem sourceChecksigTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool) (script sig key : Bytes)
    (agree : ∀ q ∈ sourceChecksigTrace functions tx selected validKey
      script sig key, answer functions' q = answer functions q) :
    sourceChecksigTrace functions' tx selected validKey script sig key =
      sourceChecksigTrace functions tx selected validKey script sig key := by
  by_cases der : DERSyntax.verifyAllEncoding sig = true
  · have pairAgree : ∀ q ∈ CheckedRunQueryTrace.pairDigestTrace functions
        tx selected validKey sig key
        (CoreFindAndDelete.run 880 script
          (CorePushSerialize.pushPattern sig)),
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by simpa [sourceChecksigTrace, der] using mem)
    have pairEq := CheckedRunQueryTrace.pairDigestTrace_congr
      functions functions' tx selected validKey sig key
      (CoreFindAndDelete.run 880 script
        (CorePushSerialize.pushPattern sig)) pairAgree
    simpa [sourceChecksigTrace, der] using pairEq
  · simp [sourceChecksigTrace, der]

/-- Source direct-push and Core-push source evaluators have the same result,
so the existing CHECKSIGVERIFY dependency proof applies to this site. -/
theorem evalBaseVerifyAll_source_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script sig key : Bytes)
    (agree : ∀ q ∈ sourceChecksigTrace functions tx selected validKey
      script sig key, answer functions' q = answer functions q) :
    CoreChecksigEval.evalBaseVerifyAll 880 script sig key validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) =
    CoreChecksigEval.evalBaseVerifyAll 880 script sig key validKey
      (JointSourceChecks.checker functions tx selected ecdsa) := by
  rw [CoreChecksigEval.evalBaseVerifyAll_eq_core,
    CoreChecksigEval.evalBaseVerifyAll_eq_core]
  exact CheckedRunQueryTrace.checksig_eval_congr functions functions'
    tx selected validKey ecdsa script sig key
    (by simpa [sourceChecksigTrace] using agree)

/-- The final fixed ten-key scan's legacy-digest queries after its count and
capacity gate, including paths whose NULLDUMMY check later fails. -/
def finalTenDigestTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (top : List Bytes) : List Query :=
  if top[0]? = some [0x0a] ∧ top[11]? = some [0x0a] ∧
      23 ≤ top.length then
    CheckedRunQueryTrace.scanDigestTrace functions tx selected validKey
      ecdsa DERSyntax.verifyAllEncoding
      (CoreMultisigEval.deletedScript script top)
      (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10)
  else []

theorem finalTenDigestTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (top : List Bytes)
    (agree : ∀ q ∈ finalTenDigestTrace functions tx selected validKey
      ecdsa script top, answer functions' q = answer functions q) :
    finalTenDigestTrace functions' tx selected validKey ecdsa script top =
      finalTenDigestTrace functions tx selected validKey ecdsa script top := by
  by_cases gate : top[0]? = some [0x0a] ∧ top[11]? = some [0x0a] ∧
      23 ≤ top.length
  · have scanAgree : ∀ q ∈ CheckedRunQueryTrace.scanDigestTrace functions
        tx selected validKey ecdsa DERSyntax.verifyAllEncoding
        (CoreMultisigEval.deletedScript script top)
        (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10),
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by simpa [finalTenDigestTrace, gate] using mem)
    have scanEq := FullCheckedRunCausality.scanDigestTrace_congr
      functions functions' tx selected validKey ecdsa
      DERSyntax.verifyAllEncoding (CoreMultisigEval.deletedScript script top)
      (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10)
      scanAgree
    simpa [finalTenDigestTrace, gate] using scanEq
  · simp [finalTenDigestTrace, gate]

theorem finalTenDigestTrace_length_le_20
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (top : List Bytes) :
    (finalTenDigestTrace functions tx selected validKey ecdsa
      script top).length ≤ 20 := by
  unfold finalTenDigestTrace
  split_ifs
  · have bound := CheckedRunQueryTrace.scanDigestTrace_length_le
      functions tx selected validKey ecdsa DERSyntax.verifyAllEncoding
      (CoreMultisigEval.deletedScript script top)
      (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10)
    have keys : ((top.drop 1).take 10).length ≤ 10 := by simp
    omega
  · simp

/-- Agreement on the reached final scan's H/R dependency inputs preserves
its optional Boolean result, including fatal DER and NULLDUMMY exits. -/
theorem finalTenEval_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (top : List Bytes)
    (agree : ∀ q ∈ finalTenDigestTrace functions tx selected validKey
      ecdsa script top, answer functions' q = answer functions q) :
    CoreMultisigEval.finalTenEval script
      (CoreFinalChecksigEval.checker validKey
        (JointSourceChecks.checker functions' tx selected ecdsa)) top =
    CoreMultisigEval.finalTenEval script
      (CoreFinalChecksigEval.checker validKey
        (JointSourceChecks.checker functions tx selected ecdsa)) top := by
  by_cases gate : top[0]? = some [0x0a] ∧ top[11]? = some [0x0a] ∧
      23 ≤ top.length
  · have scanAgree : ∀ q ∈ CheckedRunQueryTrace.scanDigestTrace functions
        tx selected validKey ecdsa DERSyntax.verifyAllEncoding
        (CoreMultisigEval.deletedScript script top)
        (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10),
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by simpa [finalTenDigestTrace, gate] using mem)
    have scanEq := CheckedRunQueryTrace.scan_result_congr
      functions functions' tx selected validKey ecdsa
      DERSyntax.verifyAllEncoding
      (CoreMultisigEval.deletedScript script top)
      (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10)
      scanAgree
    simp only [List.drop_one] at scanEq
    simp only [CoreMultisigEval.finalTenEval, if_pos gate]
    simp only [List.drop_one]
    rw [scanEq]
  · simp [CoreMultisigEval.finalTenEval, gate]

end QSB.CertificateSignatureQueries
