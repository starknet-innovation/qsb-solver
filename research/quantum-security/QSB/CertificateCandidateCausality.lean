import QSB.CertificateStructuralQueries
import QSB.CertificateSignatureQueries

/-!
An eager, conservative H/R dependency list for one source-model certificate
candidate. It includes the seven structural runs and the reached signature
digest checks. The list can include checks that `candidate` short-circuits and
places the final structural prefix before the source-site digest checks, even
though the candidate evaluates that prefix later. It is a result-dependency
inventory, not an operational trace in source execution order.

The transaction, lock, initial stack, key validator, and ECDSA predicate are
held fixed across oracle worlds. Calls hidden inside those external functions,
scriptSig evaluation, lock construction, and compiled Bitcoin Core are not
accounted for by this trace.
-/
namespace QSB.CertificateCandidateCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

private def sigTraceAt (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool) (n : Nat) :
    List Query :=
  match CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take n)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => []
  | some reached =>
      CertificateSignatureQueries.sourceChecksigTrace functions tx selected
        validKey (DynamicCheckedCertificate.wire lock)
        (reached.stack.reverse[1]?.getD [])
        (reached.stack.reverse[0]?.getD [])

private def firstScanTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) : List Query :=
  match CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 446)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => []
  | some reached =>
      CheckedRunQueryTrace.scanAtStackDigestTrace functions tx selected
        validKey ecdsa (DynamicCheckedCertificate.wire lock) reached.stack

private theorem sigTraceAt_length_le_two
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool) (n : Nat) :
    (sigTraceAt functions tx selected lock stack firstRound validKey n).length
      ≤ 2 := by
  unfold sigTraceAt
  split
  · simp
  · exact CertificateSignatureQueries.sourceChecksigTrace_length_le_two
      functions tx selected validKey _ _ _

private theorem scanAtStackDigestTrace_length_le_40
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (bottom : List Bytes) :
    (CheckedRunQueryTrace.scanAtStackDigestTrace functions tx selected
      validKey ecdsa script bottom).length ≤ 40 := by
  unfold CheckedRunQueryTrace.scanAtStackDigestTrace
  cases keys : CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none => simp
  | some n =>
      by_cases badN : n < 0 ∨ n > 20
      · simp [badN]
      · cases sigs : CoreMultisigCleanup.parseSourceCount bottom
          (n.toNat + 2) with
        | none => simp [badN, sigs]
        | some m =>
            by_cases badM : m < 0 ∨ m > n
            · simp [sigs, badN, badM]
            · by_cases short : n.toNat + m.toNat + 3 > bottom.length
              · simp [sigs, badN, badM, short]
              · have traceBound :=
                  CheckedRunQueryTrace.scanDigestTrace_length_le
                    functions tx selected validKey ecdsa
                    DERSyntax.verifyAllEncoding
                    (CoreMultisigSourceScan.deletedScript script
                      bottom.reverse n.toNat m.toNat)
                    (CoreMultisigSourceScan.reachedSignatures
                      bottom.reverse n.toNat m.toNat)
                    (CoreMultisigSourceScan.reachedKeys bottom.reverse n.toNat)
                have keysLength :
                    (CoreMultisigSourceScan.reachedKeys
                      bottom.reverse n.toNat).length ≤ n.toNat := by
                  simp [CoreMultisigSourceScan.reachedKeys]
                have nLe : n.toNat ≤ 20 := by omega
                have target :
                    (CheckedRunQueryTrace.scanDigestTrace functions tx selected
                      validKey ecdsa DERSyntax.verifyAllEncoding
                      (CoreMultisigSourceScan.deletedScript script
                        bottom.reverse n.toNat m.toNat)
                      (CoreMultisigSourceScan.reachedSignatures
                        bottom.reverse n.toNat m.toNat)
                      (CoreMultisigSourceScan.reachedKeys
                        bottom.reverse n.toNat)).length ≤ 40 := by omega
                simpa [sigs, badN, badM, short] using target

private theorem firstScanTrace_length_le_40
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    (firstScanTrace functions tx selected lock stack firstRound
      validKey ecdsa).length ≤ 40 := by
  unfold firstScanTrace
  split
  · simp
  · exact scanAtStackDigestTrace_length_le_40 functions tx selected
      validKey ecdsa (DynamicCheckedCertificate.wire lock) _

/-- Digest dependencies at the four source-side CHECKSIGVERIFY sites and the
first CHECKMULTISIG scan. Each trace uses its reached structural prefix stack. -/
def sourceSitesDigestTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) : List Query :=
  sigTraceAt functions tx selected lock stack firstRound validKey 2 ++
  sigTraceAt functions tx selected lock stack firstRound validKey 5 ++
  sigTraceAt functions tx selected lock stack firstRound validKey 423 ++
  sigTraceAt functions tx selected lock stack firstRound validKey 856 ++
  firstScanTrace functions tx selected lock stack firstRound validKey ecdsa

/-- Digest dependencies of the final ten-key source evaluator on the reached
prefix stack. -/
def finalCheckedDigestTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) : List Query :=
  match CoreStructuralRun.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => []
  | some reached =>
      CertificateSignatureQueries.finalTenDigestTrace functions tx selected
        validKey ecdsa (DynamicCheckedCertificate.wire lock)
        reached.stack.reverse

/-- All explicit H/R dependencies of one candidate, including repeated
structural work. This eagerly lists the final prefix before source-site digest
checks and is not an operational extractor trace. -/
def candidateDependencies (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) : List Query :=
  CertificateStructuralQueries.structuralDependencies functions lock stack
      firstRound ++
    sourceSitesDigestTrace functions tx selected lock stack firstRound
      validKey ecdsa ++
    finalCheckedDigestTrace functions tx selected lock stack firstRound
      validKey ecdsa

private theorem sig_eval_congr_at
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) (n : Nat)
    (reached : CoreOpcodeStep.State)
    (runEq : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take n)
      (DynamicCheckedCertificate.initial stack firstRound) = some reached)
    (agree : ∀ q ∈ sigTraceAt functions tx selected lock stack firstRound
      validKey n, answer functions' q = answer functions q) :
    CoreChecksigEval.evalBaseVerifyAll 880
      (DynamicCheckedCertificate.wire lock)
      (reached.stack.reverse[1]?.getD [])
      (reached.stack.reverse[0]?.getD []) validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) =
    CoreChecksigEval.evalBaseVerifyAll 880
      (DynamicCheckedCertificate.wire lock)
      (reached.stack.reverse[1]?.getD [])
      (reached.stack.reverse[0]?.getD []) validKey
      (JointSourceChecks.checker functions tx selected ecdsa) := by
  apply CertificateSignatureQueries.evalBaseVerifyAll_source_congr
    functions functions' tx selected validKey ecdsa
  intro q mem
  exact agree q (by simpa [sigTraceAt, runEq] using mem)

private theorem first_scan_congr_at
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (reached : CoreOpcodeStep.State)
    (runEq : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 446)
      (DynamicCheckedCertificate.initial stack firstRound) = some reached)
    (agree : ∀ q ∈ firstScanTrace functions tx selected lock stack
      firstRound validKey ecdsa,
      answer functions' q = answer functions q) :
    CoreMultisigSourceScan.scanAtStack
      (DynamicCheckedCertificate.wire lock)
      (CoreFinalChecksigEval.checker validKey
        (JointSourceChecks.checker functions' tx selected ecdsa))
      reached.stack =
    CoreMultisigSourceScan.scanAtStack
      (DynamicCheckedCertificate.wire lock)
      (CoreFinalChecksigEval.checker validKey
        (JointSourceChecks.checker functions tx selected ecdsa))
      reached.stack := by
  apply CheckedRunQueryTrace.scanAtStack_result_congr
    functions functions' tx selected validKey ecdsa
  intro q mem
  exact agree q (by simpa [firstScanTrace, runEq] using mem)

/-- The source certificate's four direct-push CHECKSIGVERIFY checks and first
multisignature scan are causal in their reached digest-query list. -/
theorem sourceSites_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock stack
        firstRound, answer functions' q = answer functions q)
    (digestAgree : ∀ q ∈ sourceSitesDigestTrace functions tx selected
      lock stack firstRound validKey ecdsa,
      answer functions' q = answer functions q) :
    DynamicCheckedCertificate.sourceSites
      (JointSourceChecks.hashes functions') lock stack validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) firstRound =
    DynamicCheckedCertificate.sourceSites
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) firstRound := by
  have allRuns := CertificateStructuralQueries.structural_runs_congr
    functions functions' lock stack firstRound structuralAgree
  have run2 := allRuns ((DynamicCheckedCertificate.program lock).take 2)
    (by simp [CertificateStructuralQueries.sitePrograms])
  have run5 := allRuns ((DynamicCheckedCertificate.program lock).take 5)
    (by simp [CertificateStructuralQueries.sitePrograms])
  have run423 := allRuns ((DynamicCheckedCertificate.program lock).take 423)
    (by simp [CertificateStructuralQueries.sitePrograms])
  have run446 := allRuns ((DynamicCheckedCertificate.program lock).take 446)
    (by simp [CertificateStructuralQueries.sitePrograms])
  have run856 := allRuns ((DynamicCheckedCertificate.program lock).take 856)
    (by simp [CertificateStructuralQueries.sitePrograms])
  have agree2 : ∀ q ∈ sigTraceAt functions tx selected lock stack
      firstRound validKey 2, answer functions' q = answer functions q := by
    intro q mem
    exact digestAgree q (by simp [sourceSitesDigestTrace, mem])
  have agree5 : ∀ q ∈ sigTraceAt functions tx selected lock stack
      firstRound validKey 5, answer functions' q = answer functions q := by
    intro q mem
    exact digestAgree q (by simp [sourceSitesDigestTrace, mem])
  have agree423 : ∀ q ∈ sigTraceAt functions tx selected lock stack
      firstRound validKey 423, answer functions' q = answer functions q := by
    intro q mem
    exact digestAgree q (by simp [sourceSitesDigestTrace, mem])
  have agree856 : ∀ q ∈ sigTraceAt functions tx selected lock stack
      firstRound validKey 856, answer functions' q = answer functions q := by
    intro q mem
    exact digestAgree q (by simp [sourceSitesDigestTrace, mem])
  have agreeScan : ∀ q ∈ firstScanTrace functions tx selected lock stack
      firstRound validKey ecdsa,
      answer functions' q = answer functions q := by
    intro q mem
    exact digestAgree q (by simp [sourceSitesDigestTrace, mem])
  unfold DynamicCheckedCertificate.sourceSites
  rw [run2, run5, run423, run446, run856]
  cases r2 : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 2)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => simp
  | some pin =>
    cases r5 : CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 5)
        (DynamicCheckedCertificate.initial stack firstRound) with
    | none => simp
    | some early =>
      cases r423 : CoreStructuralRun.run (JointSourceChecks.hashes functions)
          ((DynamicCheckedCertificate.program lock).take 423)
          (DynamicCheckedCertificate.initial stack firstRound) with
      | none => simp
      | some firstPuzzle =>
        cases r446 : CoreStructuralRun.run (JointSourceChecks.hashes functions)
            ((DynamicCheckedCertificate.program lock).take 446)
            (DynamicCheckedCertificate.initial stack firstRound) with
        | none => simp
        | some firstCheck =>
          cases r856 : CoreStructuralRun.run
              (JointSourceChecks.hashes functions)
              ((DynamicCheckedCertificate.program lock).take 856)
              (DynamicCheckedCertificate.initial stack firstRound) with
          | none => simp
          | some late =>
            have pinEq := sig_eval_congr_at functions functions' tx selected
              lock stack firstRound validKey ecdsa 2 pin r2 agree2
            have earlyEq := sig_eval_congr_at functions functions' tx selected
              lock stack firstRound validKey ecdsa 5 early r5 agree5
            have firstEq := sig_eval_congr_at functions functions' tx selected
              lock stack firstRound validKey ecdsa 423 firstPuzzle r423
              agree423
            have lateEq := sig_eval_congr_at functions functions' tx selected
              lock stack firstRound validKey ecdsa 856 late r856 agree856
            have scanEq := first_scan_congr_at functions functions' tx selected
              lock stack firstRound validKey ecdsa firstCheck r446 agreeScan
            simp [pinEq, earlyEq, firstEq, lateEq, scanEq]

/-- The final source scan has the same result when the structural prefix and
its reached digest queries agree. -/
theorem finalChecked_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock stack
        firstRound, answer functions' q = answer functions q)
    (digestAgree : ∀ q ∈ finalCheckedDigestTrace functions tx selected
      lock stack firstRound validKey ecdsa,
      answer functions' q = answer functions q) :
    DynamicCheckedCertificate.finalChecked
      (JointSourceChecks.hashes functions') lock stack validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) firstRound =
    DynamicCheckedCertificate.finalChecked
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) firstRound := by
  have prefixEq :=
    CertificateStructuralQueries.structural_runs_congr functions functions'
      lock stack firstRound structuralAgree
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (by simp [CertificateStructuralQueries.sitePrograms])
  unfold DynamicCheckedCertificate.finalChecked
  rw [prefixEq]
  cases reached : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => simp
  | some beforeCheck =>
      have localAgree : ∀ q ∈
          CertificateSignatureQueries.finalTenDigestTrace functions tx
            selected validKey ecdsa (DynamicCheckedCertificate.wire lock)
            beforeCheck.stack.reverse,
          answer functions' q = answer functions q := by
        intro q mem
        exact digestAgree q (by
          simpa [finalCheckedDigestTrace, reached] using mem)
      have finalEq := CertificateSignatureQueries.finalTenEval_congr
        functions functions' tx selected validKey ecdsa
        (DynamicCheckedCertificate.wire lock) beforeCheck.stack.reverse
        localAgree
      simp [finalEq]

theorem sourceSitesDigestTrace_length_le_48
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    (sourceSitesDigestTrace functions tx selected lock stack firstRound
      validKey ecdsa).length ≤ 48 := by
  have h2 := sigTraceAt_length_le_two functions tx selected lock stack
    firstRound validKey 2
  have h5 := sigTraceAt_length_le_two functions tx selected lock stack
    firstRound validKey 5
  have h423 := sigTraceAt_length_le_two functions tx selected lock stack
    firstRound validKey 423
  have h856 := sigTraceAt_length_le_two functions tx selected lock stack
    firstRound validKey 856
  have hscan := firstScanTrace_length_le_40 functions tx selected lock stack
    firstRound validKey ecdsa
  simp only [sourceSitesDigestTrace, List.length_append]
  omega

theorem finalCheckedDigestTrace_length_le_20
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    (finalCheckedDigestTrace functions tx selected lock stack firstRound
      validKey ecdsa).length ≤ 20 := by
  unfold finalCheckedDigestTrace
  split
  · simp
  · exact CertificateSignatureQueries.finalTenDigestTrace_length_le_20
      functions tx selected validKey ecdsa
      (DynamicCheckedCertificate.wire lock) _

/-- An eager candidate dependency inventory has at most 299 H/R entries:
231 structural, 48 from the four CHECKSIGVERIFY sites plus an arbitrary
at-most-20-key first scan, and 20 from the final ten-key scan. The bound does
not include oracle work inside externally supplied functions. -/
theorem candidateDependencies_length_le_299
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    (candidateDependencies functions tx selected lock stack firstRound
      validKey ecdsa).length ≤ 299 := by
  have structural :=
    CertificateStructuralQueries.structuralDependencies_length_le_231
      functions lock stack firstRound
  have sites := sourceSitesDigestTrace_length_le_48 functions tx selected
    lock stack firstRound validKey ecdsa
  have final := finalCheckedDigestTrace_length_le_20 functions tx selected
    lock stack firstRound validKey ecdsa
  simp only [candidateDependencies, List.length_append]
  omega

/-- Agreement on one candidate's eager dependency inventory preserves its
entire optional result. This is source-model causality with all external
predicates and the lock held fixed. -/
theorem candidate_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (agree : ∀ q ∈ candidateDependencies functions tx selected lock stack
      firstRound validKey ecdsa,
      answer functions' q = answer functions q) :
    DynamicCheckedCertificate.candidate
      (JointSourceChecks.hashes functions') lock stack validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) firstRound =
    DynamicCheckedCertificate.candidate
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) firstRound := by
  have structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock stack
        firstRound, answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [candidateDependencies, mem])
  have siteAgree : ∀ q ∈ sourceSitesDigestTrace functions tx selected lock
      stack firstRound validKey ecdsa,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [candidateDependencies, mem])
  have finalAgree : ∀ q ∈ finalCheckedDigestTrace functions tx selected lock
      stack firstRound validKey ecdsa,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [candidateDependencies, mem])
  have fullRunEq :=
    CertificateStructuralQueries.structural_runs_congr functions functions'
      lock stack firstRound structuralAgree
      (DynamicCheckedCertificate.program lock)
      (by simp [CertificateStructuralQueries.sitePrograms])
  have sitesEq := sourceSites_congr functions functions' tx selected lock
    stack firstRound validKey ecdsa structuralAgree siteAgree
  have finalEq := finalChecked_congr functions functions' tx selected lock
    stack firstRound validKey ecdsa structuralAgree finalAgree
  unfold DynamicCheckedCertificate.candidate
  rw [fullRunEq, sitesEq, finalEq]

end QSB.CertificateCandidateCausality
