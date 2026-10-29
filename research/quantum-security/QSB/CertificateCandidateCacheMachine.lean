import QSB.CertificateCandidateCausality
import QSB.CertificateStructuralPrefixCausality

/-!
Prefix causality and a classical response-cache machine for one fixed
source-model certificate candidate. The inventory lists seven structural
runs before source signature digest checks, and can include checks that the
candidate short-circuits. Its order is a causal evaluation order for this
machine, not the candidate's source execution order. Lock construction,
transaction and initial-stack generation, calls hidden in the fixed key
validator or ECDSA predicate, scriptSig, compiled Core, and coherent quantum
queries remain outside this local bound.
-/
namespace QSB.CertificateCandidateCacheMachine
open ByteMachine
open CausalQueryAlgorithm (Query answer)
open FullCheckedRunPrefixCausality (PrefixCausal)

theorem append_prefix_at
    (functions functions' : JointSourceChecks.Functions)
    (headF headG tailF tailG : List Query)
    (headPrefix : ∀ k < headF.length,
      (∀ q ∈ headF.take k, answer functions' q = answer functions q) →
      headG.take (k + 1) = headF.take (k + 1))
    (headCongr : (∀ q ∈ headF,
      answer functions' q = answer functions q) → headG = headF)
    (tailPrefix : ∀ k < tailF.length,
      (∀ q ∈ tailF.take k, answer functions' q = answer functions q) →
      tailG.take (k + 1) = tailF.take (k + 1))
    (k : Nat) (available : k < (headF ++ tailF).length)
    (agree : ∀ q ∈ (headF ++ tailF).take k,
      answer functions' q = answer functions q) :
    (headG ++ tailG).take (k + 1) =
      (headF ++ tailF).take (k + 1) := by
  by_cases inHead : k < headF.length
  · have headAgree : ∀ q ∈ headF.take k,
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by
        rw [List.take_append_of_le_length (by omega : k ≤ headF.length)]
        exact mem)
    have sameHead := headPrefix k inHead headAgree
    have headLength : k + 1 ≤ headG.length := by
      have lengths := congrArg List.length sameHead
      simp only [List.length_take] at lengths
      omega
    rw [List.take_append_of_le_length headLength,
      List.take_append_of_le_length (by omega : k + 1 ≤ headF.length)]
    exact sameHead
  · have pastHead : headF.length ≤ k := by omega
    have headAgree : ∀ q ∈ headF,
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by
        rw [List.take_append, List.take_of_length_le pastHead]
        exact List.mem_append.mpr (Or.inl mem))
    have sameHead := headCongr headAgree
    have tailAvailable : k - headF.length < tailF.length := by
      simp only [List.length_append] at available
      omega
    have tailAgree : ∀ q ∈ tailF.take (k - headF.length),
        answer functions' q = answer functions q := by
      intro q mem
      exact agree q (by
        rw [List.take_append, List.take_of_length_le pastHead]
        exact List.mem_append.mpr (Or.inr mem))
    have sameTail := tailPrefix (k - headF.length) tailAvailable tailAgree
    rw [List.take_append, List.take_append, sameHead]
    rw [List.take_of_length_le (by omega : headF.length ≤ k + 1)]
    have index : k + 1 - headF.length =
        (k - headF.length) + 1 := by omega
    simp only [index, sameTail]

theorem sourceChecksigTrace_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool) (script sig key : Bytes) :
    PrefixCausal (fun functions =>
      CertificateSignatureQueries.sourceChecksigTrace functions tx selected
        validKey script sig key) := by
  intro functions functions' k available agree
  dsimp only at available agree ⊢
  by_cases der : DERSyntax.verifyAllEncoding sig = true
  · have h := FullCheckedRunPrefixCausality.pairDigestTrace_prefix tx
      selected validKey sig key
      (CoreFindAndDelete.run 880 script
        (CorePushSerialize.pushPattern sig))
      functions functions' k
      (by simpa [CertificateSignatureQueries.sourceChecksigTrace,
        der] using available)
      (by
        intro q mem
        exact agree q (by simpa
          [CertificateSignatureQueries.sourceChecksigTrace, der] using mem))
    simpa [CertificateSignatureQueries.sourceChecksigTrace,
      der] using h
  · simp [CertificateSignatureQueries.sourceChecksigTrace,
      der] at available

theorem finalTenDigestTrace_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (top : List Bytes) :
    PrefixCausal (fun functions =>
      CertificateSignatureQueries.finalTenDigestTrace functions tx selected
        validKey ecdsa script top) := by
  intro functions functions' k available agree
  dsimp only at available agree ⊢
  by_cases gate : top[0]? = some [0x0a] ∧ top[11]? = some [0x0a] ∧
      23 ≤ top.length
  · have h := FullCheckedRunPrefixCausality.scanDigestTrace_prefix tx
      selected validKey ecdsa DERSyntax.verifyAllEncoding
      (CoreMultisigEval.deletedScript script top)
      (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10)
      functions functions' k
      (by simpa [CertificateSignatureQueries.finalTenDigestTrace,
        gate] using available)
      (by
        intro q mem
        exact agree q (by simpa
          [CertificateSignatureQueries.finalTenDigestTrace, gate] using mem))
    simpa [CertificateSignatureQueries.finalTenDigestTrace,
      gate] using h
  · simp [CertificateSignatureQueries.finalTenDigestTrace,
      gate] at available

def sigTraceAt (functions : JointSourceChecks.Functions)
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

def firstScanTrace (functions : JointSourceChecks.Functions)
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

theorem sourceSites_replica
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    CertificateCandidateCausality.sourceSitesDigestTrace functions tx
      selected lock stack firstRound validKey ecdsa =
    sigTraceAt functions tx selected lock stack firstRound validKey 2 ++
    sigTraceAt functions tx selected lock stack firstRound validKey 5 ++
    sigTraceAt functions tx selected lock stack firstRound validKey 423 ++
    sigTraceAt functions tx selected lock stack firstRound validKey 856 ++
    firstScanTrace functions tx selected lock stack firstRound validKey
      ecdsa := by
  rfl

/-- Descriptor order for the four direct signature checks and first scan. -/
inductive SourceSite where
  | checksig : Nat → SourceSite
  | firstScan : SourceSite
  deriving DecidableEq

def sourceSiteOrder : List SourceSite :=
  [.checksig 2, .checksig 5, .checksig 423, .checksig 856, .firstScan]

def sourceSiteTrace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) : SourceSite → List Query
  | .checksig n =>
      sigTraceAt functions tx selected lock stack firstRound validKey n
  | .firstScan =>
      firstScanTrace functions tx selected lock stack firstRound
        validKey ecdsa

theorem sourceSites_eq_flatMap
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    CertificateCandidateCausality.sourceSitesDigestTrace functions tx
      selected lock stack firstRound validKey ecdsa =
    sourceSiteOrder.flatMap (sourceSiteTrace functions tx selected lock
      stack firstRound validKey ecdsa) := by
  rw [sourceSites_replica]
  simp [sourceSiteOrder, sourceSiteTrace]

/-- A fixed reached structural prefix makes the source CHECKSIG query list
prefix-causal in its own digest answers. -/
theorem sigTraceAt_prefix_of_runEq
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool) (n : Nat)
    (runEq : CoreStructuralRun.run
        (JointSourceChecks.hashes functions')
        ((DynamicCheckedCertificate.program lock).take n)
        (DynamicCheckedCertificate.initial stack firstRound) =
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take n)
        (DynamicCheckedCertificate.initial stack firstRound)) :
    ∀ k, k < (sigTraceAt functions tx selected lock stack firstRound
        validKey n).length →
      (∀ q ∈ (sigTraceAt functions tx selected lock stack firstRound
        validKey n).take k,
        answer functions' q = answer functions q) →
      (sigTraceAt functions' tx selected lock stack firstRound
        validKey n).take (k + 1) =
      (sigTraceAt functions tx selected lock stack firstRound
        validKey n).take (k + 1) := by
  intro k available agree
  unfold sigTraceAt at available agree ⊢
  rw [runEq]
  cases reached : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take n)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => simp [reached] at available
  | some state =>
      exact sourceChecksigTrace_prefix tx selected validKey
        (DynamicCheckedCertificate.wire lock)
        (state.stack.reverse[1]?.getD [])
        (state.stack.reverse[0]?.getD [])
        functions functions' k (by simpa [reached] using available)
        (by
          intro q mem
          exact agree q (by simpa [reached] using mem))

theorem sigTraceAt_congr_of_runEq
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool) (n : Nat)
    (runEq : CoreStructuralRun.run
        (JointSourceChecks.hashes functions')
        ((DynamicCheckedCertificate.program lock).take n)
        (DynamicCheckedCertificate.initial stack firstRound) =
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take n)
        (DynamicCheckedCertificate.initial stack firstRound))
    (agree : ∀ q ∈ sigTraceAt functions tx selected lock stack
      firstRound validKey n, answer functions' q = answer functions q) :
    sigTraceAt functions' tx selected lock stack firstRound validKey n =
      sigTraceAt functions tx selected lock stack firstRound validKey n := by
  unfold sigTraceAt at agree ⊢
  rw [runEq]
  cases reached : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take n)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => rfl
  | some state =>
      exact CertificateSignatureQueries.sourceChecksigTrace_congr
        functions functions' tx selected validKey
        (DynamicCheckedCertificate.wire lock)
        (state.stack.reverse[1]?.getD [])
        (state.stack.reverse[0]?.getD [])
        (by intro q mem; exact agree q (by simpa [reached] using mem))

/-- The first multisignature's reached structural prefix fixes its scan
stack; earlier digest answers then select each next scan query. -/
theorem firstScanTrace_prefix_of_runEq
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (runEq : CoreStructuralRun.run
        (JointSourceChecks.hashes functions')
        ((DynamicCheckedCertificate.program lock).take 446)
        (DynamicCheckedCertificate.initial stack firstRound) =
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 446)
        (DynamicCheckedCertificate.initial stack firstRound)) :
    ∀ k, k < (firstScanTrace functions tx selected lock stack
        firstRound validKey ecdsa).length →
      (∀ q ∈ (firstScanTrace functions tx selected lock stack
        firstRound validKey ecdsa).take k,
        answer functions' q = answer functions q) →
      (firstScanTrace functions' tx selected lock stack firstRound
        validKey ecdsa).take (k + 1) =
      (firstScanTrace functions tx selected lock stack firstRound
        validKey ecdsa).take (k + 1) := by
  intro k available agree
  unfold firstScanTrace at available agree ⊢
  rw [runEq]
  cases reached : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 446)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => simp [reached] at available
  | some state =>
      exact FullCheckedRunPrefixCausality.scanAtStackDigestTrace_prefix
        tx selected validKey ecdsa (DynamicCheckedCertificate.wire lock)
        state.stack functions functions' k
        (by simpa [reached] using available)
        (by
          intro q mem
          exact agree q (by simpa [reached] using mem))

theorem firstScanTrace_congr_of_runEq
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (runEq : CoreStructuralRun.run
        (JointSourceChecks.hashes functions')
        ((DynamicCheckedCertificate.program lock).take 446)
        (DynamicCheckedCertificate.initial stack firstRound) =
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 446)
        (DynamicCheckedCertificate.initial stack firstRound))
    (agree : ∀ q ∈ firstScanTrace functions tx selected lock stack
      firstRound validKey ecdsa,
      answer functions' q = answer functions q) :
    firstScanTrace functions' tx selected lock stack firstRound
      validKey ecdsa =
    firstScanTrace functions tx selected lock stack firstRound
      validKey ecdsa := by
  unfold firstScanTrace at agree ⊢
  rw [runEq]
  cases reached : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 446)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => rfl
  | some state =>
      exact FullCheckedRunCausality.scanAtStackDigestTrace_congr
        functions functions' tx selected validKey ecdsa
        (DynamicCheckedCertificate.wire lock) state.stack
        (by intro q mem; exact agree q (by simpa [reached] using mem))

def sourceSiteProgram (lock : DynamicCheckedCertificate.Lock) :
    SourceSite → List Op
  | .checksig n => (DynamicCheckedCertificate.program lock).take n
  | .firstScan => (DynamicCheckedCertificate.program lock).take 446

theorem sourceSiteProgram_mem
    (lock : DynamicCheckedCertificate.Lock) (site : SourceSite)
    (member : site ∈ sourceSiteOrder) :
    sourceSiteProgram lock site ∈
      CertificateStructuralQueries.sitePrograms lock := by
  cases site with
  | checksig n =>
      simp [sourceSiteOrder] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals simp [sourceSiteProgram,
        CertificateStructuralQueries.sitePrograms]
  | firstScan =>
      simp [sourceSiteProgram,
        CertificateStructuralQueries.sitePrograms]

theorem sourceSite_run_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (site : SourceSite)
    (member : site ∈ sourceSiteOrder)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q) :
    CoreStructuralRun.run (JointSourceChecks.hashes functions')
        (sourceSiteProgram lock site)
        (DynamicCheckedCertificate.initial stack firstRound) =
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (sourceSiteProgram lock site)
        (DynamicCheckedCertificate.initial stack firstRound) :=
  CertificateStructuralQueries.structural_runs_congr functions functions'
    lock stack firstRound structuralAgree (sourceSiteProgram lock site)
      (sourceSiteProgram_mem lock site member)

/-- Once the preceding structural inventory is agreed, one reached site
has prefix-causal digest dependencies. -/
theorem sourceSiteTrace_prefix_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (site : SourceSite) (member : site ∈ sourceSiteOrder)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q) :
    ∀ k, k < (sourceSiteTrace functions tx selected lock stack firstRound
        validKey ecdsa site).length →
      (∀ q ∈ (sourceSiteTrace functions tx selected lock stack firstRound
        validKey ecdsa site).take k,
        answer functions' q = answer functions q) →
      (sourceSiteTrace functions' tx selected lock stack firstRound
        validKey ecdsa site).take (k + 1) =
      (sourceSiteTrace functions tx selected lock stack firstRound
        validKey ecdsa site).take (k + 1) := by
  have runEq := sourceSite_run_congr functions functions' lock stack
    firstRound site member structuralAgree
  cases site with
  | checksig n =>
      exact sigTraceAt_prefix_of_runEq functions functions' tx selected
        lock stack firstRound validKey n runEq
  | firstScan =>
      exact firstScanTrace_prefix_of_runEq functions functions' tx selected
        lock stack firstRound validKey ecdsa runEq

theorem sourceSiteTrace_congr_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (site : SourceSite) (member : site ∈ sourceSiteOrder)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q)
    (agree : ∀ q ∈ sourceSiteTrace functions tx selected lock stack
      firstRound validKey ecdsa site,
      answer functions' q = answer functions q) :
    sourceSiteTrace functions' tx selected lock stack firstRound
      validKey ecdsa site =
    sourceSiteTrace functions tx selected lock stack firstRound
      validKey ecdsa site := by
  have runEq := sourceSite_run_congr functions functions' lock stack
    firstRound site member structuralAgree
  cases site with
  | checksig n =>
      exact sigTraceAt_congr_of_runEq functions functions' tx selected
        lock stack firstRound validKey n runEq agree
  | firstScan =>
      exact firstScanTrace_congr_of_runEq functions functions' tx selected
        lock stack firstRound validKey ecdsa runEq agree

/-- A list of reached signature-site traces stays prefix-causal after the
structural inventory fixes all of their input stacks. -/
theorem sourceSiteList_prefix_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q) :
    ∀ sites : List SourceSite,
      (∀ site ∈ sites, site ∈ sourceSiteOrder) →
      ∀ k, k < (sites.flatMap (sourceSiteTrace functions tx selected lock
          stack firstRound validKey ecdsa)).length →
        (∀ q ∈ (sites.flatMap (sourceSiteTrace functions tx selected lock
          stack firstRound validKey ecdsa)).take k,
          answer functions' q = answer functions q) →
        (sites.flatMap (sourceSiteTrace functions' tx selected lock stack
          firstRound validKey ecdsa)).take (k + 1) =
        (sites.flatMap (sourceSiteTrace functions tx selected lock stack
          firstRound validKey ecdsa)).take (k + 1)
  | [], _, k, available, _ => by simp at available
  | site :: rest, allMem, k, available, agree => by
      have member : site ∈ sourceSiteOrder :=
        allMem site (by simp)
      have restMem : ∀ x ∈ rest, x ∈ sourceSiteOrder := by
        intro x mem
        exact allMem x (by simp [mem])
      have headPrefix := sourceSiteTrace_prefix_of_structural_agree
        functions functions' tx selected lock stack firstRound validKey
        ecdsa site member structuralAgree
      have headCongr := sourceSiteTrace_congr_of_structural_agree
        functions functions' tx selected lock stack firstRound validKey
        ecdsa site member structuralAgree
      have tailPrefix := sourceSiteList_prefix_of_structural_agree
        functions functions' tx selected lock stack firstRound validKey
        ecdsa structuralAgree rest restMem
      have combined := append_prefix_at functions functions'
        (sourceSiteTrace functions tx selected lock stack firstRound
          validKey ecdsa site)
        (sourceSiteTrace functions' tx selected lock stack firstRound
          validKey ecdsa site)
        (rest.flatMap (sourceSiteTrace functions tx selected lock stack
          firstRound validKey ecdsa))
        (rest.flatMap (sourceSiteTrace functions' tx selected lock stack
          firstRound validKey ecdsa))
        headPrefix headCongr tailPrefix k
        (by simpa [List.flatMap_cons] using available)
        (by
          intro q mem
          exact agree q (by simpa [List.flatMap_cons] using mem))
      simpa [List.flatMap_cons] using combined

theorem sourceSiteList_congr_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q) :
    ∀ sites : List SourceSite,
      (∀ site ∈ sites, site ∈ sourceSiteOrder) →
      (∀ q ∈ sites.flatMap (sourceSiteTrace functions tx selected lock
        stack firstRound validKey ecdsa),
        answer functions' q = answer functions q) →
      sites.flatMap (sourceSiteTrace functions' tx selected lock stack
        firstRound validKey ecdsa) =
      sites.flatMap (sourceSiteTrace functions tx selected lock stack
        firstRound validKey ecdsa)
  | [], _, _ => by simp
  | site :: rest, allMem, agree => by
      have member : site ∈ sourceSiteOrder := allMem site (by simp)
      have restMem : ∀ x ∈ rest, x ∈ sourceSiteOrder := by
        intro x mem
        exact allMem x (by simp [mem])
      have headAgree : ∀ q ∈ sourceSiteTrace functions tx selected lock
          stack firstRound validKey ecdsa site,
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by simp [List.flatMap_cons, mem])
      have tailAgree : ∀ q ∈ rest.flatMap
          (sourceSiteTrace functions tx selected lock stack firstRound
            validKey ecdsa),
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by simp [List.flatMap_cons, mem])
      have headEq := sourceSiteTrace_congr_of_structural_agree
        functions functions' tx selected lock stack firstRound validKey
        ecdsa site member structuralAgree headAgree
      have tailEq := sourceSiteList_congr_of_structural_agree
        functions functions' tx selected lock stack firstRound validKey
        ecdsa structuralAgree rest restMem tailAgree
      simp [List.flatMap_cons, headEq, tailEq]

theorem sourceSitesDigestTrace_prefix_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q) :
    ∀ k, k < (CertificateCandidateCausality.sourceSitesDigestTrace
        functions tx selected lock stack firstRound validKey ecdsa).length →
      (∀ q ∈ (CertificateCandidateCausality.sourceSitesDigestTrace
        functions tx selected lock stack firstRound validKey ecdsa).take k,
        answer functions' q = answer functions q) →
      (CertificateCandidateCausality.sourceSitesDigestTrace functions'
        tx selected lock stack firstRound validKey ecdsa).take (k + 1) =
      (CertificateCandidateCausality.sourceSitesDigestTrace functions
        tx selected lock stack firstRound validKey ecdsa).take (k + 1) := by
  intro k available agree
  simp only [sourceSites_eq_flatMap] at available agree ⊢
  exact sourceSiteList_prefix_of_structural_agree functions functions'
    tx selected lock stack firstRound validKey ecdsa structuralAgree
    sourceSiteOrder (by intro site mem; exact mem) k available agree

theorem sourceSitesDigestTrace_congr_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q)
    (agree : ∀ q ∈ CertificateCandidateCausality.sourceSitesDigestTrace
      functions tx selected lock stack firstRound validKey ecdsa,
      answer functions' q = answer functions q) :
    CertificateCandidateCausality.sourceSitesDigestTrace functions'
      tx selected lock stack firstRound validKey ecdsa =
    CertificateCandidateCausality.sourceSitesDigestTrace functions
      tx selected lock stack firstRound validKey ecdsa := by
  simp only [sourceSites_eq_flatMap] at agree ⊢
  exact sourceSiteList_congr_of_structural_agree functions functions'
    tx selected lock stack firstRound validKey ecdsa structuralAgree
    sourceSiteOrder (by intro site mem; exact mem) agree

/-- Full structural-query agreement fixes each run's dependency list, not
only its terminal state. -/
theorem programs_query_trace_congr
    (functions functions' : JointSourceChecks.Functions) :
    ∀ (programs : List (List Op)) (s : State),
      (∀ q ∈ programs.flatMap
        (fun ops => ByteMachineQueries.runQueries functions ops s),
        answer functions' q = answer functions q) →
      programs.flatMap
          (fun ops => ByteMachineQueries.runQueries functions' ops s) =
        programs.flatMap
          (fun ops => ByteMachineQueries.runQueries functions ops s)
  | [], s, _ => by simp
  | ops :: rest, s, agree => by
      have headAgree : ∀ q ∈ ByteMachineQueries.runQueries functions ops s,
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by simp [List.flatMap_cons, mem])
      have tailAgree : ∀ q ∈ rest.flatMap
          (fun other => ByteMachineQueries.runQueries functions other s),
          answer functions' q = answer functions q := by
        intro q mem
        exact agree q (by simp [List.flatMap_cons, mem])
      have headEq := CertificateStructuralPrefixCausality.byteRunQueries_congr
        functions functions' ops s headAgree
      have tailEq := programs_query_trace_congr functions functions' rest
        s tailAgree
      simp [List.flatMap_cons, headEq, tailEq]

theorem structuralDependencies_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool)
    (agree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q) :
    CertificateStructuralQueries.structuralDependencies functions'
      lock stack firstRound =
    CertificateStructuralQueries.structuralDependencies functions
      lock stack firstRound := by
  simpa [CertificateStructuralQueries.structuralDependencies] using
    programs_query_trace_congr functions functions'
      (CertificateStructuralQueries.sitePrograms lock)
      (CertificateStructuralQueries.initialByte stack firstRound) agree

/-- Structural agreement fixes the final prefix stack, after which the
final ten-key digest list has its usual adaptive prefix property. -/
theorem finalCheckedDigestTrace_prefix_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q) :
    ∀ k, k < (CertificateCandidateCausality.finalCheckedDigestTrace
        functions tx selected lock stack firstRound validKey ecdsa).length →
      (∀ q ∈ (CertificateCandidateCausality.finalCheckedDigestTrace
        functions tx selected lock stack firstRound validKey ecdsa).take k,
        answer functions' q = answer functions q) →
      (CertificateCandidateCausality.finalCheckedDigestTrace functions'
        tx selected lock stack firstRound validKey ecdsa).take (k + 1) =
      (CertificateCandidateCausality.finalCheckedDigestTrace functions
        tx selected lock stack firstRound validKey ecdsa).take (k + 1) := by
  have runEq := CertificateStructuralQueries.structural_runs_congr
    functions functions' lock stack firstRound structuralAgree
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    (by simp [CertificateStructuralQueries.sitePrograms])
  intro k available agree
  unfold CertificateCandidateCausality.finalCheckedDigestTrace at available agree ⊢
  rw [runEq]
  cases reached : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => simp [reached] at available
  | some state =>
      exact finalTenDigestTrace_prefix tx selected validKey ecdsa
        (DynamicCheckedCertificate.wire lock) state.stack.reverse
        functions functions' k (by simpa [reached] using available)
        (by
          intro q mem
          exact agree q (by simpa [reached] using mem))

theorem finalCheckedDigestTrace_congr_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q)
    (agree : ∀ q ∈ CertificateCandidateCausality.finalCheckedDigestTrace
      functions tx selected lock stack firstRound validKey ecdsa,
      answer functions' q = answer functions q) :
    CertificateCandidateCausality.finalCheckedDigestTrace functions'
      tx selected lock stack firstRound validKey ecdsa =
    CertificateCandidateCausality.finalCheckedDigestTrace functions
      tx selected lock stack firstRound validKey ecdsa := by
  have runEq := CertificateStructuralQueries.structural_runs_congr
    functions functions' lock stack firstRound structuralAgree
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    (by simp [CertificateStructuralQueries.sitePrograms])
  unfold CertificateCandidateCausality.finalCheckedDigestTrace at agree ⊢
  rw [runEq]
  cases reached : CoreStructuralRun.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial stack firstRound) with
  | none => rfl
  | some state =>
      exact CertificateSignatureQueries.finalTenDigestTrace_congr
        functions functions' tx selected validKey ecdsa
        (DynamicCheckedCertificate.wire lock) state.stack.reverse
        (by intro q mem; exact agree q (by simpa [reached] using mem))

/-- With structural dependencies already answered, the remaining source-site
and final-check digest inventory is prefix-causal. -/
theorem digestTail_prefix_of_structural_agree
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (structuralAgree : ∀ q ∈
      CertificateStructuralQueries.structuralDependencies functions lock
        stack firstRound,
      answer functions' q = answer functions q)
    (k : Nat)
    (available : k <
      (CertificateCandidateCausality.sourceSitesDigestTrace functions tx
          selected lock stack firstRound validKey ecdsa ++
        CertificateCandidateCausality.finalCheckedDigestTrace functions tx
          selected lock stack firstRound validKey ecdsa).length)
    (agree : ∀ q ∈
      (CertificateCandidateCausality.sourceSitesDigestTrace functions tx
          selected lock stack firstRound validKey ecdsa ++
        CertificateCandidateCausality.finalCheckedDigestTrace functions tx
          selected lock stack firstRound validKey ecdsa).take k,
      answer functions' q = answer functions q) :
    (CertificateCandidateCausality.sourceSitesDigestTrace functions' tx
        selected lock stack firstRound validKey ecdsa ++
      CertificateCandidateCausality.finalCheckedDigestTrace functions' tx
        selected lock stack firstRound validKey ecdsa).take (k + 1) =
    (CertificateCandidateCausality.sourceSitesDigestTrace functions tx
        selected lock stack firstRound validKey ecdsa ++
      CertificateCandidateCausality.finalCheckedDigestTrace functions tx
        selected lock stack firstRound validKey ecdsa).take (k + 1) :=
  append_prefix_at functions functions' _ _ _ _
    (sourceSitesDigestTrace_prefix_of_structural_agree functions functions'
      tx selected lock stack firstRound validKey ecdsa structuralAgree)
    (sourceSitesDigestTrace_congr_of_structural_agree functions functions'
      tx selected lock stack firstRound validKey ecdsa structuralAgree)
    (finalCheckedDigestTrace_prefix_of_structural_agree functions functions'
      tx selected lock stack firstRound validKey ecdsa structuralAgree)
    k available agree

/-- Prefix causality of the full eager 299-entry candidate dependency
inventory. Its order is chosen for a cache machine, not the source candidate
execution order. -/
theorem candidateDependencies_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    PrefixCausal (fun functions =>
      CertificateCandidateCausality.candidateDependencies functions tx
        selected lock stack firstRound validKey ecdsa) := by
  let head : JointSourceChecks.Functions → List Query :=
    fun functions => CertificateStructuralQueries.structuralDependencies
      functions lock stack firstRound
  let tail : JointSourceChecks.Functions → List Query :=
    fun functions =>
      CertificateCandidateCausality.sourceSitesDigestTrace functions tx
        selected lock stack firstRound validKey ecdsa ++
      CertificateCandidateCausality.finalCheckedDigestTrace functions tx
        selected lock stack firstRound validKey ecdsa
  have headPrefix : PrefixCausal head := by
    simpa [head] using
      CertificateStructuralPrefixCausality.structuralDependencies_prefix
        lock stack firstRound
  have headCongr : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      head functions' = head functions := by
    intro functions functions' agree
    exact structuralDependencies_congr functions functions' lock stack
      firstRound agree
  have tailPrefix : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      ∀ k, k < (tail functions).length →
        (∀ q ∈ (tail functions).take k,
          answer functions' q = answer functions q) →
        (tail functions').take (k + 1) =
          (tail functions).take (k + 1) := by
    intro functions functions' headAgree
    exact digestTail_prefix_of_structural_agree functions functions'
      tx selected lock stack firstRound validKey ecdsa headAgree
  have combined := FullCheckedRunPrefixCausality.append_prefix head tail
    headPrefix headCongr tailPrefix
  simpa [head, tail, CertificateCandidateCausality.candidateDependencies,
    List.append_assoc] using combined

/-! ### A fixed-input classical candidate machine -/

structure FixedInput where
  lock : DynamicCheckedCertificate.Lock
  tx : SighashAllWire.TxFields
  selected : Nat
  stack : List Bytes
  firstRound : Bool
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool

def trace (p : FixedInput) (functions : JointSourceChecks.Functions) :
    List Query :=
  CertificateCandidateCausality.candidateDependencies functions p.tx
    p.selected p.lock p.stack p.firstRound p.validKey p.ecdsa

def candidateResult (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    Option CoreOpcodeStep.State :=
  DynamicCheckedCertificate.candidate (JointSourceChecks.hashes functions)
    p.lock p.stack p.validKey
    (JointSourceChecks.checker functions p.tx p.selected p.ecdsa)
    p.firstRound

/-- The cache machine computes its next request from stored replies and
width-correct fixed defaults, never by consulting the true oracle inside
its own `step`. -/
def machine (p : FixedInput) :
    CausalQueryAlgorithm.Machine CheckedRunCacheMachine.Cache
      (Option CoreOpcodeStep.State) where
  step := fun cache =>
    let completed := CheckedRunCacheMachine.completedFunctions cache
    match CheckedRunCacheMachine.firstMissing cache (trace p completed) with
    | some q => .inr q
    | none => .inl (candidateResult p completed)
  resume := fun cache reply =>
    match CheckedRunCacheMachine.firstMissing cache
        (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
    | some q => (q, reply) :: cache
    | none => cache

/-- The candidate's first uncached dependency under a sound completed cache
also occurs in the true candidate dependency list. -/
theorem firstMissing_true_mem
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (sound : CheckedRunCacheMachine.CacheSound functions cache)
    (q : Query)
    (missing : CheckedRunCacheMachine.firstMissing cache
      (trace p (CheckedRunCacheMachine.completedFunctions cache)) = some q) :
    q ∈ trace p functions := by
  obtain ⟨before, after, shape, covered, _⟩ :=
    CheckedRunCacheMachine.firstMissing_some_prefix cache _ q missing
  let completed := CheckedRunCacheMachine.completedFunctions cache
  have index : before.length < (trace p completed).length := by
    rw [shape]
    simp
  have takeBefore : (trace p completed).take before.length = before := by
    rw [shape]
    simp
  have agreeBefore : ∀ x ∈ (trace p completed).take before.length,
      answer functions x = answer completed x := by
    intro x member
    have inBefore : x ∈ before := by simpa [takeBefore] using member
    obtain ⟨reply, found⟩ := covered x inBefore
    exact (CheckedRunCacheMachine.complete_agrees_of_lookup functions
      cache sound x reply found).symm
  have samePrefix := candidateDependencies_prefix p.tx p.selected p.lock
    p.stack p.firstRound p.validKey p.ecdsa completed functions
    before.length index agreeBefore
  have prefixShape : (trace p completed).take (before.length + 1) =
      before ++ [q] := by
    rw [shape]
    simp [List.take_append]
  have qInPrefix : q ∈ (trace p functions).take (before.length + 1) := by
    change q ∈ (CertificateCandidateCausality.candidateDependencies
      functions p.tx p.selected p.lock p.stack p.firstRound p.validKey
      p.ecdsa).take (before.length + 1)
    rw [samePrefix]
    change q ∈ (trace p completed).take (before.length + 1)
    rw [prefixShape]
    simp
  exact (List.take_sublist _ _).subset qInPrefix

structure GoodCache (p : FixedInput)
    (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache) : Prop where
  sound : CheckedRunCacheMachine.CacheSound functions cache
  nodup : (cache.map Prod.fst).Nodup
  inTrace : ∀ entry ∈ cache, entry.1 ∈ trace p functions

theorem goodCache_nil (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    GoodCache p functions [] := by
  constructor <;> simp [CheckedRunCacheMachine.CacheSound]

theorem goodCache_cons
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (good : GoodCache p functions cache)
    (q : Query)
    (missing : CheckedRunCacheMachine.lookup cache q = none)
    (inTrace : q ∈ trace p functions) :
    GoodCache p functions ((q, answer functions q) :: cache) := by
  refine ⟨?_, ?_, ?_⟩
  · intro query reply member
    rcases List.mem_cons.mp member with same | later
    · cases same
      rfl
    · exact good.sound query reply later
  · have notMem :=
      (CheckedRunCacheMachine.lookup_none_iff_not_mem cache q).mp missing
    simp [notMem, good.nodup]
  · intro entry member
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact inTrace
    · exact good.inTrace entry later

theorem goodCache_length_le_trace
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (good : GoodCache p functions cache) :
    cache.length ≤ (trace p functions).length := by
  have subset : (cache.map Prod.fst).toFinset ⊆
      (trace p functions).toFinset := by
    intro q member
    have inKeys : q ∈ cache.map Prod.fst := by simpa using member
    obtain ⟨entry, inCache, same⟩ := List.mem_map.mp inKeys
    have inTrue := good.inTrace entry inCache
    simpa [same] using inTrue
  calc
    cache.length = (cache.map Prod.fst).length := by simp
    _ = (cache.map Prod.fst).toFinset.card :=
      (List.toFinset_card_of_nodup good.nodup).symm
    _ ≤ (trace p functions).toFinset.card := Finset.card_le_card subset
    _ ≤ (trace p functions).length := List.toFinset_card_le _

theorem trace_length_le_299 (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    (trace p functions).length ≤ 299 :=
  CertificateCandidateCausality.candidateDependencies_length_le_299
    functions p.tx p.selected p.lock p.stack p.firstRound p.validKey p.ecdsa

/-- Fully cached candidate dependencies determine the candidate's exact
optional result under the true oracle pair. -/
theorem covered_candidateResult_eq
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (sound : CheckedRunCacheMachine.CacheSound functions cache)
    (covered : CheckedRunCacheMachine.firstMissing cache
      (trace p (CheckedRunCacheMachine.completedFunctions cache)) = none) :
    candidateResult p (CheckedRunCacheMachine.completedFunctions cache) =
      candidateResult p functions := by
  have agree : ∀ q ∈ trace p (CheckedRunCacheMachine.completedFunctions cache),
      answer functions q =
        answer (CheckedRunCacheMachine.completedFunctions cache) q := by
    intro q member
    obtain ⟨reply, found⟩ :=
      CheckedRunCacheMachine.firstMissing_none_covered cache _ covered
        q member
    exact (CheckedRunCacheMachine.complete_agrees_of_lookup functions
      cache sound q reply found).symm
  exact (CertificateCandidateCausality.candidate_congr
    (CheckedRunCacheMachine.completedFunctions cache) functions p.tx
    p.selected p.lock p.stack p.firstRound p.validKey p.ecdsa agree).symm

/-- Any halted cache run computes the true candidate result. -/
theorem halted_result_correct (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : CheckedRunCacheMachine.Cache)
      (out : Option CoreOpcodeStep.State),
      CheckedRunCacheMachine.CacheSound functions cache →
      (CausalQueryAlgorithm.run (machine p) functions budget cache).1 =
        some out →
      out = candidateResult p functions
  | 0, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_candidateResult_eq p functions cache sound
            missing
          have outEq : candidateResult p
              (CheckedRunCacheMachine.completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          simp [CausalQueryAlgorithm.run, machine, missing] at halted
  | budget + 1, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_candidateResult_eq p functions cache sound
            missing
          have outEq : candidateResult p
              (CheckedRunCacheMachine.completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          have nextSound : CheckedRunCacheMachine.CacheSound functions
              ((q, answer functions q) :: cache) := by
            intro query reply member
            rcases List.mem_cons.mp member with same | later
            · cases same
              rfl
            · exact sound query reply later
          have tail :
              (CausalQueryAlgorithm.run (machine p) functions budget
                ((q, answer functions q) :: cache)).1 = some out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact halted_result_correct p functions budget _ out nextSound tail

/-- A good cache with enough remaining requests cannot exhaust its fuel:
every requested query is distinct and belongs to the true eager inventory. -/
theorem run_halts_of_enough
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : CheckedRunCacheMachine.Cache),
      GoodCache p functions cache →
      (trace p functions).length ≤ cache.length + budget →
      ∃ out, (CausalQueryAlgorithm.run (machine p) functions budget
        cache).1 = some out
  | 0, cache, good, enough => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          exact ⟨candidateResult p
            (CheckedRunCacheMachine.completedFunctions cache), by
            simp [CausalQueryAlgorithm.run, machine, missing]⟩
      | some q =>
          have uncached := CheckedRunCacheMachine.firstMissing_some_missing
            cache _ q missing
          have trueMember := firstMissing_true_mem p functions cache
            good.sound q missing
          have nextGood := goodCache_cons p functions cache good q
            uncached trueMember
          have bound := goodCache_length_le_trace p functions _ nextGood
          simp only [List.length_cons, Nat.add_zero] at enough bound
          omega
  | budget + 1, cache, good, enough => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          exact ⟨candidateResult p
            (CheckedRunCacheMachine.completedFunctions cache), by
            simp [CausalQueryAlgorithm.run, machine, missing]⟩
      | some q =>
          have uncached := CheckedRunCacheMachine.firstMissing_some_missing
            cache _ q missing
          have trueMember := firstMissing_true_mem p functions cache
            good.sound q missing
          have nextGood := goodCache_cons p functions cache good q
            uncached trueMember
          have enough' : (trace p functions).length ≤
              ((q, answer functions q) :: cache).length + budget := by
            simpa only [List.length_cons, Nat.add_succ, Nat.succ_add]
              using enough
          obtain ⟨out, tail⟩ :=
            run_halts_of_enough p functions budget _ nextGood enough'
          exact ⟨out, by
            simpa [CausalQueryAlgorithm.run, machine, missing] using tail⟩

/-- The fixed-input source-model certificate candidate can be computed by
one classical response-cache machine with at most 299 actual H/R requests.
The eager inventory may query checks the source candidate short-circuits and
reorders the final structural prefix before signature digests. -/
theorem run_299_correct
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run (machine p) functions 299 []).1 =
        some (candidateResult p functions) ∧
      (CausalQueryAlgorithm.run (machine p) functions 299 []).2.length ≤
        299 := by
  obtain ⟨out, halted⟩ := run_halts_of_enough p functions 299 []
    (goodCache_nil p functions) (by
      simpa using trace_length_le_299 p functions)
  have correct := halted_result_correct p functions 299 [] out
    (by simp [CheckedRunCacheMachine.CacheSound]) halted
  exact ⟨by simpa [correct] using halted,
    CausalQueryAlgorithm.run_length_le (machine p) functions 299 []⟩

end QSB.CertificateCandidateCacheMachine
