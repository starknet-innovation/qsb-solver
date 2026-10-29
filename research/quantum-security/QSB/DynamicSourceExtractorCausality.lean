import QSB.CertificateSearchCausality
import QSB.DynamicSourceGame

/-!
An eager H/R dependency inventory for the source-model extractor on one fixed
already-prepared attempt. It records both certificate searches and three
additional structural runs, including runs skipped by an early failure. The
inventory is analytic: its order does not reproduce every source call, and it
is not an effectful oracle machine or an actual-query budget.

The lock, transaction fields, selected input, initial stack, key validator,
and ECDSA predicate are fixed. Parsing and scriptSig execution happen before
this attempt is formed; their costs, the supplied functions' internals, lock
construction, and compiled Bitcoin Core are outside this theorem.
-/
namespace QSB.DynamicSourceExtractorCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

private def initialByte (attempt : DynamicSourceGame.Attempt)
    (firstRound : Bool) : State :=
  ⟨attempt.stack, CoreCheckedCertificate.outcomes firstRound, 0⟩

private def priorAndFirst (lock : DynamicCheckedCertificate.Lock) : List Op :=
  DynamicFullSerialized.priorOps lock.pin lock.nonce0
    lock.firstCommitment ++ [.checkmultisig]

private def pinTrace (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) : List Query :=
  ByteMachineQueries.runQueries functions
    ((DynamicCheckedCertificate.program lock).take 2)
    (initialByte attempt firstRound)

private def extractionTrace (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) : List Query :=
  ByteMachineQueries.runQueries functions (priorAndFirst lock)
    (initialByte attempt firstRound)

private def finalPrefixTrace (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) : List Query :=
  ByteMachineQueries.runQueries functions
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    (initialByte attempt firstRound)

/-- The second search and three structural runs can be skipped at runtime.
They are listed eagerly once the first search selects a Boolean result. -/
def continuationDependencies (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt) : List Query :=
  match DynamicCheckedCertificate.search (JointSourceChecks.hashes functions)
      lock attempt.stack validKey
      (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa) with
  | none => []
  | some (firstRound, _) =>
      pinTrace functions lock attempt firstRound ++
      CertificateSearchCausality.searchDependencies functions attempt.tx
        attempt.selected lock attempt.stack validKey ecdsa ++
      extractionTrace functions lock attempt firstRound ++
      finalPrefixTrace functions lock attempt firstRound

/-- Eager source-model dependencies of `DynamicSourceGame.extractor` on one
fixed attempt. The repeated search is charged twice. -/
def extractorDependencies (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt) : List Query :=
  CertificateSearchCausality.searchDependencies functions attempt.tx
      attempt.selected lock attempt.stack validKey ecdsa ++
    continuationDependencies functions lock validKey ecdsa attempt

private theorem pinTrace_length_le_33 (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) :
    (pinTrace functions lock attempt firstRound).length ≤ 33 := by
  unfold pinTrace
  exact (ByteMachineQueries.runQueries_length_le functions _ _).trans
    (CertificateStructuralQueries.prefix_budget_le_33 lock 2)

private theorem priorAndFirst_budget_le_33
    (lock : DynamicCheckedCertificate.Lock) :
    ((priorAndFirst lock).map ByteMachineQueries.opBudget).sum ≤ 33 := by
  have total := ByteMachineQueries.lock_budget lock
  change (((priorAndFirst lock) ++
      DynamicFinalInit.finalRoundProgram lock.nonce1
        lock.secondCommitment).map ByteMachineQueries.opBudget).sum = 33
    at total
  simp only [List.map_append, List.sum_append] at total
  omega

private theorem extractionTrace_length_le_33
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) :
    (extractionTrace functions lock attempt firstRound).length ≤ 33 := by
  unfold extractionTrace
  exact (ByteMachineQueries.runQueries_length_le functions _ _).trans
    (priorAndFirst_budget_le_33 lock)

private theorem finalPrefixTrace_length_le_33
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) :
    (finalPrefixTrace functions lock attempt firstRound).length ≤ 33 := by
  unfold finalPrefixTrace
  exact (ByteMachineQueries.runQueries_length_le functions _ _).trans
    (CertificateStructuralQueries.beforeFinal_budget_le_33 lock)

/-- At most 598 calls per certificate search plus 33 for each of the three
additional structural runs. External and earlier-stage calls are excluded. -/
theorem extractorDependencies_length_le_1295
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt) :
    (extractorDependencies functions lock validKey ecdsa attempt).length ≤
      1295 := by
  have searchBound := CertificateSearchCausality.searchDependencies_length_le_598
    functions attempt.tx attempt.selected lock attempt.stack validKey ecdsa
  have continuationBound :
      (continuationDependencies functions lock validKey ecdsa attempt).length
        ≤ 697 := by
    cases found : DynamicCheckedCertificate.search
        (JointSourceChecks.hashes functions) lock attempt.stack validKey
        (JointSourceChecks.checker functions attempt.tx attempt.selected
          ecdsa) with
    | none => simp [continuationDependencies, found]
    | some pair =>
        obtain ⟨firstRound, sourceFinal⟩ := pair
        have pin := pinTrace_length_le_33 functions lock attempt firstRound
        have extract := extractionTrace_length_le_33 functions lock attempt
          firstRound
        have final := finalPrefixTrace_length_le_33 functions lock attempt
          firstRound
        simp only [continuationDependencies, found,
          List.length_append]
        omega
  simp only [extractorDependencies, List.length_append]
  omega

private theorem pin_run_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool)
    (agree : ∀ q ∈ pinTrace functions lock attempt firstRound,
      answer functions' q = answer functions q) :
    CoreStructuralRun.run (JointSourceChecks.hashes functions')
      ((DynamicCheckedCertificate.program lock).take 2)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) =
    CoreStructuralRun.run (JointSourceChecks.hashes functions)
      ((DynamicCheckedCertificate.program lock).take 2)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) := by
  simpa [pinTrace, initialByte, DynamicCheckedCertificate.initial] using
    ByteMachineQueries.structural_run_congr functions functions'
      ((DynamicCheckedCertificate.program lock).take 2)
      (initialByte attempt firstRound) agree

private theorem extractTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool)
    (agree : ∀ q ∈ extractionTrace functions lock attempt firstRound,
      answer functions' q = answer functions q) :
    DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions')
      (DynamicFullSerialized.priorOps lock.pin lock.nonce0
        lock.firstCommitment)
      (initialByte attempt firstRound) =
    DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions)
      (DynamicFullSerialized.priorOps lock.pin lock.nonce0
        lock.firstCommitment)
      (initialByte attempt firstRound) := by
  have runEq := ByteMachineQueries.run_congr functions functions'
    (priorAndFirst lock) (initialByte attempt firstRound)
    (by simpa [extractionTrace] using agree)
  unfold DynamicWholeSource.extractTrace
  simpa only [priorAndFirst] using congrArg
    (fun outcome : Option State => outcome.bind fun afterFirst =>
      match afterFirst.stack with
      | [] => none
      | _ :: tail => FinalSignedChain.extractOrdered (List.finRange 7)
          (List.finRange 150) 0 tail) runEq

private theorem finalPrefix_run_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool)
    (agree : ∀ q ∈ finalPrefixTrace functions lock attempt firstRound,
      answer functions' q = answer functions q) :
    CoreStructuralRun.run (JointSourceChecks.hashes functions')
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) =
    CoreStructuralRun.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial attempt.stack firstRound) := by
  simpa [finalPrefixTrace, initialByte, DynamicCheckedCertificate.initial] using
    ByteMachineQueries.structural_run_congr functions functions'
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (initialByte attempt firstRound) agree

private theorem extractor_eq_explicit
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt) :
    DynamicSourceGame.extractor functions lock validKey ecdsa attempt =
      (do
        let found ← DynamicCheckedCertificate.search
          (JointSourceChecks.hashes functions) lock attempt.stack validKey
          (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa)
        let beforePin ← CoreStructuralRun.run
          (JointSourceChecks.hashes functions)
          ((DynamicCheckedCertificate.program lock).take 2)
          (DynamicCheckedCertificate.initial attempt.stack found.1)
        let w ← DynamicRoundWitness.extract
          (JointSourceChecks.hashes functions) lock attempt.stack validKey
          (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa)
        some (DynamicJointTransaction.reachedPinKey beforePin, w)) := by
  rfl

/-- For a fixed already-prepared attempt, agreement on the eager inventory
preserves the source extractor's optional pin key and final-round witness.
This is result causality of the Lean model, not an operational machine budget
or compiled-Core refinement. -/
theorem extractor_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt)
    (agree : ∀ q ∈ extractorDependencies functions lock validKey ecdsa
      attempt, answer functions' q = answer functions q) :
    DynamicSourceGame.extractor functions' lock validKey ecdsa attempt =
    DynamicSourceGame.extractor functions lock validKey ecdsa attempt := by
  have firstAgree : ∀ q ∈
      CertificateSearchCausality.searchDependencies functions attempt.tx
        attempt.selected lock attempt.stack validKey ecdsa,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [extractorDependencies, mem])
  have continuationAgree : ∀ q ∈ continuationDependencies functions lock
      validKey ecdsa attempt,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [extractorDependencies, mem])
  have searchEq := CertificateSearchCausality.search_congr
    functions functions' attempt.tx attempt.selected lock attempt.stack
      validKey ecdsa firstAgree
  rw [extractor_eq_explicit functions' lock validKey ecdsa attempt,
    extractor_eq_explicit functions lock validKey ecdsa attempt]
  rw [searchEq]
  cases found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock attempt.stack validKey
      (JointSourceChecks.checker functions attempt.tx attempt.selected
        ecdsa) with
  | none => simp
  | some pair =>
      obtain ⟨firstRound, sourceFinal⟩ := pair
      have pinAgree : ∀ q ∈ pinTrace functions lock attempt firstRound,
          answer functions' q = answer functions q := by
        intro q mem
        exact continuationAgree q (by
          simp [continuationDependencies, found, mem])
      have extractAgree : ∀ q ∈ extractionTrace functions lock attempt
          firstRound, answer functions' q = answer functions q := by
        intro q mem
        exact continuationAgree q (by
          simp [continuationDependencies, found, mem])
      have finalAgree : ∀ q ∈ finalPrefixTrace functions lock attempt
          firstRound, answer functions' q = answer functions q := by
        intro q mem
        exact continuationAgree q (by
          simp [continuationDependencies, found, mem])
      have pinEq := pin_run_congr functions functions' lock attempt
        firstRound pinAgree
      have extractEq := extractTrace_congr functions functions' lock attempt
        firstRound extractAgree
      have extractEq' :
          DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions')
              (DynamicFullSerialized.priorOps lock.pin lock.nonce0
                lock.firstCommitment)
              ⟨attempt.stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
            DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions)
              (DynamicFullSerialized.priorOps lock.pin lock.nonce0
                lock.firstCommitment)
              ⟨attempt.stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ :=
        by simpa [initialByte] using extractEq
      have finalEq := finalPrefix_run_congr functions functions' lock attempt
        firstRound finalAgree
      have roundEq :
          DynamicRoundWitness.extract (JointSourceChecks.hashes functions')
              lock attempt.stack validKey
              (JointSourceChecks.checker functions' attempt.tx
                attempt.selected ecdsa) =
            DynamicRoundWitness.extract (JointSourceChecks.hashes functions)
              lock attempt.stack validKey
              (JointSourceChecks.checker functions attempt.tx
                attempt.selected ecdsa) := by
        unfold DynamicRoundWitness.extract
        rw [searchEq]
        simp [found, extractEq', finalEq]
      simp [pinEq, roundEq]

end QSB.DynamicSourceExtractorCausality
