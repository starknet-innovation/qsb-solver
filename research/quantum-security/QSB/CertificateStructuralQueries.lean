import QSB.ByteMachineQueries
import QSB.DynamicCoreStructural

/-!
An ordered, conservative dependency list for the seven structural runs that
can be evaluated by one `DynamicCheckedCertificate.candidate`: the full lock,
five signature-site prefixes, and the prefix before the final multisignature.
Every trace starts from the same candidate input and supplied outcomes. The
list may include sites skipped by `candidate` short-circuiting.

Only structural hash opcodes are counted. Source signature checker SHA256d
queries, key parsing, ECDSA work, and any wider extractor or transaction
processing are outside this trace. In particular, 231 is not a complete
extractor query budget.
-/
namespace QSB.CertificateStructuralQueries
open ByteMachine
open CausalQueryAlgorithm (Query answer)

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def initialByte (stack : List Bytes) (firstRound : Bool) : State :=
  ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩

/-- The seven potential structural runs in one certificate candidate, in
their dependency-list order. The certificate can short-circuit before some
are evaluated. -/
def sitePrograms (lock : DynamicCheckedCertificate.Lock) : List (List Op) :=
  [DynamicCheckedCertificate.program lock,
   (DynamicCheckedCertificate.program lock).take 2,
   (DynamicCheckedCertificate.program lock).take 5,
   (DynamicCheckedCertificate.program lock).take 423,
   (DynamicCheckedCertificate.program lock).take 446,
   (DynamicCheckedCertificate.program lock).take 856,
   DynamicCheckedCertificate.beforeFinalProgram lock]

def structuralDependencies (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) : List Query :=
  (sitePrograms lock).flatMap fun ops =>
    ByteMachineQueries.runQueries functions ops (initialByte stack firstRound)

/-- Every full-program prefix has at most the lock's 33 hash-opcode calls. -/
theorem prefix_budget_le_33 (lock : DynamicCheckedCertificate.Lock)
    (n : Nat) :
    (((DynamicCheckedCertificate.program lock).take n).map
      ByteMachineQueries.opBudget).sum ≤ 33 := by
  have split := congrArg
    (fun ops : List Op => (ops.map ByteMachineQueries.opBudget).sum)
    (List.take_append_drop n (DynamicCheckedCertificate.program lock))
  change (((DynamicCheckedCertificate.program lock).take n ++
      (DynamicCheckedCertificate.program lock).drop n).map
        ByteMachineQueries.opBudget).sum =
      ((DynamicCheckedCertificate.program lock).map
        ByteMachineQueries.opBudget).sum at split
  rw [List.map_append, List.sum_append,
    ByteMachineQueries.lock_budget] at split
  omega

/-- The final-check prefix ends just before the last CHECKMULTISIG. -/
theorem program_eq_beforeFinal_append
    (lock : DynamicCheckedCertificate.Lock) :
    DynamicCheckedCertificate.program lock =
      DynamicCheckedCertificate.beforeFinalProgram lock ++
        [.checkmultisig] := by
  simpa only [DynamicCheckedCertificate.program,
    DynamicCheckedCertificate.beforeFinalProgram] using
    DynamicCoreStructural.full_program_final_check_split
      (DynamicFullSerialized.priorOps lock.pin lock.nonce0
        lock.firstCommitment) lock.nonce1 lock.secondCommitment

theorem beforeFinal_budget_le_33
    (lock : DynamicCheckedCertificate.Lock) :
    ((DynamicCheckedCertificate.beforeFinalProgram lock).map
      ByteMachineQueries.opBudget).sum ≤ 33 := by
  have budget := ByteMachineQueries.lock_budget lock
  rw [program_eq_beforeFinal_append lock, List.map_append,
    List.sum_append] at budget
  omega

/-- Seven potential structural runs, each charged at most 33 hash calls.
Repeated prefix work is deliberately counted again. -/
theorem structuralDependencies_length_le_231
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) :
    (structuralDependencies functions lock stack firstRound).length ≤
      231 := by
  let s := initialByte stack firstRound
  have full := ByteMachineQueries.lock_queries_le_33 functions lock s
  have p2 := (ByteMachineQueries.runQueries_length_le functions
    ((DynamicCheckedCertificate.program lock).take 2) s).trans
      (prefix_budget_le_33 lock 2)
  have p5 := (ByteMachineQueries.runQueries_length_le functions
    ((DynamicCheckedCertificate.program lock).take 5) s).trans
      (prefix_budget_le_33 lock 5)
  have p423 := (ByteMachineQueries.runQueries_length_le functions
    ((DynamicCheckedCertificate.program lock).take 423) s).trans
      (prefix_budget_le_33 lock 423)
  have p446 := (ByteMachineQueries.runQueries_length_le functions
    ((DynamicCheckedCertificate.program lock).take 446) s).trans
      (prefix_budget_le_33 lock 446)
  have p856 := (ByteMachineQueries.runQueries_length_le functions
    ((DynamicCheckedCertificate.program lock).take 856) s).trans
      (prefix_budget_le_33 lock 856)
  have before := (ByteMachineQueries.runQueries_length_le functions
    (DynamicCheckedCertificate.beforeFinalProgram lock) s).trans
      (beforeFinal_budget_le_33 lock)
  dsimp only [s] at full p2 p5 p423 p446 p856 before
  simp only [structuralDependencies, sitePrograms, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_append]
  omega

/-- Agreement on the combined dependency list preserves every one of the
seven Core-shaped structural runs from the common initial state. -/
theorem structural_runs_congr
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool)
    (agree : ∀ q ∈ structuralDependencies functions lock stack firstRound,
      answer functions' q = answer functions q) :
    ∀ ops ∈ sitePrograms lock,
      CoreStructuralRun.run (JointSourceChecks.hashes functions') ops
          (DynamicCheckedCertificate.initial stack firstRound) =
        CoreStructuralRun.run (JointSourceChecks.hashes functions) ops
          (DynamicCheckedCertificate.initial stack firstRound) := by
  intro ops member
  have localAgree : ∀ q ∈ ByteMachineQueries.runQueries functions ops
      (initialByte stack firstRound),
      answer functions' q = answer functions q := by
    intro q queryMember
    apply agree q
    exact List.mem_flatMap.mpr ⟨ops, member, queryMember⟩
  simpa [DynamicCheckedCertificate.initial, initialByte] using
    ByteMachineQueries.structural_run_congr functions functions' ops
      (initialByte stack firstRound) localAgree

end QSB.CertificateStructuralQueries
