import QSB.CausalQueryAlgorithm
import QSB.LockOpcodeInventory
import QSB.CoreStructuralEquiv

/-!
The idealized H/R queries made by the byte-model hash opcodes. Each `HASH160`
is one H call followed by one R call on its output; each `SHA256` is one H
call. The trace is defined alongside the existing interpreter rather than by
changing it, and the interpreter's result is causal in that trace: two
function pairs agreeing on the recorded queries give the same run. For every
parameterized Config A lock the trace has at most 33 entries.

Signature outcomes are supplied to the byte model, so the SHA256d calls made
by the source-shaped signature checker at the four `CHECKSIGVERIFY` and two
ten-key `CHECKMULTISIG` sites are not in this trace. Compiled Core execution
and the scriptSig evaluator remain external.
-/
namespace QSB.ByteMachineQueries
open ByteMachine
open CausalQueryAlgorithm (Query answer)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Queries made by one opcode step from a given stack, when it executes. -/
def stepQueries (functions : JointSourceChecks.Functions) (op : Op)
    (stack : List Bytes) : List Query :=
  match op, stack with
  | .hash160, x :: _ => [.H x, .R (functions.H x)]
  | .sha256, x :: _ => [.H x]
  | _, _ => []

/-- The ordered query trace of a run, stopping where the run stops. -/
def runQueries (functions : JointSourceChecks.Functions) :
    List Op → State → List Query
  | [], _ => []
  | op :: rest, s =>
      match step (JointSourceChecks.hashes functions) op s with
      | none => stepQueries functions op s.stack
      | some next =>
          if next.stack.length > 1000 then stepQueries functions op s.stack
          else stepQueries functions op s.stack ++ runQueries functions rest next

/-- Maximum oracle calls of one opcode: two for `HASH160`, one for
`SHA256`, none otherwise. -/
def opBudget : Op → Nat
  | .hash160 => 2
  | .sha256 => 1
  | _ => 0

theorem stepQueries_length_le (functions : JointSourceChecks.Functions)
    (op : Op) (stack : List Bytes) :
    (stepQueries functions op stack).length ≤ opBudget op := by
  cases op <;> cases stack <;> simp [stepQueries, opBudget]

theorem runQueries_length_le (functions : JointSourceChecks.Functions) :
    ∀ (ops : List Op) (s : State),
      (runQueries functions ops s).length ≤ (ops.map opBudget).sum
  | [], s => by simp [runQueries]
  | op :: rest, s => by
      have head := stepQueries_length_le functions op s.stack
      simp only [runQueries, List.map_cons, List.sum_cons]
      cases hstep : step (JointSourceChecks.hashes functions) op s with
      | none =>
          dsimp only
          omega
      | some next =>
          by_cases large : 1000 < next.stack.length
          · simp only [gt_iff_lt, large, if_true]
            omega
          · have tail := runQueries_length_le functions rest next
            simp only [gt_iff_lt, large, if_false, List.length_append]
            omega

theorem answer_H (functions : JointSourceChecks.Functions) (x : Bytes) :
    answer functions (.H x) = functions.H x := rfl

theorem answer_R (functions : JointSourceChecks.Functions) (x : Bytes) :
    answer functions (.R x) = functions.R x := rfl

/-- A step that is not a hash opcode never consults the hash functions. -/
theorem step_no_hash (h h' : Hashes) (op : Op) (s : State)
    (not160 : op ≠ .hash160) (not256 : op ≠ .sha256) :
    step h' op s = step h op s := by
  rcases s with ⟨stack, outcomes, ops⟩
  cases op <;> first
    | exact absurd rfl not160
    | exact absurd rfl not256
    | (rcases stack with _ | ⟨x, _ | ⟨y, xs⟩⟩ <;> rfl)

theorem step_hash160 (h : Hashes) (x : Bytes) (xs : List Bytes)
    (outcomes : List Bool) (ops : Nat) :
    step h .hash160 ⟨x :: xs, outcomes, ops⟩ =
      if ops + 1 > 201 then none
      else some ⟨h.h160 x :: xs, outcomes, ops + 1⟩ := by
  unfold step
  simp

theorem step_sha256 (h : Hashes) (x : Bytes) (xs : List Bytes)
    (outcomes : List Bool) (ops : Nat) :
    step h .sha256 ⟨x :: xs, outcomes, ops⟩ =
      if ops + 1 > 201 then none
      else some ⟨h.h256 x :: xs, outcomes, ops + 1⟩ := by
  unfold step
  simp

theorem step_hash160_nil (h : Hashes) (outcomes : List Bool) (ops : Nat) :
    step h .hash160 ⟨[], outcomes, ops⟩ = none := by
  unfold step
  simp

theorem step_sha256_nil (h : Hashes) (outcomes : List Bool) (ops : Nat) :
    step h .sha256 ⟨[], outcomes, ops⟩ = none := by
  unfold step
  simp

/-- One step is determined by the oracle values at its recorded queries. -/
theorem step_congr (functions functions' : JointSourceChecks.Functions)
    (op : Op) (s : State)
    (agree : ∀ q ∈ stepQueries functions op s.stack,
      answer functions' q = answer functions q) :
    step (JointSourceChecks.hashes functions') op s =
      step (JointSourceChecks.hashes functions) op s := by
  by_cases h160 : op = .hash160
  · subst h160
    rcases s with ⟨_ | ⟨x, xs⟩, outcomes, ops⟩
    · rw [step_hash160_nil, step_hash160_nil]
    · have hx : functions'.H x = functions.H x :=
        agree (.H x) (by simp [stepQueries])
      have rx : functions'.R (functions.H x) = functions.R (functions.H x) :=
        agree (.R (functions.H x)) (by simp [stepQueries])
      rw [step_hash160, step_hash160]
      simp [JointSourceChecks.hashes, hx, rx]
  · by_cases h256 : op = .sha256
    · subst h256
      rcases s with ⟨_ | ⟨x, xs⟩, outcomes, ops⟩
      · rw [step_sha256_nil, step_sha256_nil]
      · have hx : functions'.H x = functions.H x :=
          agree (.H x) (by simp [stepQueries])
        rw [step_sha256, step_sha256]
        simp [JointSourceChecks.hashes, hx]
    · exact step_no_hash _ _ op s h160 h256

/-- The first step's queries are recorded in the run trace. -/
theorem stepQueries_mem_runQueries (functions : JointSourceChecks.Functions)
    (op : Op) (rest : List Op) (s : State) (q : Query)
    (mem : q ∈ stepQueries functions op s.stack) :
    q ∈ runQueries functions (op :: rest) s := by
  simp only [runQueries]
  cases step (JointSourceChecks.hashes functions) op s with
  | none => exact mem
  | some next =>
      by_cases large : 1000 < next.stack.length <;> simp [large, mem]

/-- A continuing run records the remaining steps' queries after the first. -/
theorem restQueries_mem_runQueries (functions : JointSourceChecks.Functions)
    (op : Op) (rest : List Op) (s next : State)
    (hstep : step (JointSourceChecks.hashes functions) op s = some next)
    (small : ¬ 1000 < next.stack.length) (q : Query)
    (mem : q ∈ runQueries functions rest next) :
    q ∈ runQueries functions (op :: rest) s := by
  simp [runQueries, hstep, small, mem]

/-- Causality of the byte interpreter: the run consults the oracle only at
its recorded queries. -/
theorem run_congr (functions functions' : JointSourceChecks.Functions) :
    ∀ (ops : List Op) (s : State),
      (∀ q ∈ runQueries functions ops s,
        answer functions' q = answer functions q) →
      run (JointSourceChecks.hashes functions') ops s =
        run (JointSourceChecks.hashes functions) ops s
  | [], s => by
      intro _
      rfl
  | op :: rest, s => by
      intro agree
      have sameStep := step_congr functions functions' op s
        (fun q mem => agree q (stepQueries_mem_runQueries functions op rest s q mem))
      simp only [run, sameStep]
      cases hstep : step (JointSourceChecks.hashes functions) op s with
      | none => rfl
      | some next =>
          by_cases large : 1000 < next.stack.length
          · simp [large]
          · have restAgree : ∀ q ∈ runQueries functions rest next,
                answer functions' q = answer functions q :=
              fun q mem => agree q
                (restQueries_mem_runQueries functions op rest s next hstep large q mem)
            simp [large, run_congr functions functions' rest next restAgree]

theorem runQueries_append (functions : JointSourceChecks.Functions)
    (before after : List Op) (s : State) :
    runQueries functions (before ++ after) s =
      match run (JointSourceChecks.hashes functions) before s with
      | none => runQueries functions before s
      | some mid => runQueries functions before s ++
          runQueries functions after mid := by
  induction before generalizing s with
  | nil => simp [runQueries, run]
  | cons op rest ih =>
      simp only [List.cons_append, runQueries, run]
      cases hstep : step (JointSourceChecks.hashes functions) op s with
      | none => simp
      | some next =>
          by_cases large : 1000 < next.stack.length
          · simp [large]
          · simp [large, ih next]
            cases run (JointSourceChecks.hashes functions) rest next <;> simp

/-! ### The parameterized Config A lock -/

theorem opBudget_skeleton (op : Op) :
    opBudget (LockOpcodeInventory.skeleton op) = opBudget op := by
  cases op <;> rfl

theorem literal_budget : (ByteLayout.program.map opBudget).sum = 33 := by
  decide

/-- The hash-opcode oracle budget of every parameterized lock is 33: 15 H
plus 15 R from `HASH160` and 3 H from `SHA256`. -/
theorem lock_budget (lock : DynamicCheckedCertificate.Lock) :
    ((DynamicCheckedCertificate.program lock).map opBudget).sum = 33 := by
  have same := congrArg
    (fun ops : List Op => (ops.map opBudget).sum)
    (LockOpcodeInventory.program_skeleton lock)
  simpa [List.map_map, opBudget_skeleton, literal_budget] using same

/-- Every parameterized lock makes at most 33 hash-opcode oracle calls from
any initial byte stack and supplied outcomes. -/
theorem lock_queries_le_33 (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock) (s : State) :
    (runQueries functions (DynamicCheckedCertificate.program lock) s).length
      ≤ 33 := by
  have := runQueries_length_le functions
    (DynamicCheckedCertificate.program lock) s
  rw [lock_budget] at this
  exact this

/-- The Core-shaped bottom-first run of any opcode list is equally causal in
the byte trace, through the checked structural equivalence. -/
theorem structural_run_congr (functions functions' : JointSourceChecks.Functions)
    (ops : List Op) (s : State)
    (agree : ∀ q ∈ runQueries functions ops s,
      answer functions' q = answer functions q) :
    CoreStructuralRun.run (JointSourceChecks.hashes functions') ops
        (CoreOpcodeStep.ofByte s) =
      CoreStructuralRun.run (JointSourceChecks.hashes functions) ops
        (CoreOpcodeStep.ofByte s) := by
  rw [CoreStructuralEquiv.run_eq_byte, CoreStructuralEquiv.run_eq_byte,
    run_congr functions functions' ops s agree]

end QSB.ByteMachineQueries
