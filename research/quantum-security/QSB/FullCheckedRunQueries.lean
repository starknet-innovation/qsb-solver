import QSB.CheckedRunQueryTrace

/-!
One ordered H/R query trace for the source-shaped checked lock interpreter.
On successful executions, each reached opcode contributes its hash-opcode
calls or the explicit legacy digest calls made by its signature checker.
The trace follows the checked interpreter's computed next state and stops
when execution stops. At a failing step it can conservatively record calls
that an earlier guard prevented; its all-attempt bound is an overapproximation.
The list is computed from pure oracle functions, not an instrumented effectful
interpreter. The 81 bound is for this source-model dependency list; a whole-run
causality theorem and an operational query-budget refinement remain open.
The external key validator and ECDSA predicate are fixed pure functions; any
oracle work inside their implementations is outside this trace.
-/
namespace QSB.FullCheckedRunQueries
open ByteMachine
open CausalQueryAlgorithm (Query answer)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Explicit H/R queries at one checked opcode, in source order when the
step succeeds. A failing early guard can leave this list conservative. -/
def stepQueries (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (s : CoreCheckedStep.State) : List Query :=
  match op with
  | .checksigverify =>
      CheckedRunQueryTrace.checksigDigestTrace functions tx selected
        validKey script s
  | .checkmultisig =>
      CheckedRunQueryTrace.scanAtStackDigestTrace functions tx selected
        validKey ecdsa script s.stack
  | _ => ByteMachineQueries.stepQueries functions op s.stack.reverse

/-- The ordered explicit H/R calls along a successful checked execution.
The branch after each step is the actual `CoreCheckedStep.step` branch, so a
false first-round multisignature result is retained and execution continues.
A failed step can conservatively record its potential queries. -/
def runQueries (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) : List Op → CoreCheckedStep.State → List Query
  | [], _ => []
  | op :: rest, s =>
      let current := stepQueries functions tx selected validKey ecdsa
        script op s
      match CoreCheckedStep.step (JointSourceChecks.hashes functions)
          script validKey
          (JointSourceChecks.checker functions tx selected ecdsa) op s with
      | none => current
      | some (next, _) =>
          if next.stack.length > 1000 then current
          else current ++ runQueries functions tx selected validKey ecdsa
            script rest next

private theorem singleton_queries (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (s : CoreCheckedStep.State) :
    runQueries functions tx selected validKey ecdsa script [op] s =
      stepQueries functions tx selected validKey ecdsa script op s := by
  simp only [runQueries]
  cases CoreCheckedStep.step (JointSourceChecks.hashes functions) script
      validKey (JointSourceChecks.checker functions tx selected ecdsa)
      op s with
  | none => rfl
  | some pair =>
      obtain ⟨next, record⟩ := pair
      simp

/-- On a segment with no multisignature opcode, each reached step fits its
static hash-opcode plus single-checker allowance. -/
theorem stepQueries_length_le_no_multisig
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (op : Op) (s : CoreCheckedStep.State)
    (noMulti : op ≠ .checkmultisig) :
    (stepQueries functions tx selected validKey ecdsa script op s).length ≤
      ByteMachineQueries.opBudget op +
        LockSignatureQueryBudget.sigHAllowance op := by
  have ordinary := ByteMachineQueries.stepQueries_length_le functions op
    s.stack.reverse
  have signature := CheckedRunQueryTrace.checksigDigestTrace_length_le_two
    functions tx selected validKey script s
  cases op <;>
    simp_all [stepQueries, ByteMachineQueries.opBudget,
      LockSignatureQueryBudget.sigHAllowance]

/-- A segment without multisignature calls fits its pointwise allowance,
whether it succeeds or stops early. -/
theorem runQueries_length_le_no_multisig
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) :
    ∀ (ops : List Op) (s : CoreCheckedStep.State),
      (∀ op ∈ ops, op ≠ .checkmultisig) →
      (runQueries functions tx selected validKey ecdsa script ops s).length ≤
        (ops.map (fun op => ByteMachineQueries.opBudget op +
          LockSignatureQueryBudget.sigHAllowance op)).sum
  | [], s, _ => by simp [runQueries]
  | op :: rest, s, noMulti => by
      have head := stepQueries_length_le_no_multisig functions tx selected
        validKey ecdsa script op s (noMulti op (by simp))
      have tail := runQueries_length_le_no_multisig functions tx selected
        validKey ecdsa script rest
      simp only [runQueries, List.map_cons, List.sum_cons]
      cases hstep : CoreCheckedStep.step
          (JointSourceChecks.hashes functions) script validKey
          (JointSourceChecks.checker functions tx selected ecdsa) op s with
      | none => simp only; omega
      | some pair =>
          obtain ⟨next, record⟩ := pair
          by_cases large : next.stack.length > 1000
          · simp only [gt_iff_lt, large, if_true]; omega
          · have later := tail next (fun nextOp mem =>
              noMulti nextOp (by simp [mem]))
            simp only [gt_iff_lt, large, if_false, List.length_append]
            omega

/-- The generated push followed by one ten-key source scan contributes at
most 20 explicit digest H calls, including an unsuccessful Boolean scan. -/
theorem keyCheck_queries_le_20
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (s : CoreCheckedStep.State) :
    (runQueries functions tx selected validKey ecdsa script
      LockOpcodeBudget.keyCheck s).length ≤ 20 := by
  change (runQueries functions tx selected validKey ecdsa script
    [.push [0x0a], .checkmultisig] s).length ≤ 20
  simp only [runQueries]
  cases hpush : CoreCheckedStep.step (JointSourceChecks.hashes functions)
      script validKey (JointSourceChecks.checker functions tx selected ecdsa)
      (.push [0x0a]) s with
  | none => simp [stepQueries, ByteMachineQueries.stepQueries]
  | some pair =>
      obtain ⟨pushed, record⟩ := pair
      obtain ⟨shape, _⟩ := LockSignatureQueryBudget.checked_push_ten_shape
        (JointSourceChecks.hashes functions) script validKey
        (JointSourceChecks.checker functions tx selected ecdsa)
        s pushed record hpush
      subst pushed
      by_cases large : (s.stack ++ [[0x0a]]).length > 1000
      · have atCap : 1000 ≤ s.stack.length := by
          simp only [List.length_append, List.length_singleton] at large
          omega
        simp [atCap, stepQueries, ByteMachineQueries.stepQueries]
      · have ten := LockSignatureQueryBudget.parse_ten_after_push s.stack
        have bound := CheckedRunQueryTrace.scanAtStackDigestTrace_ten_le_20
          functions tx selected validKey ecdsa script
          (s.stack ++ [[0x0a]]) ten
        simp only [large, if_false, stepQueries,
          ByteMachineQueries.stepQueries, List.nil_append]
        split <;> simpa using bound

/-- A trace splits at exactly the same boundary as the checked interpreter. -/
theorem runQueries_append (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (before after : List Op)
    (s : CoreCheckedStep.State) :
    runQueries functions tx selected validKey ecdsa script
      (before ++ after) s =
      match CoreCheckedStep.run (JointSourceChecks.hashes functions)
          script validKey
          (JointSourceChecks.checker functions tx selected ecdsa)
          before s with
      | none => runQueries functions tx selected validKey ecdsa
          script before s
      | some (middle, _) =>
          runQueries functions tx selected validKey ecdsa script before s ++
            runQueries functions tx selected validKey ecdsa script after middle := by
  induction before generalizing s with
  | nil => simp [runQueries, CoreCheckedStep.run]
  | cons op rest ih =>
      simp only [List.cons_append, runQueries, CoreCheckedStep.run]
      cases hstep : CoreCheckedStep.step (JointSourceChecks.hashes functions)
          script validKey (JointSourceChecks.checker functions tx selected ecdsa)
          op s with
      | none => simp
      | some pair =>
          obtain ⟨next, record⟩ := pair
          by_cases large : next.stack.length > 1000
          · simp [large]
          · simp [large, ih next]
            cases hrest : CoreCheckedStep.run
                (JointSourceChecks.hashes functions) script validKey
                (JointSourceChecks.checker functions tx selected ecdsa)
                rest next with
            | none => simp
            | some pair =>
                obtain ⟨middle, first⟩ := pair
                simp

/-- Uniform segment bounds compose in execution order. -/
theorem runQueries_length_le_append
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (script : Bytes) (before after : List Op)
    (first second : Nat)
    (beforeBound : ∀ s : CoreCheckedStep.State,
      (runQueries functions tx selected validKey ecdsa script before s).length
        ≤ first)
    (afterBound : ∀ s : CoreCheckedStep.State,
      (runQueries functions tx selected validKey ecdsa script after s).length
        ≤ second)
    (s : CoreCheckedStep.State) :
    (runQueries functions tx selected validKey ecdsa script
      (before ++ after) s).length ≤ first + second := by
  rw [runQueries_append]
  cases hbefore : CoreCheckedStep.run (JointSourceChecks.hashes functions)
      script validKey (JointSourceChecks.checker functions tx selected ecdsa)
      before s with
  | none =>
      simp only
      have h := beforeBound s
      omega
  | some pair =>
      obtain ⟨middle, records⟩ := pair
      simp only [List.length_append]
      have h₁ := beforeBound s
      have h₂ := afterBound middle
      omega

/-- The interleaved trace has at most 81 H/R entries for every parameterized
lock. For a failed run this is a conservative dependency allowance. -/
theorem lock_queries_le_81
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (lock : DynamicCheckedCertificate.Lock)
    (s : CoreCheckedStep.State) :
    (runQueries functions tx selected validKey ecdsa
      (DynamicCheckedCertificate.wire lock)
      (DynamicCheckedCertificate.program lock) s).length ≤ 81 := by
  let script := DynamicCheckedCertificate.wire lock
  let budget := fun op => ByteMachineQueries.opBudget op +
    LockSignatureQueryBudget.sigHAllowance op
  let preOps := LockOpcodeBudget.priorPrefix lock
  let midOps := LockOpcodeBudget.finalMiddle lock
  let keyOps := LockOpcodeBudget.keyCheck
  have prefixBound (u : CoreCheckedStep.State) :
      (runQueries functions tx selected validKey ecdsa script preOps u).length ≤
        (preOps.map budget).sum :=
    runQueries_length_le_no_multisig functions tx selected validKey ecdsa
      script preOps u (LockOpcodeBudget.priorPrefix_no_multisig lock)
  have middleBound (u : CoreCheckedStep.State) :
      (runQueries functions tx selected validKey ecdsa script midOps u).length ≤
        (midOps.map budget).sum :=
    runQueries_length_le_no_multisig functions tx selected validKey ecdsa
      script midOps u (LockOpcodeBudget.finalMiddle_no_multisig lock)
  have keyBound (u : CoreCheckedStep.State) :
      (runQueries functions tx selected validKey ecdsa script keyOps u).length ≤
        (keyOps.map budget).sum := by
    have h := keyCheck_queries_le_20 functions tx selected validKey
      ecdsa script u
    simpa [keyOps, budget, LockOpcodeBudget.keyCheck,
      ByteMachineQueries.opBudget,
      LockSignatureQueryBudget.sigHAllowance] using h
  have secondPartBound (u : CoreCheckedStep.State) :
      (runQueries functions tx selected validKey ecdsa script
        (midOps ++ keyOps) u).length ≤
        (midOps.map budget).sum + (keyOps.map budget).sum :=
    runQueries_length_le_append functions tx selected validKey ecdsa
      script midOps keyOps _ _ middleBound keyBound u
  have firstPartBound (u : CoreCheckedStep.State) :
      (runQueries functions tx selected validKey ecdsa script
        (keyOps ++ (midOps ++ keyOps)) u).length ≤
        (keyOps.map budget).sum +
          ((midOps.map budget).sum + (keyOps.map budget).sum) :=
    runQueries_length_le_append functions tx selected validKey ecdsa
      script keyOps (midOps ++ keyOps) _ _ keyBound secondPartBound u
  have whole := runQueries_length_le_append functions tx selected
    validKey ecdsa script preOps (keyOps ++ (midOps ++ keyOps)) _ _
    prefixBound firstPartBound s
  have allowance := LockSignatureQueryBudget.lock_total_allowance lock
  rw [LockOpcodeBudget.program_split] at allowance
  simp only [List.map_append, List.sum_append] at allowance
  change (runQueries functions tx selected validKey ecdsa script
      (preOps ++ (keyOps ++ (midOps ++ keyOps))) s).length ≤ 81
  have allowance' :
      (preOps.map budget).sum +
        ((keyOps.map budget).sum +
          ((midOps.map budget).sum + (keyOps.map budget).sum)) = 81 := by
    simpa [preOps, midOps, keyOps, budget, Nat.add_assoc] using allowance
  exact le_trans whole (le_of_eq allowance')

/-- The successful checked run has a bounded ordered source-model dependency
list, with all reached signature results computed by the source model. This
is not yet a causal or effectful oracle-algorithm theorem. -/
theorem checked_run_queries_le_81
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (lock : DynamicCheckedCertificate.Lock)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (_success : CoreCheckedStep.run (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.wire lock) validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records)) :
    (runQueries functions tx selected validKey ecdsa
      (DynamicCheckedCertificate.wire lock)
      (DynamicCheckedCertificate.program lock) initial).length ≤ 81 :=
  lock_queries_le_81 functions tx selected validKey ecdsa lock initial

end QSB.FullCheckedRunQueries
