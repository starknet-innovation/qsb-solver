import QSB.ByteBonusBetween

/-!
An invariant for signed selections once their dummy-signature `OP_ROLL`s have
been shown to address the generated nonempty dummy pool. The remaining
obligation is to derive those pool-address premises from every accepted byte
and Core execution; this module does not assume a canonical index order.
-/
namespace QSB.PoolRollInvariant
open ByteMachine

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- A roll targeting the middle list selects that list's element and leaves
the prefix and arbitrary tail untouched. -/
theorem roll_from_middle {α : Type*} (front pool tail : List α)
    (j : Nat) (hj : j < pool.length) :
    KeyRolls.rollAt (front.length + j) (front ++ pool ++ tail) =
      some (pool[j] :: front ++ pool.eraseIdx j ++ tail) := by
  have get : (front ++ pool ++ tail)[front.length + j]? =
      some pool[j] := by
    have bound : front.length + j < (front ++ pool).length := by
      simp only [List.length_append]
      omega
    rw [List.getElem?_append_left bound]
    rw [List.getElem?_append_right (by omega)]
    simp [hj]
  have erased : (front ++ pool ++ tail).eraseIdx (front.length + j) =
      front ++ pool.eraseIdx j ++ tail := by
    have bound : front.length + j < (front ++ pool).length := by
      simp only [List.length_append]
      omega
    rw [List.eraseIdx_append_of_lt_length bound]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp
  unfold KeyRolls.rollAt
  rw [get, erased]
  rfl

/-- Selecting any pool element keeps the gathered signatures, nonce, and
zero dummy in order and removes exactly that pool element. -/
theorem roll_at_pool (front pool tail : List Bytes) (nonce : Bytes)
    (j : Nat) (hj : j < pool.length) :
    KeyRolls.rollAt (front.length + 2 + j)
      (front ++ [nonce, []] ++ pool ++ tail) =
      some (pool[j] :: front ++ [nonce, []] ++ pool.eraseIdx j ++ tail) := by
  simpa [List.append_assoc, List.length_append, Nat.add_assoc]
    using roll_from_middle (front ++ [nonce, []]) pool tail j hj

/-- Abstract the consecutive pool-only signature rolls, retaining the
attacker-independent order of the unselected dummy cells. -/
def drawMany : List Nat → List Bytes → List Bytes →
    Option (List Bytes × List Bytes)
  | [], gathered, pool => some (gathered, pool)
  | j :: rest, gathered, pool => do
      let chosen ← pool[j]?
      drawMany rest (chosen :: gathered) (pool.eraseIdx j)

def poolRollDepths : Nat → List Nat → List Nat
  | _, [] => []
  | gatheredLength, j :: rest =>
      (gatheredLength + 2 + j) :: poolRollDepths (gatheredLength + 1) rest

/-- The abstract pool draws have the same stack effect as the corresponding
ordinary `OP_ROLL` positions. This is a generic list theorem, so the
per-selection hash checks and exact generated index arithmetic are separate. -/
theorem drawMany_matches_rollMany (indices : List Nat)
    (gathered pool selected remaining tail : List Bytes) (nonce : Bytes)
    (draws : drawMany indices gathered pool = some (selected, remaining)) :
    KeyRolls.rollMany (poolRollDepths gathered.length indices)
      (gathered ++ [nonce, []] ++ pool ++ tail) =
      some (selected ++ [nonce, []] ++ remaining ++ tail) := by
  induction indices generalizing gathered pool with
  | nil =>
      simp [drawMany] at draws
      rcases draws with ⟨rfl, rfl⟩
      rfl
  | cons j rest ih =>
      simp only [drawMany] at draws
      cases chosen : pool[j]? with
      | none => simp [chosen] at draws
      | some value =>
          simp only [chosen] at draws
          have hj : j < pool.length := (List.getElem?_eq_some_iff.mp chosen).1
          have roll := roll_at_pool gathered pool tail nonce j hj
          have chosenEq : pool[j] = value :=
            (List.getElem?_eq_some_iff.mp chosen).2
          rw [chosenEq] at roll
          simp only [poolRollDepths, KeyRolls.rollMany, roll]
          exact ih (value :: gathered) (pool.eraseIdx j) draws

theorem drawMany_preserves_nonempty_pool (indices : List Nat)
    (gathered pool selected remaining : List Bytes)
    (allNonempty : ∀ x ∈ pool, x ≠ [])
    (draws : drawMany indices gathered pool = some (selected, remaining)) :
    (∀ x ∈ remaining, x ≠ []) ∧
      selected.length = gathered.length + indices.length ∧
      remaining.length + indices.length = pool.length := by
  induction indices generalizing gathered pool with
  | nil =>
      simp [drawMany] at draws
      rcases draws with ⟨rfl, rfl⟩
      exact ⟨allNonempty, by simp, by simp⟩
  | cons j rest ih =>
      simp only [drawMany] at draws
      cases chosen : pool[j]? with
      | none => simp [chosen] at draws
      | some value =>
          simp only [chosen] at draws
          have hj : j < pool.length := (List.getElem?_eq_some_iff.mp chosen).1
          have nextNonempty : ∀ x ∈ pool.eraseIdx j, x ≠ [] := by
            intro x hx
            exact allNonempty x (List.mem_of_mem_eraseIdx hx)
          obtain ⟨remainingNonempty, selectedLength, remainingLength⟩ :=
            ih (value :: gathered) (pool.eraseIdx j) nextNonempty draws
          constructor
          · exact remainingNonempty
          constructor
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using selectedLength
          · rw [List.length_eraseIdx_of_lt hj] at remainingLength
            simp only [List.length_cons]
            omega

/-- Seven selections from an initially nonempty pool of at least nine bytes
leave two nonempty cells immediately below the gathered signatures, nonce,
and zero dummy. Selection order and selected signature contents are arbitrary. -/
theorem seven_pool_draws_leave_two_nonempty (indices : List Nat)
    (pool selected remaining : List Bytes)
    (nonce : Bytes) (tail : List Bytes)
    (seven : indices.length = 7) (enough : 9 ≤ pool.length)
    (allNonempty : ∀ x ∈ pool, x ≠ [])
    (draws : drawMany indices [] pool = some (selected, remaining)) :
    ∃ nine ten : Bytes,
      nine ≠ [] ∧ ten ≠ [] ∧
      (selected ++ [nonce, []] ++ remaining ++ tail)[9]? = some nine ∧
      (selected ++ [nonce, []] ++ remaining ++ tail)[10]? = some ten := by
  obtain ⟨remainingNonempty, selectedLength, remainingLength⟩ :=
    drawMany_preserves_nonempty_pool indices [] pool selected remaining
      allNonempty draws
  have selectedSeven : selected.length = 7 := by simpa [seven] using selectedLength
  have atLeastTwo : 2 ≤ remaining.length := by omega
  let nine := remaining[0]
  let ten := remaining[1]
  have h0 : 0 < remaining.length := by omega
  have h1 : 1 < remaining.length := by omega
  have nineNonempty : nine ≠ [] :=
    remainingNonempty nine (List.getElem_mem h0)
  have tenNonempty : ten ≠ [] :=
    remainingNonempty ten (List.getElem_mem h1)
  refine ⟨nine, ten, nineNonempty, tenNonempty, ?_, ?_⟩
  · simp [List.getElem?_append, selectedSeven, nine, h0]
  · simp [List.getElem?_append, selectedSeven, ten, h1]
    rfl

/-- The 150 literal dummy-signature pushes in the generated second round.
Their reverse order is the pool's stack order at the start of its signed
selection loop. -/
def finalDummyPushOps : List Op := ByteLayout.program.drop 597 |>.take 150

def finalDummyPushes : List Bytes :=
  finalDummyPushOps.filterMap FirstOvershoot.pushValue

def finalDummyPool : List Bytes := finalDummyPushes.reverse

theorem generated_dummy_ops_are_pushes :
    finalDummyPushOps = finalDummyPushes.map Op.push := by decide

theorem generated_dummy_pool_length : finalDummyPool.length = 150 := by decide

theorem generated_dummy_pool_nonempty :
    ∀ x ∈ finalDummyPool, x ≠ [] := by
  have checked : List.Forall (fun x => x ≠ []) finalDummyPool := by decide
  exact List.forall_iff_forall_mem.mp checked

theorem generated_dummy_pushes_small :
    ∀ x ∈ finalDummyPushes, x.length ≤ 520 := by
  have checked : List.Forall (fun x => x.length ≤ 520)
      finalDummyPushes := by decide
  exact List.forall_iff_forall_mem.mp checked

/-- These 150 literal pushes establish the entire nonempty dummy pool over
any earlier stack that satisfies the Script size and opcode budgets. -/
theorem generated_dummy_pool_pushes (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (capacity : 150 + stack.length ≤ 1000) (budget : cost ≤ 201) :
    run hashes finalDummyPushOps (State.mk stack outcomes cost) =
      some (State.mk (finalDummyPool ++ stack) outcomes cost) := by
  rw [generated_dummy_ops_are_pushes]
  have count : finalDummyPushes.length = 150 := by decide
  have enough : finalDummyPushes.length + stack.length ≤ 1000 := by
    simpa [count] using capacity
  simpa [finalDummyPool] using
    (ByteMachine.run_pushes hashes finalDummyPushes stack outcomes cost
      generated_dummy_pushes_small enough budget)

def finalNonce : Bytes :=
  match ByteLayout.program[748]? with
  | some (Op.push value) => value
  | _ => []

def finalRoundInitOps : List Op := ByteLayout.program.drop 597 |>.take 152

theorem generated_final_round_init_ops : finalRoundInitOps =
    (finalDummyPushes ++ [[], finalNonce]).map Op.push := by decide

theorem generated_final_nonce_nonempty : finalNonce ≠ [] := by decide

/-- The complete generated second-round initialization, from any earlier
stack, places its fixed nonce and empty dummy directly above the 150
nonempty signature bytes. -/
theorem generated_final_round_initial_stack (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (capacity : 152 + stack.length ≤ 1000) (budget : cost ≤ 201) :
    run hashes finalRoundInitOps (State.mk stack outcomes cost) =
      some (State.mk (finalNonce :: [] :: finalDummyPool ++ stack)
        outcomes cost) := by
  rw [generated_final_round_init_ops]
  have count : (finalDummyPushes ++ [[], finalNonce]).length = 152 := by
    decide
  have small : ∀ value ∈ finalDummyPushes ++ [[], finalNonce],
      value.length ≤ 520 := by
    have checked : List.Forall (fun value => value.length ≤ 520)
        (finalDummyPushes ++ [[], finalNonce]) := by decide
    exact List.forall_iff_forall_mem.mp checked
  have enough : (finalDummyPushes ++ [[], finalNonce]).length +
      stack.length ≤ 1000 := by simpa [count] using capacity
  simpa [finalDummyPool, List.reverse_append, List.append_assoc] using
    (ByteMachine.run_pushes hashes (finalDummyPushes ++ [[], finalNonce])
      stack outcomes cost small enough budget)

/-- Specialize the abstract seven-draw invariant to all 150 generated bytes.
Only the premise that the seven signed rolls actually draw from this pool
remains to be established for arbitrary accepted executions. -/
theorem generated_pool_seven_draws_sources_nonempty
    (indices : List Nat) (selected remaining tail : List Bytes)
    (nonce : Bytes) (seven : indices.length = 7)
    (draws : drawMany indices [] finalDummyPool =
      some (selected, remaining)) :
    ∃ nine ten : Bytes,
      nine ≠ [] ∧ ten ≠ [] ∧
      (selected ++ [nonce, []] ++ remaining ++ tail)[9]? = some nine ∧
      (selected ++ [nonce, []] ++ remaining ++ tail)[10]? = some ten := by
  exact seven_pool_draws_leave_two_nonempty indices finalDummyPool
    selected remaining nonce tail seven
    (by rw [generated_dummy_pool_length]; omega)
    generated_dummy_pool_nonempty draws

/-- The exact generated dummy pool plus a pool-addressed seven-selection
history supplies the two source premises of the arbitrary-stack bonus theorem.
No canonical index order or equality of selected signatures is assumed. -/
theorem accepted_bonus_bounds_after_pool_draws (hashes : Hashes)
    (indices : List Nat) (selected remaining tail : List Bytes)
    (nonce rawFirst rawLast : Bytes) (regionLast : List Bytes)
    (firstIndex lastIndex : Nat) (outcomes : List Bool) (cost : Nat)
    (postFirst beforeLast postLast final : State)
    (seven : indices.length = 7)
    (draws : drawMany indices [] finalDummyPool =
      some (selected, remaining))
    (decodedFirst : ByteIndex.parseScriptNum rawFirst =
      some (Int.ofNat firstIndex))
    (decodedLast : ByteIndex.parseScriptNum rawLast =
      some (Int.ofNat lastIndex))
    (firstRoll : run hashes [.roll]
      (State.mk (rawFirst ::
        (selected ++ [nonce, []] ++ remaining ++ tail)) outcomes cost) =
        some postFirst)
    (between : run hashes ByteBonusBetween.betweenOps postFirst =
      some beforeLast)
    (lastShape : beforeLast.stack = rawLast :: regionLast)
    (lastRoll : run hashes [.roll] beforeLast = some postLast)
    (suffix : run hashes (ByteLayout.program.drop 850)
      postLast = some final) :
    9 ≤ firstIndex ∧ 10 ≤ lastIndex := by
  obtain ⟨nine, ten, nineNonempty, tenNonempty, firstNine, firstTen⟩ :=
    generated_pool_seven_draws_sources_nonempty indices selected remaining
      tail nonce seven draws
  exact ByteBonusBetween.successful_two_bonus_index_bounds hashes
    rawFirst rawLast (selected ++ [nonce, []] ++ remaining ++ tail)
    regionLast firstIndex lastIndex outcomes cost postFirst beforeLast
    postLast final nine ten nineNonempty tenNonempty firstNine firstTen
    decodedFirst decodedLast firstRoll between lastShape lastRoll suffix

end QSB.PoolRollInvariant
