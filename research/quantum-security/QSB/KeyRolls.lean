import QSB.Layout
import QSB.Multisig

/-!
An arbitrary-stack invariant for the final CHECKMULTISIG setup. The lock
pushes its signature count 10, then performs ten constant-index OP_ROLLs to
collect public keys. Each index is strictly deeper than the pushed count's
current position, so successful rolls move that count to position 10 without
changing its value. The last lock instruction pushes the public-key count 10.

This does not identify which cells were rolled as keys or signatures, nor
prove the ECDSA checks; it only fixes the two count operands conditional on
reaching this suffix and its rolls succeeding. Unlike the canonical bonus
region result, the lemma allows an arbitrary underlying stack.
-/
namespace QSB.KeyRolls
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def rollAt {α : Type*} (n : Nat) (stack : List α) : Option (List α) := do
  let x ← stack[n]?
  pure (x :: stack.eraseIdx n)

/-- The generic list roll is exactly the symbolic machine's stack update for
a nonnegative numeric index while its opcode budget permits the step. -/
theorem rollAt_matches_symbolic_step (n : Nat)
    (stack : List StackMachine.Cell) (outcomes : List Bool) (ops : Nat)
    (budget : ops + 1 ≤ 201) :
    (StackMachine.step .roll
      (StackMachine.State.mk (.num n :: stack) outcomes ops)).map
      (fun s => s.stack) = rollAt n stack := by
  unfold StackMachine.step
  have nonnegative : ¬ ((n : Int) < 0) := by
    have hn := Int.natCast_nonneg n
    omega
  have withinBudget : ¬ (201 < ops + 1) := by omega
  simp only [if_neg withinBudget, if_neg nonnegative]
  cases hget : stack[n]? with
  | none => simp [rollAt, hget]
  | some x => simp [rollAt, hget]

def rollMany {α : Type*} : List Nat → List α → Option (List α)
  | [], stack => some stack
  | n :: ns, stack => do
      let next ← rollAt n stack
      rollMany ns next

theorem rollAt_preserves_shallower_cell {α : Type*}
    {stack next : List α} {n p : Nat} {marker : α}
    (shallower : p < n) (atP : stack[p]? = some marker)
    (run : rollAt n stack = some next) :
    next[p + 1]? = some marker := by
  unfold rollAt at run
  cases hget : stack[n]? with
  | none => simp [hget] at run
  | some x =>
      simp [hget] at run
      cases run
      simpa using (List.getElem?_eraseIdx_of_lt shallower).trans atP

def safeIndices : Nat → List Nat → Prop
  | _, [] => True
  | p, n :: ns => p < n ∧ safeIndices (p + 1) ns

theorem rollMany_preserves_marker {α : Type*}
    (indices : List Nat) (p : Nat) {stack final : List α} {marker : α}
    (safe : safeIndices p indices)
    (atP : stack[p]? = some marker)
    (run : rollMany indices stack = some final) :
    final[p + indices.length]? = some marker := by
  induction indices generalizing p stack final with
  | nil =>
      simp [rollMany] at run
      cases run
      simpa using atP
  | cons n ns ih =>
      obtain ⟨shallower, tailSafe⟩ := safe
      simp only [rollMany] at run
      cases hfirst : rollAt n stack with
      | none => simp [hfirst] at run
      | some next =>
          simp only [hfirst] at run
          have moved := rollAt_preserves_shallower_cell shallower atP hfirst
          have tail := ih (p + 1) tailSafe moved run
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

def keyIndices : List Nat := [1, 581, 582, 583, 584, 585, 586, 587, 588, 589]

theorem key_indices_safe : safeIndices 0 keyIndices := by
  simp [safeIndices, keyIndices]
theorem key_indices_length : keyIndices.length = 10 := by decide

/-- Independent of the underlying stack values and length, provided every
roll completes, the count pushed by the lock remains at offset 10. -/
theorem final_signature_count_fixed {α : Type*}
    {under final : List α} (count : α)
    (run : rollMany keyIndices (count :: under) = some final) :
    final[10]? = some count := by
  have h := rollMany_preserves_marker keyIndices 0 key_indices_safe
    (stack := count :: under) (marker := count) (by rfl) run
  simpa [key_indices_length] using h

/-- Once the last constant 10 is pushed, Core's two CHECKMULTISIG count
positions are both 10 for any underlying stack on which the key rolls finish. -/
theorem final_count_operands_ten
    {under final : List StackMachine.Cell}
    (run : rollMany keyIndices (.num 10 :: under) = some final) :
    ((.num 10 :: final)[0]? = some (.num 10)) ∧
    ((.num 10 :: final)[11]? = some (.num 10)) := by
  have oldCount := final_signature_count_fixed (StackMachine.Cell.num 10) run
  simp [oldCount]

/-- The final ten signature and key cells are computable from the public
execution stack. If the Core-style matching loop succeeds, every corresponding
pair verifies. This remains conditional on the supplied per-pair predicate
matching Core's byte parser, FindAndDelete and ECDSA checker. -/
theorem successful_final_pairs
    {under final : List StackMachine.Cell}
    (verify : StackMachine.Cell → StackMachine.Cell → Bool)
    (run : rollMany keyIndices (.num 10 :: under) = some final)
    (enough : 22 ≤ final.length)
    (success : Multisig.matchSigs verify
      ((final.drop 11).take 10) (final.take 10) = true) :
    ((.num 10 :: final)[0]? = some (.num 10)) ∧
    ((.num 10 :: final)[11]? = some (.num 10)) ∧
    List.Forall₂ (fun sig key => verify sig key = true)
      ((final.drop 11).take 10) (final.take 10) := by
  obtain ⟨nCount, mCount⟩ := final_count_operands_ten run
  have lengths : ((final.drop 11).take 10).length = (final.take 10).length := by
    simp [List.length_take, List.length_drop]
    omega
  exact ⟨nCount, mCount,
    (Multisig.equal_counts_success_iff_pairs verify lengths).mp success⟩

/-- The exact generated lock emits the count push, the ten key rolls with
these indices, then the final count push and CHECKMULTISIG. -/
theorem generated_final_suffix :
    Layout.program.drop 857 =
      [.push (.num 10),
       .push (.num 1), .roll,
       .push (.num 581), .roll,
       .push (.num 582), .roll,
       .push (.num 583), .roll,
       .push (.num 584), .roll,
       .push (.num 585), .roll,
       .push (.num 586), .roll,
       .push (.num 587), .roll,
       .push (.num 588), .roll,
       .push (.num 589), .roll,
       .push (.num 10), .checkmultisig] := by
  decide

end QSB.KeyRolls
