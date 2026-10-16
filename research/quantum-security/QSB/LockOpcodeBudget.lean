import QSB.LockOpcodeInventory
import QSB.FirstAcceptedOrigin
import QSB.ByteFinalCounts
import QSB.CoreStructuralEquiv

/-!
Every parameterized Config A lock spends exactly Core's 201-opcode budget in
any successful byte-model run: 181 counted opcodes plus the two ten-key
`CHECKMULTISIG` charges. Both key-count pushes lie in the static parts of the
program, so this holds for every pin, nonce, and commitment choice. One more
counted opcode after the lock is rejected by the modeled cap. These are
statements about the Lean interpreters; they corroborate the modeled count
at Core's boundary only together with the native acceptance experiments.
-/
namespace QSB.LockOpcodeBudget
open ByteMachine
open LockOpcodeInventory (counted)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- A successful step that is not a multisignature advances the counter by
exactly its ordinary cost. -/
theorem step_counted (hashes : Hashes) (op : Op) (s next : State)
    (notMulti : op ≠ .checkmultisig)
    (success : step hashes op s = some next) :
    next.ops = s.ops + counted op := by
  rcases s with ⟨stack, outcomes, ops⟩
  unfold step at success
  cases op
  all_goals first
    | exact absurd rfl notMulti
    | (rcases stack with _ | ⟨x, _ | ⟨y, xs⟩⟩ <;>
        rcases outcomes with _ | ⟨_ | _, rest⟩ <;>
        simp [counted, Option.bind_eq_some_iff, Option.ite_none_left_eq_some,
          Option.ite_none_right_eq_some] at success ⊢ <;> aesop)

theorem parse_ten : ByteIndex.parseScriptNum [0x0a] = some 10 := by decide

/-- A successful ten-key multisignature charges one plus ten. -/
theorem step_multisig_ten (hashes : Hashes) (xs : List Bytes)
    (outcomes : List Bool) (ops : Nat) (next : State)
    (success : step hashes .checkmultisig ⟨[0x0a] :: xs, outcomes, ops⟩ =
      some next) :
    next.ops = ops + 1 + 10 := by
  unfold step at success
  rcases outcomes with _ | ⟨b, rest⟩ <;>
    simp [parse_ten, Option.bind_eq_some_iff, Option.ite_none_left_eq_some,
      Option.ite_none_right_eq_some] at success
  aesop

theorem run_counted (hashes : Hashes) :
    ∀ (ops : List Op) (s next : State),
      (∀ op ∈ ops, op ≠ .checkmultisig) →
      run hashes ops s = some next →
      next.ops = s.ops + (ops.map counted).sum
  | [], s, next, _, success => by
      simp [run] at success
      subst success
      simp
  | op :: rest, s, next, noMulti, success => by
      obtain ⟨mid, stepped, _, continued⟩ :=
        FirstAcceptedOrigin.run_cons_success hashes op rest s next success
      have head := step_counted hashes op s mid (noMulti op (by simp)) stepped
      have tail := run_counted hashes rest mid next
        (fun o mem => noMulti o (by simp [mem])) continued
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The key-count push followed by the ten-key check. -/
def keyCheck : List Op := [.push [0x0a], .checkmultisig]

theorem run_keyCheck (hashes : Hashes) (s next : State)
    (success : run hashes keyCheck s = some next) :
    next.ops = s.ops + 11 := by
  obtain ⟨pushed, stepped, _, continued⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes _ _ s next success
  rcases s with ⟨stack, outcomes, ops⟩
  have shape := ByteFinalCounts.push_success_shape hashes _ _ _ _ _ stepped
  subst shape
  obtain ⟨checked, checkStep, _, finished⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes _ _ _ next continued
  have charged := step_multisig_ten hashes _ _ _ _ checkStep
  simp [run] at finished
  subst finished
  simp only [charged]

/-! ### Static position of both key-count pushes -/

def priorPrefix (lock : DynamicCheckedCertificate.Lock) : List Op :=
  DynamicFullSerialized.pinOps lock.pin ++
    DynamicFullSerialized.firstDataOps lock.nonce0 lock.firstCommitment ++
    DynamicFullSerialized.staticOps 308 137

def finalMiddle (lock : DynamicCheckedCertificate.Lock) : List Op :=
  DynamicFinalInit.dataOps lock.nonce1 lock.secondCommitment ++
    (ByteLayout.program.drop 749).take 129

theorem static_first_key_push :
    DynamicFullSerialized.staticOps 308 138 =
      DynamicFullSerialized.staticOps 308 137 ++ [.push [0x0a]] := by
  decide

theorem static_final_key_check :
    ByteLayout.program.drop 749 =
      (ByteLayout.program.drop 749).take 129 ++ keyCheck := by
  decide

/-- Every parameterized lock is a multisignature-free prefix, the first
ten-key check, a multisignature-free middle, and the final ten-key check. -/
theorem program_split (lock : DynamicCheckedCertificate.Lock) :
    DynamicCheckedCertificate.program lock =
      priorPrefix lock ++ keyCheck ++ finalMiddle lock ++ keyCheck := by
  simp only [DynamicCheckedCertificate.program, DynamicWholeSource.fullProgram,
    DynamicFullSerialized.priorOps, DynamicFinalInit.finalRoundProgram,
    priorPrefix, static_first_key_push]
  rw [static_final_key_check]
  simp [finalMiddle, keyCheck, List.append_assoc]

theorem pushes_no_multisig (values : List Bytes) :
    ∀ op ∈ values.map Op.push, op ≠ Op.checkmultisig := by
  intro op mem
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp mem
  simp

theorem static_no_multisig :
    (∀ op ∈ DynamicFullSerialized.staticOps 1 5, op ≠ Op.checkmultisig) ∧
    (∀ op ∈ DynamicFullSerialized.staticOps 156 151, op ≠ Op.checkmultisig) ∧
    (∀ op ∈ DynamicFullSerialized.staticOps 308 137, op ≠ Op.checkmultisig) ∧
    (∀ op ∈ (ByteLayout.program.drop 749).take 129, op ≠ Op.checkmultisig) := by
  decide

theorem pinOps_no_multisig (pin : Bytes) :
    ∀ op ∈ DynamicFullSerialized.pinOps pin, op ≠ Op.checkmultisig := by
  intro op mem
  simp only [DynamicFullSerialized.pinOps, List.cons_append, List.nil_append,
    List.mem_cons] at mem
  rcases mem with rfl | h
  · simp
  · exact static_no_multisig.1 op h

theorem firstDataOps_no_multisig (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) :
    ∀ op ∈ DynamicFullSerialized.firstDataOps nonce commitmentAt,
      op ≠ Op.checkmultisig := by
  intro op mem
  simp only [DynamicFullSerialized.firstDataOps, List.mem_append,
    List.mem_singleton] at mem
  rcases mem with (h | h) | rfl
  · exact pushes_no_multisig _ op h
  · exact static_no_multisig.2.1 op h
  · simp

theorem priorPrefix_no_multisig (lock : DynamicCheckedCertificate.Lock) :
    ∀ op ∈ priorPrefix lock, op ≠ Op.checkmultisig := by
  intro op mem
  simp only [priorPrefix, List.mem_append] at mem
  rcases mem with (h | h) | h
  · exact pinOps_no_multisig _ op h
  · exact firstDataOps_no_multisig _ _ op h
  · exact static_no_multisig.2.2.1 op h

theorem finalMiddle_no_multisig (lock : DynamicCheckedCertificate.Lock) :
    ∀ op ∈ finalMiddle lock, op ≠ Op.checkmultisig := by
  intro op mem
  simp only [finalMiddle, DynamicFinalInit.dataOps, List.mem_append] at mem
  rcases mem with h | h
  · exact pushes_no_multisig _ op h
  · exact static_no_multisig.2.2.2 op h

theorem pushes_counted_zero (values : List Bytes) :
    ((values.map Op.push).map counted).sum = 0 := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.sum_cons, counted, Nat.zero_add]
      exact ih

theorem static_counted :
    ((DynamicFullSerialized.staticOps 1 5).map counted).sum +
      ((DynamicFullSerialized.staticOps 156 151).map counted).sum +
      ((DynamicFullSerialized.staticOps 308 137).map counted).sum +
      (((ByteLayout.program.drop 749).take 129).map counted).sum = 179 := by
  decide

theorem split_counted (lock : DynamicCheckedCertificate.Lock) :
    ((priorPrefix lock).map counted).sum +
      ((finalMiddle lock).map counted).sum = 179 := by
  have := static_counted
  simp only [priorPrefix, finalMiddle, DynamicFullSerialized.pinOps,
    DynamicFullSerialized.firstDataOps, DynamicFinalInit.dataOps,
    List.map_append, List.sum_append, pushes_counted_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, counted]
  omega

/-- Any successful byte-model run of any parameterized lock advances the
opcode counter by exactly 201. -/
theorem lock_run_ops (hashes : Hashes) (lock : DynamicCheckedCertificate.Lock)
    (s final : State)
    (success : run hashes (DynamicCheckedCertificate.program lock) s =
      some final) :
    final.ops = s.ops + 201 := by
  rw [program_split, run_append, run_append, run_append] at success
  obtain ⟨afterMiddle, middleRun, finalRun⟩ :=
    Option.bind_eq_some_iff.mp success
  obtain ⟨afterFirst, firstRun, middleRun⟩ :=
    Option.bind_eq_some_iff.mp middleRun
  obtain ⟨afterPrefix, prefixRun, firstRun⟩ :=
    Option.bind_eq_some_iff.mp firstRun
  have prefixOps := run_counted hashes _ s afterPrefix
    (priorPrefix_no_multisig lock) prefixRun
  have firstOps := run_keyCheck hashes _ _ firstRun
  have middleOps := run_counted hashes _ afterFirst afterMiddle
    (finalMiddle_no_multisig lock) middleRun
  have finalOps := run_keyCheck hashes _ _ finalRun
  have total := split_counted lock
  omega

/-- From the certificate's zero counter, every accepted run ends exactly at
Core's cap. -/
theorem lock_run_ops_from_zero (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (outcomes : List Bool) (final : State)
    (success : run hashes (DynamicCheckedCertificate.program lock)
      ⟨stack, outcomes, 0⟩ = some final) :
    final.ops = 201 := by
  simpa using lock_run_ops hashes lock _ final success

theorem step_over_budget (hashes : Hashes) (op : Op) (s : State)
    (countedOp : counted op = 1) (full : s.ops ≥ 201) :
    step hashes op s = none := by
  rcases s with ⟨stack, outcomes, ops⟩
  have exceeded : ops + 1 > 201 := by
    simp only at full
    omega
  unfold step
  cases op <;> simp [counted] at countedOp <;> simp [exceeded]

/-- One further counted opcode after any parameterized lock is rejected by
the modeled 201-opcode cap, whatever its stack effect would have been. -/
theorem lock_rejects_extra_counted_op (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock) (op : Op)
    (countedOp : counted op = 1) (stack : List Bytes) (outcomes : List Bool) :
    run hashes (DynamicCheckedCertificate.program lock ++ [op])
      ⟨stack, outcomes, 0⟩ = none := by
  rw [run_append]
  cases lockRun : run hashes (DynamicCheckedCertificate.program lock)
      ⟨stack, outcomes, 0⟩ with
  | none => rfl
  | some final =>
      have full : final.ops ≥ 201 :=
        (lock_run_ops_from_zero hashes lock stack outcomes final lockRun).ge
      simp [run, step_over_budget hashes op final countedOp full]

/-- The Core-shaped bottom-first run of the parameterized lock ends with the
same counter, through the checked structural equivalence. -/
theorem structural_lock_run_ops (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (outcomes : List Bool) (final : CoreOpcodeStep.State)
    (success : CoreStructuralRun.run hashes
      (DynamicCheckedCertificate.program lock)
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) = some final) :
    final.ops = 201 := by
  rw [CoreStructuralEquiv.run_eq_byte] at success
  obtain ⟨byteFinal, byteRun, lifted⟩ := Option.map_eq_some_iff.mp success
  rw [← lifted]
  exact lock_run_ops_from_zero hashes lock stack outcomes byteFinal byteRun

end QSB.LockOpcodeBudget
