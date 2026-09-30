import QSB.ByteFinalCounts

/-!
The generated seven-opcode puzzle segment between the final bonus selection
and the final key-roll suffix. It moves a deep key to the top, hashes that key,
rolls in a deep verifier key, and runs CHECKSIGVERIFY. Conditional on modeled
success, the shallow signature/dummy cells are preserved in order. Their
origin before the final bonus selection remains a separate obligation.
-/
namespace QSB.ByteLatePuzzle
open ByteMachine
open ByteFinalCounts
open FirstAcceptedOrigin
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def lateOps : List Op := ByteLayout.program.drop 850 |>.take 7

theorem generated_late_ops : lateOps =
    [.push [0x4c, 0x02], .roll, .dup, .sha256,
     .push [0x4e, 0x02], .roll, .checksigverify] := by decide

theorem late_indices_decode :
    ByteIndex.parseScriptNum [0x4c, 0x02] = some 588 ∧
    ByteIndex.parseScriptNum [0x4e, 0x02] = some 590 := by decide

/-- Successful DUP;SHA256 keeps the input top cell immediately below its
hash and leaves the remaining tail unchanged. -/
theorem accepted_dup_sha256_shape (hashes : Hashes)
    (before after : State)
    (accepted : run hashes [.dup, .sha256] before = some after) :
    ∃ x xs, before.stack = x :: xs ∧
      after.stack = hashes.h256 x :: x :: xs := by
  obtain ⟨afterDup, dupStep, _, shaRun⟩ :=
    run_cons_success hashes .dup [.sha256] before after accepted
  cases before with
  | mk stack outcomes cost =>
      cases stack with
      | nil =>
          change (if cost + 1 > 201 then none else none) = some afterDup at dupStep
          simp at dupStep
      | cons x xs =>
          have dupShape : afterDup.stack = x :: x :: xs := by
            change (if cost + 1 > 201 then none else
              some (State.mk (x :: x :: xs) outcomes (cost + 1))) =
                some afterDup at dupStep
            split_ifs at dupStep; simp_all
            cases dupStep
            rfl
          obtain ⟨afterHash, hashStep, _, finished⟩ :=
            run_cons_success hashes .sha256 [] afterDup after shaRun
          cases afterDup with
          | mk dupStack dupOutcomes dupCost =>
              change dupStack = x :: x :: xs at dupShape
              subst dupStack
              have hashShape : afterHash.stack = hashes.h256 x :: x :: xs := by
                change (if dupCost + 1 > 201 then none else
                  some (State.mk (hashes.h256 x :: x :: xs)
                    dupOutcomes (dupCost + 1))) = some afterHash at hashStep
                split_ifs at hashStep; simp_all
                cases hashStep
                rfl
              simp [run] at finished
              cases finished
              exact ⟨x, xs, rfl, hashShape⟩

/-- A successful CHECKSIGVERIFY pops precisely two top cells. The supplied
Boolean outcome is external to Core signature verification. -/
theorem accepted_checksigverify_tail (hashes : Hashes)
    (before after : State)
    (accepted : run hashes [.checksigverify] before = some after) :
    ∃ pub sig tail, before.stack = pub :: sig :: tail ∧
      after.stack = tail := by
  obtain ⟨next, checked, _, finished⟩ :=
    run_cons_success hashes .checksigverify [] before after accepted
  cases before with
  | mk stack outcomes cost =>
      cases stack with
      | nil =>
          change (if cost + 1 > 201 then none else none) = some next at checked
          simp at checked
      | cons pub rest =>
          cases rest with
          | nil =>
              change (if cost + 1 > 201 then none else none) = some next at checked
              simp at checked
          | cons sig tail =>
              cases outcomes with
              | nil =>
                  change (if cost + 1 > 201 then none else none) = some next at checked
                  simp at checked
              | cons outcome more =>
                  cases outcome with
                  | false =>
                      change (if cost + 1 > 201 then none else none) = some next at checked
                      simp at checked
                  | true =>
                      have shape : next.stack = tail := by
                        change (if cost + 1 > 201 then none else
                          some (State.mk tail more (cost + 1))) = some next at checked
                        split_ifs at checked; simp_all
                        cases checked
                        rfl
                      simp [run] at finished
                      cases finished
                      exact ⟨pub, sig, tail, rfl, shape⟩

/-- The bytes SHA256-hashed as the late puzzle signature are exactly the
key left on top after CHECKSIGVERIFY. This identifies the actual consumed
signature bytes in the byte model; the successful signature Boolean remains
external to Core. -/
theorem accepted_late_puzzle_key (hashes : Hashes)
    (before after : State)
    (accepted : run hashes lateOps before = some after) :
    ∃ key beforeVerify,
      run hashes (lateOps.take 6) before = some beforeVerify ∧
      beforeVerify.stack[1]? = some (hashes.h256 key) ∧
      after.stack[0]? = some key ∧
      run hashes [.checksigverify] beforeVerify = some after := by
  rw [generated_late_ops] at accepted
  have split : ([.push [0x4c, 0x02], .roll, .dup, .sha256,
      .push [0x4e, 0x02], .roll, .checksigverify] : List Op) =
      [.push [0x4c, 0x02], .roll] ++
      ([.dup, .sha256] ++
        ([.push [0x4e, 0x02], .roll] ++ [.checksigverify])) := rfl
  rw [split, run_append] at accepted
  cases firstRun : run hashes [.push [0x4c, 0x02], .roll] before with
  | none => simp [firstRun] at accepted
  | some afterFirst =>
      simp only [firstRun, Option.bind_some] at accepted
      rw [run_append] at accepted
      cases hashRun : run hashes [.dup, .sha256] afterFirst with
      | none => simp [hashRun] at accepted
      | some afterHash =>
          obtain ⟨key, xs, _, hashShape⟩ :=
            accepted_dup_sha256_shape hashes afterFirst afterHash hashRun
          simp only [hashRun, Option.bind_some] at accepted
          rw [run_append] at accepted
          cases secondRun : run hashes [.push [0x4e, 0x02], .roll]
              afterHash with
          | none => simp [secondRun] at accepted
          | some beforeVerify =>
              cases afterHash with
              | mk hashStack hashOutcomes hashCost =>
                  change hashStack = hashes.h256 key :: key :: xs at hashShape
                  have sigPreserved := accepted_pair_preserves_shallower_option
                    hashes [0x4e, 0x02] 590 0 hashStack
                    hashOutcomes hashCost beforeVerify late_indices_decode.2
                    (by omega) secondRun
                  have keyPreserved := accepted_pair_preserves_shallower_option
                    hashes [0x4e, 0x02] 590 1 hashStack
                    hashOutcomes hashCost beforeVerify late_indices_decode.2
                    (by omega) secondRun
                  have sigAt : beforeVerify.stack[1]? =
                      some (hashes.h256 key) := by
                    rw [hashShape] at sigPreserved
                    simpa using sigPreserved
                  have keyAt : beforeVerify.stack[2]? = some key := by
                    rw [hashShape] at keyPreserved
                    simpa using keyPreserved
                  simp only [secondRun, Option.bind_some] at accepted
                  obtain ⟨_pub, _sig, tail, verifyShape, afterShape⟩ :=
                    accepted_checksigverify_tail hashes beforeVerify after
                      accepted
                  have keyTail : tail[0]? = some key := by
                    rw [verifyShape] at keyAt
                    simpa using keyAt
                  have prefixOps : lateOps.take 6 =
                      ([.push [0x4c, 0x02], .roll] ++
                        [.dup, .sha256]) ++
                        [.push [0x4e, 0x02], .roll] := by decide
                  have prefixRun : run hashes (lateOps.take 6) before =
                      some beforeVerify := by
                    rw [prefixOps, run_append, run_append]
                    simp [firstRun, hashRun, secondRun]
                  refine ⟨key, beforeVerify, prefixRun, sigAt, ?_, accepted⟩
                  rw [afterShape]
                  exact keyTail

/-- Every shallow cell through the prospective NULLDUMMY slot survives the
exact puzzle segment, shifted one place below the deep key moved to the top.
This statement starts after the last bonus roll and assumes only successful
execution of these seven byte-model instructions. -/
theorem accepted_late_preserves_witness_option (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (cost p : Nat)
    (beforeSuffix : State) (hp : p ≤ 10)
    (accepted : run hashes lateOps
      (State.mk stack outcomes cost) = some beforeSuffix) :
    beforeSuffix.stack[p + 1]? = stack[p]? := by
  rw [generated_late_ops] at accepted
  have split : ([.push [0x4c, 0x02], .roll, .dup, .sha256,
      .push [0x4e, 0x02], .roll, .checksigverify] : List Op) =
      [.push [0x4c, 0x02], .roll] ++
      ([.dup, .sha256] ++
        ([.push [0x4e, 0x02], .roll] ++ [.checksigverify])) := rfl
  rw [split, run_append] at accepted
  cases firstRun : run hashes [.push [0x4c, 0x02], .roll]
      (State.mk stack outcomes cost) with
  | none => simp [firstRun] at accepted
  | some afterFirst =>
      have firstKeep := accepted_pair_preserves_shallower_option hashes
        [0x4c, 0x02] 588 p stack outcomes cost afterFirst
        late_indices_decode.1 (by omega) firstRun
      simp only [firstRun, Option.bind_some] at accepted
      rw [run_append] at accepted
      cases hashRun : run hashes [.dup, .sha256] afterFirst with
      | none => simp [hashRun] at accepted
      | some afterHash =>
          obtain ⟨x, xs, firstShape, hashShape⟩ :=
            accepted_dup_sha256_shape hashes afterFirst afterHash hashRun
          have hashKeep : afterHash.stack[p + 2]? = stack[p]? := by
            rw [hashShape]
            rw [firstShape] at firstKeep
            simpa using firstKeep
          simp only [hashRun, Option.bind_some] at accepted
          rw [run_append] at accepted
          cases secondRun : run hashes [.push [0x4e, 0x02], .roll]
              afterHash with
          | none => simp [secondRun] at accepted
          | some beforeVerify =>
              cases afterHash with
              | mk hashStack hashOutcomes hashCost =>
                  have secondKeep := accepted_pair_preserves_shallower_option
                    hashes [0x4e, 0x02] 590 (p + 2) hashStack
                    hashOutcomes hashCost beforeVerify late_indices_decode.2
                    (by omega) secondRun
                  have beforeKeep : beforeVerify.stack[p + 3]? = stack[p]? := by
                    simpa [Nat.add_assoc] using secondKeep.trans hashKeep
                  simp only [secondRun, Option.bind_some] at accepted
                  obtain ⟨pub, sig, tail, verifyShape, finalShape⟩ :=
                    accepted_checksigverify_tail hashes beforeVerify
                      beforeSuffix accepted
                  rw [finalShape]
                  rw [verifyShape] at beforeKeep
                  simpa [Nat.add_assoc] using beforeKeep

/-- Composing the seven-opcode puzzle segment with the generated key-roll
setup identifies each final signature slot directly with a cell immediately
after the last bonus roll. The intervening puzzle key and hash operations do
not replace any of those eleven shallow cells. -/
theorem accepted_late_final_witness_origin (hashes : Hashes)
    (afterBonus : List Bytes) (outcomes : List Bool) (cost : Nat)
    (first : Bytes) (rest : List Bytes)
    (laterOutcomes : List Bool) (laterCost p : Nat)
    (beforeCheck : State) (hp : p ≤ 10)
    (late : run hashes lateOps
      (State.mk afterBonus outcomes cost) =
        some (State.mk (first :: rest) laterOutcomes laterCost))
    (setup : run hashes ByteFinalCounts.finalSetup
      (State.mk (first :: rest) laterOutcomes laterCost) = some beforeCheck) :
    beforeCheck.stack[p + 12]? = afterBonus[p]? := by
  have lateCell := accepted_late_preserves_witness_option hashes
    afterBonus outcomes cost p
    (State.mk (first :: rest) laterOutcomes laterCost) hp late
  change rest[p]? = afterBonus[p]? at lateCell
  have finalCell := ByteFinalCounts.accepted_final_setup_witness_option
    hashes first rest laterOutcomes laterCost p beforeCheck hp setup
  exact finalCell.trans lateCell

/-- A successful modeled final suffix forces the post-bonus dummy source to
be empty as well. This is conditional on the actual seven-opcode puzzle
segment succeeding; it does not classify which earlier selection supplied
the ten signature cells. -/
theorem accepted_late_final_dummy_source_empty (hashes : Hashes)
    (afterBonus : List Bytes) (outcomes : List Bool) (cost : Nat)
    (first : Bytes) (rest : List Bytes)
    (laterOutcomes : List Bool) (laterCost : Nat) (final : State)
    (late : run hashes lateOps
      (State.mk afterBonus outcomes cost) =
        some (State.mk (first :: rest) laterOutcomes laterCost))
    (suffix : run hashes (ByteLayout.program.drop 857)
      (State.mk (first :: rest) laterOutcomes laterCost) = some final) :
    afterBonus[10]? = some [] := by
  have lateCell := accepted_late_preserves_witness_option hashes
    afterBonus outcomes cost 10
    (State.mk (first :: rest) laterOutcomes laterCost) (by omega) late
  change rest[10]? = afterBonus[10]? at lateCell
  have sourceEmpty := ByteFinalCounts.accepted_final_suffix_source_dummy_empty
    hashes first rest laterOutcomes laterCost final suffix
  exact lateCell.symm.trans sourceEmpty

/-- The generated final suffix cannot start from an empty stack: its first
key roll asks for depth one after the lock has pushed the count and index. -/
theorem final_suffix_rejects_empty_stack (hashes : Hashes)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (ByteLayout.program.drop 857)
      (State.mk [] outcomes cost) = some final) : False := by
  rw [ByteFinalCounts.generated_final_setup_suffix] at accepted
  have split : ByteFinalCounts.finalSetup ++ [.checkmultisig] =
      .push [0x0a] :: .push [0x01] :: .roll ::
        (ByteFinalCounts.pairOps ByteFinalCounts.keyIndexBytes.tail ++
          [.push [0x0a], .checkmultisig]) := by decide
  rw [split] at accepted
  obtain ⟨afterCount, countPush, _, afterCountRun⟩ :=
    run_cons_success hashes (.push [0x0a])
      (.push [0x01] :: .roll ::
        (ByteFinalCounts.pairOps ByteFinalCounts.keyIndexBytes.tail ++
          [.push [0x0a], .checkmultisig]))
      (State.mk [] outcomes cost) final accepted
  have countShape := ByteFinalCounts.push_success_shape hashes
    [0x0a] [] outcomes cost afterCount countPush
  subst afterCount
  obtain ⟨afterIndex, indexPush, _, remaining⟩ :=
    run_cons_success hashes (.push [0x01])
      (.roll :: (ByteFinalCounts.pairOps
        ByteFinalCounts.keyIndexBytes.tail ++
          [.push [0x0a], .checkmultisig]))
      (State.mk [[0x0a]] outcomes cost) final afterCountRun
  have indexShape := ByteFinalCounts.push_success_shape hashes
    [0x01] [[0x0a]] outcomes cost afterIndex indexPush
  subst afterIndex
  obtain ⟨afterRoll, rolled, _, _⟩ :=
    run_cons_success hashes .roll
      (ByteFinalCounts.pairOps ByteFinalCounts.keyIndexBytes.tail ++
        [.push [0x0a], .checkmultisig])
      (State.mk [[0x01], [0x0a]] outcomes cost) final remaining
  unfold step at rolled
  simp [ByteIndex.parseScriptNum] at rolled
  have one : ByteIndex.unsignedLE [1] = 1 := by decide
  rw [one] at rolled
  simp at rolled

/-- No explicit intermediate-stack shape is needed. Every successful modeled
late-puzzle-plus-final-suffix execution forces the cell immediately after the
last bonus selection at offset ten to be the empty CHECKMULTISIG dummy. -/
theorem accepted_late_suffix_dummy_empty (hashes : Hashes)
    (afterBonus : List Bytes) (outcomes : List Bool) (cost : Nat)
    (beforeSuffix final : State)
    (late : run hashes lateOps
      (State.mk afterBonus outcomes cost) = some beforeSuffix)
    (suffix : run hashes (ByteLayout.program.drop 857)
      beforeSuffix = some final) :
    afterBonus[10]? = some [] := by
  cases beforeSuffix with
  | mk stack laterOutcomes laterCost =>
      cases stack with
      | nil =>
          exact (final_suffix_rejects_empty_stack hashes
            laterOutcomes laterCost final suffix).elim
      | cons first rest =>
          exact accepted_late_final_dummy_source_empty hashes
            afterBonus outcomes cost first rest laterOutcomes
            laterCost final late suffix

theorem generated_late_final_suffix :
    ByteLayout.program.drop 850 =
      lateOps ++ ByteLayout.program.drop 857 := by decide

theorem generated_late_final_check_split :
    ByteLayout.program.drop 850 =
      (lateOps ++ ByteFinalCounts.finalSetup) ++ [.checkmultisig] := by decide

/-- In every successful final byte-model suffix, the signature consumed by
the late puzzle CHECKSIGVERIFY is SHA256 of the last reached multisignature
key. The modeled signature outcomes remain externally supplied. -/
theorem accepted_late_final_puzzle_key (hashes : Hashes)
    (afterBonus final : State)
    (accepted : run hashes (ByteLayout.program.drop 850)
      afterBonus = some final) :
    ∃ key beforeVerify beforeSuffix beforeCheck,
      run hashes lateOps afterBonus = some beforeSuffix ∧
      run hashes (lateOps.take 6) afterBonus = some beforeVerify ∧
      run hashes [.checksigverify] beforeVerify = some beforeSuffix ∧
      beforeVerify.stack[1]? = some (hashes.h256 key) ∧
      run hashes ByteFinalCounts.finalSetup beforeSuffix = some beforeCheck ∧
      beforeCheck.stack[10]? = some key := by
  rw [generated_late_final_check_split] at accepted
  obtain ⟨beforeCheck, prefixRun⟩ := successful_prefix hashes
    (lateOps ++ ByteFinalCounts.finalSetup) [.checkmultisig]
    afterBonus final accepted
  rw [run_append] at prefixRun
  cases lateRun : run hashes lateOps afterBonus with
  | none => simp [lateRun] at prefixRun
  | some beforeSuffix =>
      simp only [lateRun, Option.bind_some] at prefixRun
      obtain ⟨key, beforeVerify, puzzlePrefix, sigAt, keyAt,
        verifyRun⟩ :=
        accepted_late_puzzle_key hashes afterBonus beforeSuffix lateRun
      cases beforeSuffix with
      | mk stack outcomes cost =>
          cases stack with
          | nil => simp at keyAt
          | cons first rest =>
              have firstKey : first = key := by simpa using keyAt
              subst first
              have keyReached := ByteFinalCounts.accepted_final_setup_first_key
                hashes key rest outcomes cost beforeCheck prefixRun
              exact ⟨key, beforeVerify,
                State.mk (key :: rest) outcomes cost, beforeCheck,
                rfl, puzzlePrefix, verifyRun, sigAt, prefixRun, keyReached⟩

/-- The same puzzle-to-last-key relation for a successful execution of all
880 generated byte-model opcodes, from an arbitrary initial byte stack. -/
theorem accepted_whole_program_final_puzzle_key (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final) :
    ∃ key beforeVerify beforeSuffix beforeCheck,
      run hashes (ByteLayout.program.take 856) initial = some beforeVerify ∧
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      run hashes [.checksigverify] beforeVerify = some beforeSuffix ∧
      beforeVerify.stack[1]? = some (hashes.h256 key) ∧
      beforeCheck.stack[10]? = some key := by
  have split : ByteLayout.program =
      ByteLayout.program.take 850 ++ ByteLayout.program.drop 850 :=
    (List.take_append_drop 850 ByteLayout.program).symm
  rw [split, run_append] at accepted
  cases prefixRun : run hashes (ByteLayout.program.take 850) initial with
  | none => simp [prefixRun] at accepted
  | some afterBonus =>
      simp only [prefixRun, Option.bind_some] at accepted
      obtain ⟨key, beforeVerify, beforeSuffix, beforeCheck,
        lateRun, puzzlePrefix, verifyRun, sigAt, setupRun, keyAt⟩ :=
          accepted_late_final_puzzle_key hashes afterBonus final accepted
      have puzzleSplit : ByteLayout.program.take 856 =
          ByteLayout.program.take 850 ++ lateOps.take 6 := by decide
      have puzzleReached : run hashes (ByteLayout.program.take 856)
          initial = some beforeVerify := by
        rw [puzzleSplit, run_append]
        simp [prefixRun, puzzlePrefix]
      have precheckSplit : ByteLayout.program.take 879 =
          (ByteLayout.program.take 850 ++ lateOps) ++
            ByteFinalCounts.finalSetup := by decide
      have reached : run hashes (ByteLayout.program.take 879)
          initial = some beforeCheck := by
        rw [precheckSplit, run_append, run_append]
        simp [prefixRun, lateRun, setupRun]
      exact ⟨key, beforeVerify, beforeSuffix, beforeCheck,
        puzzleReached, reached, verifyRun, sigAt, keyAt⟩

/-- For every successful modeled execution from just after the last bonus
roll, the final ten signature slots and dummy slot are exactly the first
eleven cells of that post-bonus stack. This is a byte-level provenance result
across the puzzle segment and key-roll suffix, not a classification of the
earlier nine selections or a Core signature-verification theorem. -/
theorem accepted_generated_final_witness_origins (hashes : Hashes)
    (afterBonus : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (ByteLayout.program.drop 850)
      (State.mk afterBonus outcomes cost) = some final) :
    ∃ beforeCheck,
      run hashes (lateOps ++ ByteFinalCounts.finalSetup)
        (State.mk afterBonus outcomes cost) = some beforeCheck ∧
      ∀ p : Nat, p ≤ 10 →
        beforeCheck.stack[p + 12]? = afterBonus[p]? := by
  have full := accepted
  rw [generated_late_final_suffix, run_append] at full
  rw [generated_late_final_check_split] at accepted
  obtain ⟨beforeCheck, prefixRun⟩ := successful_prefix hashes
    (lateOps ++ ByteFinalCounts.finalSetup) [.checkmultisig]
    (State.mk afterBonus outcomes cost) final accepted
  refine ⟨beforeCheck, prefixRun, ?_⟩
  rw [run_append] at prefixRun
  cases late : run hashes lateOps
      (State.mk afterBonus outcomes cost) with
  | none => simp [late] at prefixRun
  | some beforeSuffix =>
      simp only [late, Option.bind_some] at prefixRun
      cases beforeSuffix with
      | mk stack laterOutcomes laterCost =>
          cases stack with
          | nil =>
              simp only [late, Option.bind_some] at full
              exact (final_suffix_rejects_empty_stack hashes
                laterOutcomes laterCost final full).elim
          | cons first rest =>
              intro p hp
              exact accepted_late_final_witness_origin hashes
                afterBonus outcomes cost first rest laterOutcomes
                laterCost p beforeCheck hp late prefixRun

/-- Every successful byte-model run of the actual generated program from
immediately after the final bonus roll forces the post-bonus stack cell at
offset ten to be the empty NULLDUMMY source. The preceding signed/bonus
selection provenance remains unproved. -/
theorem accepted_generated_postbonus_dummy_empty (hashes : Hashes)
    (afterBonus : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (ByteLayout.program.drop 850)
      (State.mk afterBonus outcomes cost) = some final) :
    afterBonus[10]? = some [] := by
  rw [generated_late_final_suffix, run_append] at accepted
  cases late : run hashes lateOps
      (State.mk afterBonus outcomes cost) with
  | none => simp [late] at accepted
  | some beforeSuffix =>
      simp only [late, Option.bind_some] at accepted
      exact accepted_late_suffix_dummy_empty hashes afterBonus
        outcomes cost beforeSuffix final late accepted

end QSB.ByteLatePuzzle
