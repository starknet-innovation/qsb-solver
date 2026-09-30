import QSB.FirstAcceptedOrigin

/-!
The exact final key-roll suffix in the byte interpreter. This extends the
polymorphic list-roll count invariant to the generated raw index bytes.
Signature validity and Core refinement remain outside this module.
-/
namespace QSB.ByteFinalCounts
open ByteMachine
open FirstAcceptedOrigin
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def keyIndexBytes : List (Bytes × Nat) :=
  [([0x01], 1), ([0x45, 0x02], 581), ([0x46, 0x02], 582),
   ([0x47, 0x02], 583), ([0x48, 0x02], 584), ([0x49, 0x02], 585),
   ([0x4a, 0x02], 586), ([0x4b, 0x02], 587), ([0x4c, 0x02], 588),
   ([0x4d, 0x02], 589)]

def pairOps : List (Bytes × Nat) → List Op
  | [] => []
  | (raw, _) :: rest => .push raw :: .roll :: pairOps rest

def finalSetup : List Op :=
  [.push [0x0a]] ++ pairOps keyIndexBytes ++ [.push [0x0a]]

theorem generated_final_byte_suffix :
    ByteLayout.program.drop 857 =
      [.push [0x0a]] ++ pairOps keyIndexBytes ++
        [.push [0x0a], .checkmultisig] := by decide

theorem generated_final_setup_suffix :
    ByteLayout.program.drop 857 = finalSetup ++ [.checkmultisig] := by
  decide

theorem key_index_bytes_decode :
    ∀ pair ∈ keyIndexBytes,
      ByteIndex.parseScriptNum pair.1 = some (Int.ofNat pair.2) := by
  decide

theorem key_index_values : keyIndexBytes.map Prod.snd =
    KeyRolls.keyIndices := by decide

theorem push_success_shape (hashes : Hashes) (raw : Bytes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat) (next : State)
    (success : step hashes (.push raw)
      (State.mk stack outcomes cost) = some next) :
    next = State.mk (raw :: stack) outcomes cost := by
  unfold step at success
  by_cases budget : cost > 201
  · simp [budget] at success
  · by_cases size : raw.length > 520
    · simp [budget, size] at success
    · simp [budget, size] at success
      cases success
      rfl

theorem roll_success_budget (hashes : Hashes) (raw : Bytes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (next : State)
    (success : step hashes .roll
      (State.mk (raw :: stack) outcomes cost) = some next) :
    cost + 1 ≤ 201 := by
  by_contra tooMany
  have exceeded : cost + 1 > 201 := by omega
  unfold step at success
  simp [exceeded] at success

/-- A successful generated-style push/roll pair moves every stack cell
shallower than the rolled depth exactly one position deeper. -/
theorem accepted_pair_preserves_shallower (hashes : Hashes)
    (raw : Bytes) (n p : Nat) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat) (final : State) (marker : Bytes)
    (decoded : ByteIndex.parseScriptNum raw = some (Int.ofNat n))
    (shallower : p < n) (atP : stack[p]? = some marker)
    (accepted : run hashes [.push raw, .roll]
      (State.mk stack outcomes cost) = some final) :
    final.stack[p + 1]? = some marker := by
  obtain ⟨afterPush, pushed, _, remaining⟩ :=
    run_cons_success hashes (.push raw) [.roll]
      (State.mk stack outcomes cost) final accepted
  have pushShape := push_success_shape hashes raw stack outcomes cost
    afterPush pushed
  subst afterPush
  obtain ⟨afterRoll, rolled, _, finished⟩ :=
    run_cons_success hashes .roll []
      (State.mk (raw :: stack) outcomes cost) final remaining
  have budget := roll_success_budget hashes raw stack outcomes cost
    afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes raw n stack
    outcomes cost decoded budget] at rolled
  cases hroll : KeyRolls.rollAt n stack with
  | none => simp [hroll] at rolled
  | some rolledStack =>
      have markerMoved := KeyRolls.rollAt_preserves_shallower_cell
        shallower atP hroll
      simp [hroll] at rolled
      cases rolled
      simp [run] at finished
      cases finished
      exact markerMoved

theorem accepted_pair_preserves_shallower_option (hashes : Hashes)
    (raw : Bytes) (n p : Nat) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (decoded : ByteIndex.parseScriptNum raw = some (Int.ofNat n))
    (shallower : p < n)
    (accepted : run hashes [.push raw, .roll]
      (State.mk stack outcomes cost) = some final) :
    final.stack[p + 1]? = stack[p]? := by
  obtain ⟨afterPush, pushed, _, remaining⟩ :=
    run_cons_success hashes (.push raw) [.roll]
      (State.mk stack outcomes cost) final accepted
  have pushShape := push_success_shape hashes raw stack outcomes cost
    afterPush pushed
  subst afterPush
  obtain ⟨afterRoll, rolled, _, finished⟩ :=
    run_cons_success hashes .roll []
      (State.mk (raw :: stack) outcomes cost) final remaining
  have budget := roll_success_budget hashes raw stack outcomes cost
    afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes raw n stack
    outcomes cost decoded budget] at rolled
  cases hroll : KeyRolls.rollAt n stack with
  | none => simp [hroll] at rolled
  | some rolledStack =>
      have moved := KeyRolls.rollAt_preserves_shallower_option
        shallower hroll
      simp [hroll] at rolled
      cases rolled
      simp [run] at finished
      cases finished
      exact moved

/-- Repeating successful decoded push/roll pairs preserves the lock-pushed
count cell below all gathered keys. This permits arbitrary bytes and arbitrary
underlying stack cells. -/
theorem accepted_pairs_preserve_marker (hashes : Hashes)
    (pairs : List (Bytes × Nat)) (p : Nat)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State) (marker : Bytes)
    (decoded : ∀ pair ∈ pairs,
      ByteIndex.parseScriptNum pair.1 = some (Int.ofNat pair.2))
    (safe : KeyRolls.safeIndices p (pairs.map Prod.snd))
    (atP : stack[p]? = some marker)
    (accepted : run hashes (pairOps pairs)
      (State.mk stack outcomes cost) = some final) :
    final.stack[p + pairs.length]? = some marker := by
  induction pairs generalizing p stack outcomes cost final with
  | nil =>
      simp [pairOps, run] at accepted
      cases accepted
      simpa using atP
  | cons pair rest ih =>
      rcases pair with ⟨raw, n⟩
      have decodedHead : ByteIndex.parseScriptNum raw =
          some (Int.ofNat n) := decoded (raw, n) (by simp)
      have decodedTail : ∀ pair ∈ rest,
          ByteIndex.parseScriptNum pair.1 =
            some (Int.ofNat pair.2) := by
        intro pair membership
        exact decoded pair (by simp [membership])
      have safeHead : p < n := safe.1
      have safeTail : KeyRolls.safeIndices (p + 1)
          (rest.map Prod.snd) := safe.2
      have split : pairOps ((raw, n) :: rest) =
          [.push raw, .roll] ++ pairOps rest := rfl
      rw [split, run_append] at accepted
      cases first : run hashes [.push raw, .roll]
          (State.mk stack outcomes cost) with
      | none => simp [first] at accepted
      | some middle =>
          have markerMoved := accepted_pair_preserves_shallower
            hashes raw n p stack outcomes cost middle marker
            decodedHead safeHead atP first
          simp only [first, Option.bind_some] at accepted
          cases middle with
          | mk middleStack middleOutcomes middleCost =>
              have tail := ih (p + 1) middleStack middleOutcomes
                middleCost final decodedTail safeTail markerMoved accepted
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

theorem accepted_pairs_preserve_shallower_option (hashes : Hashes)
    (pairs : List (Bytes × Nat)) (p : Nat)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (decoded : ∀ pair ∈ pairs,
      ByteIndex.parseScriptNum pair.1 = some (Int.ofNat pair.2))
    (safe : KeyRolls.safeIndices p (pairs.map Prod.snd))
    (accepted : run hashes (pairOps pairs)
      (State.mk stack outcomes cost) = some final) :
    final.stack[p + pairs.length]? = stack[p]? := by
  induction pairs generalizing p stack outcomes cost final with
  | nil =>
      simp [pairOps, run] at accepted
      cases accepted
      simp
  | cons pair rest ih =>
      rcases pair with ⟨raw, n⟩
      have decodedHead : ByteIndex.parseScriptNum raw =
          some (Int.ofNat n) := decoded (raw, n) (by simp)
      have decodedTail : ∀ pair ∈ rest,
          ByteIndex.parseScriptNum pair.1 =
            some (Int.ofNat pair.2) := by
        intro pair membership
        exact decoded pair (by simp [membership])
      have safeHead : p < n := safe.1
      have safeTail : KeyRolls.safeIndices (p + 1)
          (rest.map Prod.snd) := safe.2
      have split : pairOps ((raw, n) :: rest) =
          [.push raw, .roll] ++ pairOps rest := rfl
      rw [split, run_append] at accepted
      cases first : run hashes [.push raw, .roll]
          (State.mk stack outcomes cost) with
      | none => simp [first] at accepted
      | some middle =>
          have moved := accepted_pair_preserves_shallower_option
            hashes raw n p stack outcomes cost middle
            decodedHead safeHead first
          simp only [first, Option.bind_some] at accepted
          cases middle with
          | mk middleStack middleOutcomes middleCost =>
              have tail := ih (p + 1) middleStack middleOutcomes
                middleCost final decodedTail safeTail accepted
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using tail.trans moved

/-- The first generated key roll takes the shallow key cell. In particular it
does not remove any of the following ten signature cells or their dummy. -/
theorem accepted_first_key_pair_shape (hashes : Hashes)
    (first : Bytes) (rest : List Bytes) (outcomes : List Bool) (cost : Nat)
    (next : State)
    (accepted : run hashes [.push [0x01], .roll]
      (State.mk ([0x0a] :: first :: rest) outcomes cost) = some next) :
    next.stack = first :: [0x0a] :: rest := by
  obtain ⟨afterPush, pushed, _, remaining⟩ :=
    run_cons_success hashes (.push [0x01]) [.roll]
      (State.mk ([0x0a] :: first :: rest) outcomes cost) next accepted
  have pushShape := push_success_shape hashes [0x01]
    ([0x0a] :: first :: rest) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨afterRoll, rolled, _, finished⟩ :=
    run_cons_success hashes .roll []
      (State.mk ([0x01] :: [0x0a] :: first :: rest) outcomes cost)
      next remaining
  have budget := roll_success_budget hashes [0x01]
    ([0x0a] :: first :: rest) outcomes cost afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes [0x01] 1
    ([0x0a] :: first :: rest) outcomes cost (by decide) budget] at rolled
  have oneRoll : KeyRolls.rollAt 1 ([0x0a] :: first :: rest) =
      some (first :: [0x0a] :: rest) := by rfl
  simp [oneRoll] at rolled
  cases rolled
  simp [run] at finished
  cases finished
  rfl

/-- The byte interpreter's generated final setup preserves every source cell
in the ten signature slots and the following dummy, for an arbitrary
underlying stack. Position `p` in `rest` becomes position `p+12` immediately
before CHECKMULTISIG; `p=0..9` are signatures and `p=10` is the dummy. -/
theorem accepted_final_setup_witness_option (hashes : Hashes)
    (first : Bytes) (rest : List Bytes)
    (outcomes : List Bool) (cost p : Nat) (beforeCheck : State)
    (hp : p ≤ 10)
    (accepted : run hashes finalSetup
      (State.mk (first :: rest) outcomes cost) = some beforeCheck) :
    beforeCheck.stack[p + 12]? = rest[p]? := by
  have setupSplit : finalSetup =
      .push [0x0a] ::
        ([.push [0x01], .roll] ++
          (pairOps keyIndexBytes.tail ++ [.push [0x0a]])) := by decide
  rw [setupSplit] at accepted
  obtain ⟨afterCount, countPush, _, remaining⟩ :=
    run_cons_success hashes (.push [0x0a])
      ([.push [0x01], .roll] ++
        (pairOps keyIndexBytes.tail ++ [.push [0x0a]]))
      (State.mk (first :: rest) outcomes cost) beforeCheck accepted
  have countShape := push_success_shape hashes [0x0a]
    (first :: rest) outcomes cost afterCount countPush
  subst afterCount
  rw [run_append] at remaining
  cases firstRun : run hashes [.push [0x01], .roll]
      (State.mk ([0x0a] :: first :: rest) outcomes cost) with
  | none => simp [firstRun] at remaining
  | some afterFirst =>
      have firstShape := accepted_first_key_pair_shape hashes first rest
        outcomes cost afterFirst firstRun
      simp only [firstRun, Option.bind_some] at remaining
      cases afterFirst with
      | mk firstStack firstOutcomes firstCost =>
          change firstStack = first :: [0x0a] :: rest at firstShape
          subst firstStack
          rw [run_append] at remaining
          cases tailRun : run hashes (pairOps keyIndexBytes.tail)
              (State.mk (first :: [0x0a] :: rest)
                firstOutcomes firstCost) with
          | none => simp [tailRun] at remaining
          | some afterTail =>
              have decoded : ∀ pair ∈ keyIndexBytes.tail,
                  ByteIndex.parseScriptNum pair.1 =
                    some (Int.ofNat pair.2) := by decide
              have safe : KeyRolls.safeIndices (p + 2)
                  (keyIndexBytes.tail.map Prod.snd) := by
                simp [keyIndexBytes, KeyRolls.safeIndices]
                omega
              have atStart :
                  (first :: [0x0a] :: rest)[p + 2]? = rest[p]? := by
                simp
              have tailMarker := accepted_pairs_preserve_shallower_option hashes
                keyIndexBytes.tail (p + 2)
                (first :: [0x0a] :: rest) firstOutcomes firstCost
                afterTail decoded safe tailRun
              have atEleven : afterTail.stack[p + 11]? = rest[p]? := by
                simpa [keyIndexBytes, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using tailMarker.trans atStart
              simp only [tailRun, Option.bind_some] at remaining
              cases afterTail with
              | mk tailStack tailOutcomes tailCost =>
                  obtain ⟨afterLastPush, lastPush, _, finished⟩ :=
                    run_cons_success hashes (.push [0x0a]) []
                      (State.mk tailStack tailOutcomes tailCost)
                      beforeCheck remaining
                  have lastShape := push_success_shape hashes [0x0a]
                    tailStack tailOutcomes tailCost afterLastPush lastPush
                  subst afterLastPush
                  simp [run] at finished
                  cases finished
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                    using atEleven

/-- The first key at the final-setup entrance is moved by the shallow roll,
then carried below nine deeper rolled keys and the final count push. It is
therefore the last reached CHECKMULTISIG key, at stack offset ten. -/
theorem accepted_final_setup_first_key (hashes : Hashes)
    (first : Bytes) (rest : List Bytes)
    (outcomes : List Bool) (cost : Nat) (beforeCheck : State)
    (accepted : run hashes finalSetup
      (State.mk (first :: rest) outcomes cost) = some beforeCheck) :
    beforeCheck.stack[10]? = some first := by
  have setupSplit : finalSetup =
      .push [0x0a] ::
        ([.push [0x01], .roll] ++
          (pairOps keyIndexBytes.tail ++ [.push [0x0a]])) := by decide
  rw [setupSplit] at accepted
  obtain ⟨afterCount, countPush, _, remaining⟩ :=
    run_cons_success hashes (.push [0x0a])
      ([.push [0x01], .roll] ++
        (pairOps keyIndexBytes.tail ++ [.push [0x0a]]))
      (State.mk (first :: rest) outcomes cost) beforeCheck accepted
  have countShape := push_success_shape hashes [0x0a]
    (first :: rest) outcomes cost afterCount countPush
  subst afterCount
  rw [run_append] at remaining
  cases firstRun : run hashes [.push [0x01], .roll]
      (State.mk ([0x0a] :: first :: rest) outcomes cost) with
  | none => simp [firstRun] at remaining
  | some afterFirst =>
      have firstShape := accepted_first_key_pair_shape hashes first rest
        outcomes cost afterFirst firstRun
      simp only [firstRun, Option.bind_some] at remaining
      cases afterFirst with
      | mk firstStack firstOutcomes firstCost =>
          change firstStack = first :: [0x0a] :: rest at firstShape
          subst firstStack
          rw [run_append] at remaining
          cases tailRun : run hashes (pairOps keyIndexBytes.tail)
              (State.mk (first :: [0x0a] :: rest)
                firstOutcomes firstCost) with
          | none => simp [tailRun] at remaining
          | some afterTail =>
              have decoded : ∀ pair ∈ keyIndexBytes.tail,
                  ByteIndex.parseScriptNum pair.1 =
                    some (Int.ofNat pair.2) := by decide
              have safe : KeyRolls.safeIndices 0
                  (keyIndexBytes.tail.map Prod.snd) := by
                simp [keyIndexBytes, KeyRolls.safeIndices]
              have firstAt : (first :: [0x0a] :: rest)[0]? =
                  some first := rfl
              have marker := accepted_pairs_preserve_marker hashes
                keyIndexBytes.tail 0 (first :: [0x0a] :: rest)
                firstOutcomes firstCost afterTail first decoded safe
                firstAt tailRun
              have atNine : afterTail.stack[9]? = some first := by
                simpa [keyIndexBytes] using marker
              simp only [tailRun, Option.bind_some] at remaining
              cases afterTail with
              | mk tailStack tailOutcomes tailCost =>
                  obtain ⟨afterLastPush, lastPush, _, finished⟩ :=
                    run_cons_success hashes (.push [0x0a]) []
                      (State.mk tailStack tailOutcomes tailCost)
                      beforeCheck remaining
                  have lastShape := push_success_shape hashes [0x0a]
                    tailStack tailOutcomes tailCost afterLastPush lastPush
                  subst afterLastPush
                  simp [run] at finished
                  cases finished
                  simpa using atNine

theorem accepted_final_setup_witness_cell (hashes : Hashes)
    (first marker : Bytes) (rest : List Bytes)
    (outcomes : List Bool) (cost p : Nat) (beforeCheck : State)
    (hp : p ≤ 10) (atP : rest[p]? = some marker)
    (accepted : run hashes finalSetup
      (State.mk (first :: rest) outcomes cost) = some beforeCheck) :
    beforeCheck.stack[p + 12]? = some marker := by
  rw [accepted_final_setup_witness_option hashes first rest
    outcomes cost p beforeCheck hp accepted]
  exact atP

/-- The byte interpreter's NULLDUMMY check forces the cell immediately after
the ten signature slots to be empty whenever the final CHECKMULTISIG executes.
This is the modeled consensus condition; Core refinement is separate. -/
theorem successful_final_check_dummy_empty (hashes : Hashes)
    (beforeCheck final : State)
    (keyCount : beforeCheck.stack[0]? = some [0x0a])
    (sigCount : beforeCheck.stack[11]? = some [0x0a])
    (accepted : run hashes [.checkmultisig] beforeCheck = some final) :
    beforeCheck.stack[22]? = some [] := by
  obtain ⟨afterCheck, checked, _, finished⟩ :=
    run_cons_success hashes .checkmultisig [] beforeCheck final accepted
  cases beforeCheck with
  | mk stack outcomes cost =>
      cases stack with
      | nil => simp at keyCount
      | cons rawN xs =>
          have rawTen : rawN = [0x0a] := by simpa using keyCount
          subst rawN
          have sigTen : xs[10]? = some [0x0a] := by simpa using sigCount
          have parseTen : ByteIndex.parseScriptNum [0x0a] = some 10 := by decide
          unfold step at checked
          simp only [parseTen] at checked
          split_ifs at checked; simp_all
          rcases checked with ⟨_, checked⟩
          cases hd : xs[21]? with
          | none => simp [hd] at checked
          | some dummy =>
              by_cases zero : dummy = []
              · simp [zero]
              · simp [hd, zero] at checked

theorem accepted_final_setup_count_operands (hashes : Hashes)
    (under : List Bytes) (outcomes : List Bool) (cost : Nat)
    (beforeCheck : State)
    (accepted : run hashes finalSetup
      (State.mk under outcomes cost) = some beforeCheck) :
    beforeCheck.stack[0]? = some [0x0a] ∧
    beforeCheck.stack[11]? = some [0x0a] := by
  have setupShape : finalSetup =
      .push [0x0a] :: (pairOps keyIndexBytes ++ [.push [0x0a]]) := rfl
  rw [setupShape] at accepted
  obtain ⟨afterFirstPush, firstPush, _, rest⟩ :=
    run_cons_success hashes (.push [0x0a])
      (pairOps keyIndexBytes ++ [.push [0x0a]])
      (State.mk under outcomes cost) beforeCheck accepted
  have firstShape := push_success_shape hashes [0x0a] under outcomes cost
    afterFirstPush firstPush
  subst afterFirstPush
  rw [run_append] at rest
  cases pairsRun : run hashes (pairOps keyIndexBytes)
      (State.mk ([0x0a] :: under) outcomes cost) with
  | none => simp [pairsRun] at rest
  | some afterPairs =>
      have markerAtZero : ([0x0a] :: under)[0]? = some [0x0a] := rfl
      have safe : KeyRolls.safeIndices 0
          (keyIndexBytes.map Prod.snd) := by
        rw [key_index_values]
        exact KeyRolls.key_indices_safe
      have marker := accepted_pairs_preserve_marker hashes
        keyIndexBytes 0 ([0x0a] :: under) outcomes cost afterPairs
        [0x0a] key_index_bytes_decode safe markerAtZero pairsRun
      have atTen : afterPairs.stack[10]? = some [0x0a] := by
        simpa [keyIndexBytes] using marker
      simp only [pairsRun, Option.bind_some] at rest
      cases afterPairs with
      | mk pairStack pairOutcomes pairCost =>
          obtain ⟨afterLastPush, lastPush, _, finished⟩ :=
            run_cons_success hashes (.push [0x0a]) []
              (State.mk pairStack pairOutcomes pairCost)
              beforeCheck rest
          have lastShape := push_success_shape hashes [0x0a]
            pairStack pairOutcomes pairCost afterLastPush lastPush
          subst afterLastPush
          simp [run] at finished
          cases finished
          exact ⟨rfl, by simpa using atTen⟩

/-- The generated byte suffix reaches its last CHECKMULTISIG with both
count operands fixed to ten, for any underlying stack and any outcomes on
which the whole suffix succeeds. This identifies no signature/key bytes. -/
theorem accepted_final_suffix_count_operands (hashes : Hashes)
    (under : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (ByteLayout.program.drop 857)
      (State.mk under outcomes cost) = some final) :
    ∃ beforeCheck,
      run hashes finalSetup (State.mk under outcomes cost) = some beforeCheck ∧
      beforeCheck.stack[0]? = some [0x0a] ∧
      beforeCheck.stack[11]? = some [0x0a] := by
  rw [generated_final_setup_suffix] at accepted
  obtain ⟨beforeCheck, setupRun⟩ := successful_prefix hashes
    finalSetup [.checkmultisig] (State.mk under outcomes cost)
    final accepted
  obtain ⟨keyCount, sigCount⟩ :=
    accepted_final_setup_count_operands hashes under outcomes cost
      beforeCheck setupRun
  exact ⟨beforeCheck, setupRun, keyCount, sigCount⟩

/-- A successful generated final suffix forces the source cell following the
ten signature cells to exist and be empty. This uses
the modeled NULLDUMMY rule in CHECKMULTISIG and the arbitrary-stack cell
origin theorem, not any assumption about canonical earlier selections. -/
theorem accepted_final_suffix_source_dummy_empty (hashes : Hashes)
    (first : Bytes) (rest : List Bytes)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (ByteLayout.program.drop 857)
      (State.mk (first :: rest) outcomes cost) = some final) :
    rest[10]? = some [] := by
  rw [generated_final_setup_suffix, run_append] at accepted
  cases setup : run hashes finalSetup
      (State.mk (first :: rest) outcomes cost) with
  | none => simp [setup] at accepted
  | some beforeCheck =>
      simp only [setup, Option.bind_some] at accepted
      have origin := accepted_final_setup_witness_option hashes first
        rest outcomes cost 10 beforeCheck (by omega) setup
      obtain ⟨keyCount, sigCount⟩ :=
        accepted_final_setup_count_operands hashes
          (first :: rest) outcomes cost beforeCheck setup
      have empty := successful_final_check_dummy_empty hashes
        beforeCheck final keyCount sigCount accepted
      exact origin.symm.trans empty

/-- A true final stack result requires the Boolean supplied to the last
modeled CHECKMULTISIG to be true, regardless of earlier signature outcomes. -/
theorem successful_last_multisig_requires_true_outcome (hashes : Hashes)
    (beforeCheck final : State)
    (accepted : run hashes [.checkmultisig] beforeCheck = some final)
    (truth : finalTruth final = true) :
    beforeCheck.outcomes.head? = some true := by
  obtain ⟨afterCheck, checked, _, finished⟩ :=
    run_cons_success hashes .checkmultisig [] beforeCheck final accepted
  simp [run] at finished
  subst final
  cases beforeCheck with
  | mk stack outcomes cost =>
      cases outcomes with
      | nil =>
          cases stack with
          | nil =>
              unfold step at checked
              simp at checked
          | cons rawN xs =>
              unfold step at checked
              simp at checked
      | cons first remaining =>
          cases first with
          | true => rfl
          | false =>
              simp only [List.head?_cons]
              cases stack with
              | nil =>
                  unfold step at checked
                  simp at checked
              | cons rawN xs =>
                  unfold step at checked
                  simp [finalTruth, boolBytes] at checked truth
                  obtain ⟨_, checked⟩ := checked
                  cases hn : ByteIndex.parseScriptNum rawN with
                  | none => simp [hn] at checked
                  | some n =>
                      simp only [hn, Option.bind_some] at checked
                      by_cases invalidN :
                          n < 0 ∨ 20 < n ∨ 201 < cost + 1 + n.toNat
                      · simp [invalidN] at checked
                      · simp only [if_neg invalidN] at checked
                        cases hm : xs[n.toNat]? with
                        | none => simp [hm] at checked
                        | some rawM =>
                            simp only [hm, Option.bind_some] at checked
                            cases hparsedM : ByteIndex.parseScriptNum rawM with
                            | none => simp [hparsedM] at checked
                            | some m =>
                                simp only [hparsedM, Option.bind_some] at checked
                                by_cases invalidM : m < 0 ∨ n < m
                                · simp [invalidM] at checked
                                · simp only [if_neg invalidM] at checked
                                  cases hd : xs[n.toNat + 1 + m.toNat]? with
                                  | none => simp [hd] at checked
                                  | some dummy =>
                                      simp only [hd, Option.bind_some] at checked
                                      by_cases nonzero : dummy ≠ []
                                      · simp [nonzero] at checked
                                      · have zero : dummy = [] := by simpa using nonzero
                                        simp [zero] at checked
                                        cases checked
                                        simp at truth

/-- Successful, truthy execution of the generated final suffix forces the
last modeled signature outcome true and both CHECKMULTISIG count operands ten.
The signature outcome is still an external Boolean, not a verified ECDSA
result. -/
theorem accepted_true_final_suffix (hashes : Hashes)
    (under : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (ByteLayout.program.drop 857)
      (State.mk under outcomes cost) = some final)
    (truth : finalTruth final = true) :
    ∃ beforeCheck,
      run hashes finalSetup (State.mk under outcomes cost) = some beforeCheck ∧
      beforeCheck.stack[0]? = some [0x0a] ∧
      beforeCheck.stack[11]? = some [0x0a] ∧
      beforeCheck.outcomes.head? = some true := by
  rw [generated_final_setup_suffix, run_append] at accepted
  cases setup : run hashes finalSetup
      (State.mk under outcomes cost) with
  | none => simp [setup] at accepted
  | some beforeCheck =>
      simp only [setup, Option.bind_some] at accepted
      obtain ⟨keyCount, sigCount⟩ :=
        accepted_final_setup_count_operands hashes under outcomes cost
          beforeCheck setup
      have finalOutcome := successful_last_multisig_requires_true_outcome
        hashes beforeCheck final accepted truth
      exact ⟨beforeCheck, by simp, keyCount, sigCount, finalOutcome⟩

/-- The final round is enforced by the *whole* generated byte program on
every modeled accepting run with a true stack top, for an arbitrary initial
byte stack. No canonical scriptSig shape or earlier multisig outcome is used.
-/
theorem accepted_true_whole_program_final_counts (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (truth : finalTruth final = true) :
    ∃ beforeSuffix beforeCheck,
      run hashes (ByteLayout.program.take 857) initial = some beforeSuffix ∧
      run hashes finalSetup beforeSuffix = some beforeCheck ∧
      beforeCheck.stack[0]? = some [0x0a] ∧
      beforeCheck.stack[11]? = some [0x0a] ∧
      beforeCheck.outcomes.head? = some true := by
  have split : ByteLayout.program = ByteLayout.program.take 857 ++
      ByteLayout.program.drop 857 := by decide
  rw [split, run_append] at accepted
  cases prefixRun : run hashes (ByteLayout.program.take 857) initial with
  | none => simp [prefixRun] at accepted
  | some beforeSuffix =>
      simp only [prefixRun, Option.bind_some] at accepted
      cases beforeSuffix with
      | mk under outcomes cost =>
          obtain ⟨beforeCheck, setup, keyCount, sigCount, lastTrue⟩ :=
            accepted_true_final_suffix hashes under outcomes cost final
              accepted truth
          exact ⟨State.mk under outcomes cost, beforeCheck, by simp,
            setup, keyCount, sigCount, lastTrue⟩

end QSB.ByteFinalCounts
