import QSB.FinalSignedBoundary
import QSB.FirstNumericRange

/-!
Execution bridge for the first signed selection in the generated final
round. This starts after the fixed deep roll has fetched the raw index, but
allows arbitrary raw ScriptNum encoding and arbitrary earlier stack tail.
-/
namespace QSB.FinalSignedAccepted
open ByteMachine
open FinalSignedBoundary
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def capAddOps : List Op := ByteLayout.program.drop 751 |>.take 5

theorem generated_cap_add_ops : capAddOps =
    [.push [0x98, 0x00], .min, .dup,
      .push [0x97, 0x00], .add] := by decide

def firstComparisonOps : List Op := ByteLayout.program.drop 751 |>.take 10

theorem generated_first_comparison_ops : firstComparisonOps =
    capAddOps ++ (ByteLayout.program.drop 756).take 5 := by decide

def baseRegion (prior : Bytes) (tail : List Bytes) : List Bytes :=
  finalNonce :: [] :: (finalDummyPool ++ finalCommitmentPool ++ prior :: tail)

theorem lookup_region_is_retained_base (retained prior : Bytes)
    (tail : List Bytes) :
    lookupRegion retained prior tail = retained :: baseRegion prior tail := rfl

/-- A successful sequence of literal pushes has its exact stack effect even
when the starting stack and opcode count are arbitrary. -/
theorem accepted_pushes_shape (hashes : Hashes) (values : List Bytes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (values.map Op.push)
      (State.mk stack outcomes cost) = some final) :
    final = State.mk (values.reverse ++ stack) outcomes cost := by
  induction values generalizing stack outcomes cost with
  | nil =>
      simp [run] at accepted
      cases accepted
      rfl
  | cons value rest ih =>
      obtain ⟨next, pushed, _, remaining⟩ :=
        FirstAcceptedOrigin.run_cons_success hashes (.push value)
          (rest.map Op.push) (State.mk stack outcomes cost) final
          (by simpa using accepted)
      have pushShape := ByteFinalCounts.push_success_shape hashes value
        stack outcomes cost next pushed
      subst next
      have result := ih (value :: stack) outcomes cost remaining
      simpa [List.reverse_cons, List.append_assoc] using result

def finalRoundAllOps : List Op := ByteLayout.program.drop 447 |>.take 302

theorem generated_final_round_all_pushes : finalRoundAllOps =
    (finalCommitmentPushes ++ finalDummyPushes ++ [[], finalNonce]).map
      Op.push := by decide

/-- The complete generated second-round data block reconstructs the nonce,
zero, dummy pool and commitment pool above any preceding stack. No capacity
or opcode-budget premise is needed because successful execution supplies it. -/
theorem accepted_final_round_init_shape (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes finalRoundAllOps
      (State.mk stack outcomes cost) = some final) :
    final = State.mk (finalNonce :: [] ::
      finalDummyPool ++ finalCommitmentPool ++ stack) outcomes cost := by
  rw [generated_final_round_all_pushes] at accepted
  have shape := accepted_pushes_shape hashes
    (finalCommitmentPushes ++ finalDummyPushes ++ [[], finalNonce])
    stack outcomes cost final accepted
  simpa [finalDummyPool, finalCommitmentPool, List.reverse_append,
    List.append_assoc] using shape

def fixedIndexPair : List Op := ByteLayout.program.drop 749 |>.take 2

theorem generated_fixed_index_pair : fixedIndexPair =
    [.push [0x4a, 0x02], .roll] := by decide

theorem fixed_index_decodes :
    ByteIndex.parseScriptNum [0x4a, 0x02] = some 586 := by decide

theorem base_region_prefix_length (prior : Bytes) :
    (finalNonce :: [] ::
      (finalDummyPool ++ finalCommitmentPool ++ [prior])).length = 303 := by
  simp [generated_dummy_pool_length, generated_commitment_pool_length]

/-- The generated fixed 586-roll fetches a byte from the arbitrary earlier
tail at offset 283 while retaining the complete generated data block and the
prior round's Boolean result. -/
theorem fixed_index_roll_source (prior : Bytes) (tail : List Bytes)
    (enough : 283 < tail.length) :
    KeyRolls.rollAt 586 (baseRegion prior tail) =
      some (tail[283] :: baseRegion prior (tail.eraseIdx 283)) := by
  have moved := PoolRollInvariant.roll_from_middle
    (finalNonce :: [] ::
      (finalDummyPool ++ finalCommitmentPool ++ [prior]))
    tail [] 283 enough
  simpa [baseRegion, base_region_prefix_length,
    List.append_assoc] using moved

theorem fixed_index_roll_requires_tail (prior : Bytes) (tail rolled : List Bytes)
    (success : KeyRolls.rollAt 586 (baseRegion prior tail) = some rolled) :
    283 < tail.length := by
  have available : (baseRegion prior tail)[586]?.isSome := by
    unfold KeyRolls.rollAt at success
    cases selected : (baseRegion prior tail)[586]? with
    | none => simp [selected] at success
    | some x => simp
  have frontLen := base_region_prefix_length prior
  have selected : (baseRegion prior tail)[586]? = tail[283]? := by
    change ((finalNonce :: [] ::
      (finalDummyPool ++ finalCommitmentPool ++ [prior])) ++ tail)[586]? =
      tail[283]?
    rw [List.getElem?_append_right (by rw [frontLen]; omega)]
    have index : 586 -
        (finalNonce :: [] ::
          (finalDummyPool ++ finalCommitmentPool ++ [prior])).length =
          283 := by rw [frontLen]
    rw [index]
  rw [selected] at available
  by_contra short
  have beyond : tail.length ≤ 283 := by omega
  rw [List.getElem?_eq_none beyond] at available
  simp at available

/-- Invert a successful generated fixed-roll pair, with no canonical raw
index encoding or assumption about the preceding witness tail. -/
theorem accepted_fixed_index_shape (hashes : Hashes)
    (prior : Bytes) (tail : List Bytes) (outcomes : List Bool)
    (cost : Nat) (final : State)
    (accepted : run hashes fixedIndexPair
      (State.mk (baseRegion prior tail) outcomes cost) = some final) :
    ∃ raw : Bytes,
      final = State.mk
        (raw :: baseRegion prior (tail.eraseIdx 283))
        outcomes (cost + 1) := by
  rw [generated_fixed_index_pair] at accepted
  obtain ⟨afterPush, pushed, _, afterRoll⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push [0x4a, 0x02])
      [.roll] (State.mk (baseRegion prior tail) outcomes cost)
      final accepted
  have pushShape := ByteFinalCounts.push_success_shape hashes
    [0x4a, 0x02] (baseRegion prior tail) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨afterStep, rollStep, _, finished⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll []
      (State.mk ([0x4a, 0x02] :: baseRegion prior tail)
        outcomes cost) final afterRoll
  have budget := ByteFinalCounts.roll_success_budget hashes [0x4a, 0x02]
    (baseRegion prior tail) outcomes cost afterStep rollStep
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes [0x4a, 0x02]
    586 (baseRegion prior tail) outcomes cost fixed_index_decodes budget]
    at rollStep
  cases rolled : KeyRolls.rollAt 586 (baseRegion prior tail) with
  | none => simp [rolled] at rollStep
  | some nextStack =>
      have enough := fixed_index_roll_requires_tail prior tail nextStack rolled
      have source := fixed_index_roll_source prior tail enough
      have stackEq : nextStack =
          tail[283] :: baseRegion prior (tail.eraseIdx 283) :=
        Option.some.inj (rolled.symm.trans source)
      subst nextStack
      simp [source] at rollStep
      cases rollStep
      simp [run] at finished
      cases finished
      exact ⟨tail[283], rfl⟩

/-- Reaching the generated cap/dup/add prefix with a parsed raw value at
least 152 fixes both retained and offset bytes, without a canonical raw
encoding or an assumption about the lower stack. -/
theorem oversized_cap_add_shape (hashes : Hashes)
    (raw prior : Bytes) (tail : List Bytes) (value : Int)
    (outcomes : List Bool) (cost : Nat) (middle : State)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value)
    (accepted : run hashes capAddOps
      (State.mk (raw :: baseRegion prior tail) outcomes cost) = some middle) :
    middle = State.mk
      ([0x2f, 0x01] :: lookupRegion [0x98, 0x00] prior tail)
      outcomes (cost + 3) := by
  rw [generated_cap_add_ops] at accepted
  obtain ⟨afterPush, pushed, _, afterPushRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push [0x98, 0x00])
      [.min, .dup, .push [0x97, 0x00], .add]
      (State.mk (raw :: baseRegion prior tail) outcomes cost)
      middle accepted
  have pushShape := ByteFinalCounts.push_success_shape hashes
    [0x98, 0x00] (raw :: baseRegion prior tail) outcomes cost
    afterPush pushed
  subst afterPush
  obtain ⟨afterMin, minStep, _, afterMinRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .min
      [.dup, .push [0x97, 0x00], .add]
      (State.mk ([0x98, 0x00] :: raw :: baseRegion prior tail)
        outcomes cost) middle afterPushRun
  have minBudget : cost + 1 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 1 > 201 := by omega
    unfold step at minStep
    simp [tooHigh] at minStep
  have minExact := FirstOvershoot.oversized_index_min_step hashes
    raw value (baseRegion prior tail) outcomes cost parsed large minBudget
  rw [minExact] at minStep
  cases minStep
  obtain ⟨afterDup, dupStep, _, afterDupRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .dup
      [.push [0x97, 0x00], .add]
      (State.mk ([0x98, 0x00] :: baseRegion prior tail)
        outcomes (cost + 1)) middle afterMinRun
  have dupBudget : cost + 2 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 2 > 201 := by omega
    unfold step at dupStep
    simp [tooHigh] at dupStep
  have dupExact : step hashes .dup
      (State.mk ([0x98, 0x00] :: baseRegion prior tail)
        outcomes (cost + 1)) =
      some (State.mk ([0x98, 0x00] :: [0x98, 0x00] ::
        baseRegion prior tail) outcomes (cost + 2)) := by
    unfold step
    simp [show ¬cost + 2 > 201 by omega]
  rw [dupExact] at dupStep
  cases dupStep
  obtain ⟨afterGap, gapStep, _, afterGapRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push [0x97, 0x00])
      [.add]
      (State.mk ([0x98, 0x00] :: [0x98, 0x00] ::
        baseRegion prior tail) outcomes (cost + 2))
      middle afterDupRun
  have gapShape := ByteFinalCounts.push_success_shape hashes
    [0x97, 0x00]
    ([0x98, 0x00] :: [0x98, 0x00] :: baseRegion prior tail)
    outcomes (cost + 2) afterGap gapStep
  subst afterGap
  obtain ⟨afterAdd, addStep, _, finished⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .add []
      (State.mk ([0x97, 0x00] :: [0x98, 0x00] :: [0x98, 0x00] ::
        baseRegion prior tail) outcomes (cost + 2))
      middle afterGapRun
  have addBudget : cost + 3 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 3 > 201 := by omega
    unfold step at addStep
    simp [tooHigh] at addStep
  have addExact : step hashes .add
      (State.mk ([0x97, 0x00] :: [0x98, 0x00] :: [0x98, 0x00] ::
        baseRegion prior tail) outcomes (cost + 2)) =
      some (State.mk ([0x2f, 0x01] :: [0x98, 0x00] ::
        baseRegion prior tail) outcomes (cost + 3)) := by
    unfold step
    simp [show ¬cost + 3 > 201 by omega,
      FirstOvershoot.parse_151, ByteIndex.positive_152,
      FirstOvershoot.encode_303]
  rw [addExact] at addStep
  cases addStep
  simp [run] at finished
  cases finished
  rfl

/-- A parsed nonnegative value below the cap is canonicalized by MIN and
shifted to its exact signed-roll offset by ADD, regardless of the raw
ScriptNum encoding or the preceding stack. -/
theorem inrange_cap_add_shape (hashes : Hashes)
    (raw prior : Bytes) (tail : List Bytes) (n : Fin 152)
    (outcomes : List Bool) (cost : Nat) (middle : State)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n.val))
    (accepted : run hashes capAddOps
      (State.mk (raw :: baseRegion prior tail) outcomes cost) = some middle) :
    middle = State.mk
      (FirstNumericRange.signedOffset n ::
        lookupRegion (FirstNumericRange.canonicalIndex n) prior tail)
      outcomes (cost + 3) := by
  rw [generated_cap_add_ops] at accepted
  obtain ⟨afterPush, pushed, _, afterPushRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push [0x98, 0x00])
      [.min, .dup, .push [0x97, 0x00], .add]
      (State.mk (raw :: baseRegion prior tail) outcomes cost)
      middle accepted
  have pushShape := ByteFinalCounts.push_success_shape hashes
    [0x98, 0x00] (raw :: baseRegion prior tail) outcomes cost
    afterPush pushed
  subst afterPush
  obtain ⟨afterMin, minStep, _, afterMinRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .min
      [.dup, .push [0x97, 0x00], .add]
      (State.mk ([0x98, 0x00] :: raw :: baseRegion prior tail)
        outcomes cost) middle afterPushRun
  have minBudget : cost + 1 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 1 > 201 := by omega
    unfold step at minStep
    simp [tooHigh] at minStep
  have minExact := FirstNumericRange.inrange_index_min_step hashes
    raw n (baseRegion prior tail) outcomes cost parsed minBudget
  rw [minExact] at minStep
  cases minStep
  obtain ⟨afterDup, dupStep, _, afterDupRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .dup
      [.push [0x97, 0x00], .add]
      (State.mk (FirstNumericRange.canonicalIndex n ::
        baseRegion prior tail) outcomes (cost + 1)) middle afterMinRun
  have dupBudget : cost + 2 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 2 > 201 := by omega
    unfold step at dupStep
    simp [tooHigh] at dupStep
  have dupExact : step hashes .dup
      (State.mk (FirstNumericRange.canonicalIndex n ::
        baseRegion prior tail) outcomes (cost + 1)) =
      some (State.mk (FirstNumericRange.canonicalIndex n ::
        FirstNumericRange.canonicalIndex n :: baseRegion prior tail)
        outcomes (cost + 2)) := by
    unfold step
    simp [show ¬cost + 2 > 201 by omega]
  rw [dupExact] at dupStep
  cases dupStep
  obtain ⟨afterGap, gapStep, _, afterGapRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push [0x97, 0x00])
      [.add]
      (State.mk (FirstNumericRange.canonicalIndex n ::
        FirstNumericRange.canonicalIndex n :: baseRegion prior tail)
        outcomes (cost + 2)) middle afterDupRun
  have gapShape := ByteFinalCounts.push_success_shape hashes
    [0x97, 0x00]
    (FirstNumericRange.canonicalIndex n ::
      FirstNumericRange.canonicalIndex n :: baseRegion prior tail)
    outcomes (cost + 2) afterGap gapStep
  subst afterGap
  obtain ⟨afterAdd, addStep, _, finished⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .add []
      (State.mk ([0x97, 0x00] :: FirstNumericRange.canonicalIndex n ::
        FirstNumericRange.canonicalIndex n :: baseRegion prior tail)
        outcomes (cost + 2)) middle afterGapRun
  have addBudget : cost + 3 ≤ 201 := by
    by_contra exceeded
    have tooHigh : cost + 3 > 201 := by omega
    unfold step at addStep
    simp [tooHigh] at addStep
  have addExact := FirstNumericRange.inrange_index_add_step hashes n
    (FirstNumericRange.canonicalIndex n :: baseRegion prior tail)
    outcomes (cost + 2) addBudget
  rw [addExact] at addStep
  cases addStep
  simp [run] at finished
  cases finished
  rfl

theorem accepted_cap_add_parses_raw (hashes : Hashes)
    (raw : Bytes) (region : List Bytes) (outcomes : List Bool)
    (cost : Nat) (final : State)
    (accepted : run hashes capAddOps
      (State.mk (raw :: region) outcomes cost) = some final) :
    ∃ value : Int, ByteIndex.parseScriptNum raw = some value := by
  rw [generated_cap_add_ops] at accepted
  obtain ⟨afterPush, pushed, _, afterPushRun⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes (.push [0x98, 0x00])
      [.min, .dup, .push [0x97, 0x00], .add]
      (State.mk (raw :: region) outcomes cost) final accepted
  have pushShape := ByteFinalCounts.push_success_shape hashes
    [0x98, 0x00] (raw :: region) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨afterMin, minStep, _, _⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .min
      [.dup, .push [0x97, 0x00], .add]
      (State.mk ([0x98, 0x00] :: raw :: region) outcomes cost)
      final afterPushRun
  unfold step at minStep
  by_cases budget : cost + 1 > 201
  · simp [budget] at minStep
  · simp [budget, ByteIndex.positive_152] at minStep
    cases parsed : ByteIndex.parseScriptNum raw with
    | none => simp [parsed] at minStep
    | some value => exact ⟨value, rfl⟩

/-- The generated first comparison rejects every raw ScriptNum value at
least 152 from the stated post-fixed-roll stack, including nonminimal raw
encodings. -/
theorem oversized_first_comparison_rejected (hashes : Hashes)
    (raw : Bytes) (tail : List Bytes) (result : Bool)
    (value : Int) (outcomes : List Bool) (cost : Nat) (final : State)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value)
    (accepted : run hashes firstComparisonOps
      (State.mk (raw :: baseRegion (ByteMachine.boolBytes result) tail)
        outcomes cost) = some final) : False := by
  rw [generated_first_comparison_ops, run_append] at accepted
  cases first : run hashes capAddOps
      (State.mk (raw :: baseRegion (ByteMachine.boolBytes result) tail)
        outcomes cost) with
  | none => simp [first] at accepted
  | some middle =>
      have shape := oversized_cap_add_shape hashes raw
        (ByteMachine.boolBytes result) tail value outcomes cost middle
        parsed large first
      subst middle
      simp only [first, Option.bind_some] at accepted
      exact capped_first_signed_comparison_rejects hashes
        [0x98, 0x00] tail result outcomes (cost + 3) final accepted

/-- A raw nonnegative first final-round index of 0 or 1 cannot survive the
generated comparison, even when its ScriptNum encoding is nonminimal. -/
theorem inrange_low_first_comparison_rejected (hashes : Hashes)
    (raw : Bytes) (tail : List Bytes) (result : Bool)
    (n : Fin 152) (low : n.val < 2)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n.val))
    (accepted : run hashes firstComparisonOps
      (State.mk (raw :: baseRegion (ByteMachine.boolBytes result) tail)
        outcomes cost) = some final) : False := by
  rw [generated_first_comparison_ops, run_append] at accepted
  cases first : run hashes capAddOps
      (State.mk (raw :: baseRegion (ByteMachine.boolBytes result) tail)
        outcomes cost) with
  | none => simp [first] at accepted
  | some middle =>
      have shape := inrange_cap_add_shape hashes raw
        (ByteMachine.boolBytes result) tail n outcomes cost middle
        parsed first
      subst middle
      simp only [first, Option.bind_some] at accepted
      exact low_first_signed_comparison_rejects hashes
        (FirstNumericRange.signedOffset n)
        (FirstNumericRange.canonicalIndex n)
        (ByteMachine.boolBytes result) tail outcomes (cost + 3) final
        n.val low (FirstNumericRange.parse_signed_offset n) accepted

def firstFinalRoundPrefix : List Op :=
  ByteLayout.program.drop 447 |>.take 314

theorem generated_first_final_round_prefix : firstFinalRoundPrefix =
    finalRoundAllOps ++ fixedIndexPair ++ firstComparisonOps := by decide

/-- In the byte interpreter, every successful first final-round signed
comparison starting after the prior CHECKMULTISIG Boolean has a parseable
raw index strictly below 152, excluding nonnegative values 0 and 1. This
covers arbitrary earlier stack tails, hash functions, and nonminimal
ScriptNum encodings; negative values and later selections remain open. -/
theorem accepted_first_final_signed_below_cap (hashes : Hashes)
    (result : Bool) (tail : List Bytes) (outcomes : List Bool)
    (cost : Nat) (final : State)
    (accepted : run hashes firstFinalRoundPrefix
      (State.mk (ByteMachine.boolBytes result :: tail) outcomes cost) =
        some final) :
    ∃ raw : Bytes, ∃ value : Int,
      ByteIndex.parseScriptNum raw = some value ∧ value < 152 ∧
      (value < 0 ∨ 2 ≤ value) := by
  rw [generated_first_final_round_prefix, List.append_assoc,
    run_append] at accepted
  cases init : run hashes finalRoundAllOps
      (State.mk (ByteMachine.boolBytes result :: tail) outcomes cost) with
  | none => simp [init] at accepted
  | some initialized =>
      have initShape := accepted_final_round_init_shape hashes
        (ByteMachine.boolBytes result :: tail) outcomes cost initialized init
      subst initialized
      simp only [init, Option.bind_some] at accepted
      change run hashes (fixedIndexPair ++ firstComparisonOps)
        (State.mk (baseRegion (ByteMachine.boolBytes result) tail)
          outcomes cost) = some final at accepted
      rw [run_append] at accepted
      cases fixed : run hashes fixedIndexPair
          (State.mk (baseRegion (ByteMachine.boolBytes result) tail)
            outcomes cost) with
      | none => simp [fixed] at accepted
      | some afterFixed =>
          obtain ⟨raw, fixedShape⟩ := accepted_fixed_index_shape hashes
            (ByteMachine.boolBytes result) tail outcomes cost afterFixed fixed
          subst afterFixed
          simp only [fixed, Option.bind_some] at accepted
          rw [generated_first_comparison_ops, run_append] at accepted
          cases cap : run hashes capAddOps
              (State.mk (raw :: baseRegion (ByteMachine.boolBytes result)
                (tail.eraseIdx 283)) outcomes (cost + 1)) with
          | none => simp [cap] at accepted
          | some middle =>
              obtain ⟨value, parsed⟩ := accepted_cap_add_parses_raw hashes
                raw (baseRegion (ByteMachine.boolBytes result)
                  (tail.eraseIdx 283)) outcomes (cost + 1) middle cap
              have below : value < 152 := by
                by_contra notBelow
                have large : 152 ≤ value := by omega
                have complete : run hashes firstComparisonOps
                    (State.mk (raw :: baseRegion
                      (ByteMachine.boolBytes result) (tail.eraseIdx 283))
                      outcomes (cost + 1)) = some final := by
                  rw [generated_first_comparison_ops, run_append]
                  simpa [cap] using accepted
                exact oversized_first_comparison_rejected hashes raw
                  (tail.eraseIdx 283) result value outcomes (cost + 1)
                  final parsed large complete
              have notLow : value < 0 ∨ 2 ≤ value := by
                by_contra neither
                have zeroOrOne : value = 0 ∨ value = 1 := by omega
                have complete : run hashes firstComparisonOps
                    (State.mk (raw :: baseRegion
                      (ByteMachine.boolBytes result) (tail.eraseIdx 283))
                      outcomes (cost + 1)) = some final := by
                  rw [generated_first_comparison_ops, run_append]
                  simpa [cap] using accepted
                rcases zeroOrOne with zero | one
                · exact inrange_low_first_comparison_rejected hashes raw
                    (tail.eraseIdx 283) result ⟨0, by decide⟩
                    (by decide) outcomes (cost + 1) final
                    (by simpa [zero] using parsed) complete
                · exact inrange_low_first_comparison_rejected hashes raw
                    (tail.eraseIdx 283) result ⟨1, by decide⟩
                    (by decide) outcomes (cost + 1) final
                    (by simpa [one] using parsed) complete
              exact ⟨raw, value, parsed, below, notLow⟩

theorem successful_checkmultisig_result_shape (hashes : Hashes)
    (before after : State)
    (success : step hashes .checkmultisig before = some after) :
    ∃ result : Bool, ∃ tail : List Bytes,
      after.stack = ByteMachine.boolBytes result :: tail := by
  cases before with
  | mk stack outcomes cost =>
    cases stack with
    | nil =>
      change (if cost + 1 > 201 then none else none) = some after at success
      simp at success
    | cons rawN xs =>
      unfold step at success
      dsimp only at success
      change (if cost + 1 > 201 then none else do
        let n ← ByteIndex.parseScriptNum rawN
        if n < 0 ∨ n > 20 ∨ cost + 1 + n.toNat > 201 then none else do
          let rawM ← xs[n.toNat]?
          let m ← ByteIndex.parseScriptNum rawM
          if m < 0 ∨ m > n then none else do
            let dummy ← xs[n.toNat + 1 + m.toNat]?
            if !dummy.isEmpty then none else
              match outcomes with
              | b :: rest => some (State.mk
                  (ByteMachine.boolBytes b :: xs.drop (n.toNat + m.toNat + 2))
                  rest (cost + 1 + n.toNat))
              | _ => none) = some after at success
      by_cases budget : cost + 1 > 201
      · simp [budget] at success
      · simp only [if_neg budget] at success
        cases parsedN : ByteIndex.parseScriptNum rawN with
        | none => simp [parsedN] at success
        | some n =>
            by_cases invalidN : n < 0 ∨ n > 20 ∨ cost + 1 + n.toNat > 201
            · simp [parsedN, invalidN] at success
            · simp [parsedN, invalidN] at success
              cases rawM : xs[n.toNat]? with
              | none => simp [rawM] at success
              | some mbytes =>
                  simp only [rawM, Option.bind_some] at success
                  cases parsedM : ByteIndex.parseScriptNum mbytes with
                  | none => simp [parsedM] at success
                  | some m =>
                      simp only [parsedM, Option.bind_some] at success
                      by_cases invalidM : m < 0 ∨ m > n
                      · simp [invalidM] at success
                      · simp only [if_neg invalidM] at success
                        cases dummy : xs[n.toNat + 1 + m.toNat]? with
                        | none => simp [dummy] at success
                        | some value =>
                            simp [dummy] at success
                            by_cases empty : value = []
                            · simp [empty] at success
                              cases outcomes with
                              | nil => simp at success
                              | cons b rest =>
                                  simp at success
                                  cases success
                                  exact ⟨b, xs.drop (n.toNat + m.toNat + 2), rfl⟩
                            · simp [empty] at success

theorem generated_first_round_check_boundary :
    ByteLayout.program =
      ByteLayout.program.take 446 ++
        (.checkmultisig ::
          (firstFinalRoundPrefix ++ ByteLayout.program.drop 761)) := by
  decide

/-- Every successful execution of the whole generated *byte model*, from
any initial byte stack and any supplied signature outcomes, forces the first
final-round signed index to parse below 152 and exclude 0 and 1. The proof derives the prior
round's Boolean result from the preceding CHECKMULTISIG, reconstructs all
302 second-round pushes, fetches the index through the fixed 586-roll, and
uses the exact generated comparison. Core refinement and the later six
signed selections remain open. -/
theorem accepted_whole_program_first_final_index_below_cap (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final) :
    ∃ raw : Bytes, ∃ value : Int,
      ByteIndex.parseScriptNum raw = some value ∧ value < 152 ∧
      (value < 0 ∨ 2 ≤ value) := by
  rw [generated_first_round_check_boundary, run_append] at accepted
  cases first : run hashes (ByteLayout.program.take 446) initial with
  | none => simp [first] at accepted
  | some beforeCheck =>
      simp only [first, Option.bind_some] at accepted
      obtain ⟨afterCheck, checkStep, _, suffix⟩ :=
        FirstAcceptedOrigin.run_cons_success hashes .checkmultisig
          (firstFinalRoundPrefix ++ ByteLayout.program.drop 761)
          beforeCheck final accepted
      obtain ⟨result, tail, shape⟩ :=
        successful_checkmultisig_result_shape hashes beforeCheck afterCheck
          checkStep
      cases afterCheck with
      | mk checkStack checkOutcomes checkCost =>
          change checkStack = ByteMachine.boolBytes result :: tail at shape
          subst checkStack
          rw [run_append] at suffix
          cases selected : run hashes firstFinalRoundPrefix
              (State.mk (ByteMachine.boolBytes result :: tail)
                checkOutcomes checkCost) with
          | none => simp [selected] at suffix
          | some middle =>
              exact accepted_first_final_signed_below_cap hashes result
                tail checkOutcomes checkCost middle selected

end QSB.FinalSignedAccepted
