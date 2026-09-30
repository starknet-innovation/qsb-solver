import QSB.FinalSignedChain
import QSB.ByteBonusBetween

/-!
Carry the seven-signed pool invariant through the exact generated bonus
prefix and connect it to the arbitrary-stack NULLDUMMY source theorem.
-/
namespace QSB.FinalBonusAccepted
open ByteMachine
open FinalSignedLoop
open FinalSignedChain
open PoolRollInvariant
open FirstAcceptedOrigin
open ByteFinalCounts
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def firstBonusPrelude : List Op :=
  (ByteLayout.program.drop 840).take 4

theorem generated_first_bonus_prelude : firstBonusPrelude =
    [.push [0x43, 0x02], .roll, .push [0x98, 0x00], .min] := by decide

theorem generated_bonus_suffix :
    ByteLayout.program.drop 840 =
      firstBonusPrelude ++
        ([.roll] ++ (ByteBonusBetween.betweenOps ++
          ([.roll] ++ ByteLayout.program.drop 850))) := by decide

/-- The generated fixed 579-roll before the first bonus fetches a raw index
from earlier tail cell 283 after all seven signed draws. -/
theorem accepted_first_bonus_fixed_raw_pair_shape (hashes : Hashes)
    (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push [0x43, 0x02], .roll]
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) = some after) :
    ∃ enough : 283 < tail.length,
      after = State.mk
        (tail[283] :: nextRawFront prior gathered dummies commitments ++
          tail.eraseIdx 283) outcomes (cost + 1) := by
  have frontLength := next_raw_front_length prior gathered dummies
    commitments shape
  have depthNat :
      (nextRawFront prior gathered dummies commitments).length + 283 =
        579 := by
    rw [frontLength, seven]
  have parsed : ByteIndex.parseScriptNum [0x43, 0x02] =
      some (Int.ofNat
        ((nextRawFront prior gathered dummies commitments).length + 283)) := by
    simpa only [depthNat] using
      ByteBonusBetween.between_roll_index_decode
  exact accepted_push_roll_tail_shape hashes [0x43, 0x02]
    (nextRawFront prior gathered dummies commitments) tail
    outcomes cost after 283 parsed accepted

/-- With seven signed dummies gathered, the first bonus's reachable depth
range splits exactly into unused dummy cells 9–151 and the first surviving
HORS commitment at depth 152. The arbitrary earlier tail is unreachable. -/
theorem first_bonus_source_map (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (n : Nat) (lower : 9 ≤ n) (upper : n ≤ 152) :
    (nextRawFront prior gathered dummies commitments ++ tail)[n]? =
      if n < 152 then dummies[n - 9]?
      else commitments[0]? := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have commitmentLength : commitments.length = 143 := by
    rw [shape.commitmentCount, dummyLength]
  have frontLength : (gathered ++ [finalNonce, []]).length = 9 := by
    simp [seven]
  have layout : nextRawFront prior gathered dummies commitments ++ tail =
      (gathered ++ [finalNonce, []]) ++
        (dummies ++ (commitments ++ (prior :: tail))) := by
    simp [nextRawFront, List.append_assoc]
  rw [layout, List.getElem?_append_right (by omega)]
  have offset : n - (gathered ++ [finalNonce, []]).length = n - 9 := by
    rw [frontLength]
  rw [offset]
  by_cases isDummy : n < 152
  · rw [if_pos isDummy, List.getElem?_append_left (by omega)]
  · have capped : n = 152 := by omega
    subst n
    rw [if_neg (by omega)]
    rw [List.getElem?_append_right (by omega)]
    simp [dummyLength]
    rw [List.getElem_append_left (by omega)]
    exact (List.getElem?_eq_getElem (by omega : 0 < commitments.length)).symm

/-- The first bonus's in-range source has generated dummy width below the
commitment boundary and HASH160 commitment width exactly at that boundary. -/
theorem first_bonus_source_width (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (n : Nat) (lower : 9 ≤ n) (upper : n ≤ 152)
    (selected : Bytes)
    (atSource :
      (nextRawFront prior gathered dummies commitments ++ tail)[n]? =
        some selected) :
    if n < 152 then selected.length = 9 else selected.length = 20 := by
  have mapped := first_bonus_source_map prior gathered dummies
    commitments tail shape seven n lower upper
  rw [atSource] at mapped
  by_cases dummy : n < 152
  · rw [if_pos dummy] at mapped ⊢
    have within : n - 9 < dummies.length := by
      have total := shape.poolCount
      omega
    rw [List.getElem?_eq_getElem within] at mapped
    have same : selected = dummies[n - 9] := by
      exact Option.some.inj mapped
    rw [same]
    exact shape.dummyWidth _ (List.getElem_mem within)
  · rw [if_neg dummy] at mapped ⊢
    have within : 0 < commitments.length := by
      rw [shape.commitmentCount]
      have total := shape.poolCount
      omega
    rw [List.getElem?_eq_getElem within] at mapped
    have same : selected = commitments[0] := by
      exact Option.some.inj mapped
    rw [same]
    exact shape.commitmentWidth _ (List.getElem_mem within)

/-- A successful generated cap pair replaces only the raw top index. -/
theorem accepted_cap_pair_stack (hashes : Hashes)
    (raw : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push [0x98, 0x00], .min]
      (State.mk (raw :: tail) outcomes cost) = some after) :
    ∃ retained : Bytes, after.stack = retained :: tail := by
  obtain ⟨afterPush, pushed, _, afterMin⟩ :=
    run_cons_success hashes (.push [0x98, 0x00]) [.min]
      (State.mk (raw :: tail) outcomes cost) after accepted
  have pushShape := push_success_shape hashes [0x98, 0x00]
    (raw :: tail) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨next, minStep, _, finished⟩ :=
    run_cons_success hashes .min []
      (State.mk ([0x98, 0x00] :: raw :: tail) outcomes cost)
      after afterMin
  obtain ⟨retained, shape⟩ :=
    ByteBonusBetween.successful_cap_min_tail hashes raw tail outcomes
      cost next minStep
  simp [run] at finished
  cases finished
  exact ⟨retained, shape⟩

/-- The exact first bonus prelude removes only its earlier-tail raw index
before leaving the capped index above the unchanged generated pools. -/
theorem accepted_first_bonus_prelude_exact (hashes : Hashes)
    (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes firstBonusPrelude
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) = some after) :
    ∃ retained : Bytes,
      after.stack = retained ::
        (nextRawFront prior gathered dummies commitments ++
          tail.eraseIdx 283) := by
  rw [generated_first_bonus_prelude] at accepted
  have split : ([.push [0x43, 0x02], .roll,
      .push [0x98, 0x00], .min] : List Op) =
      [.push [0x43, 0x02], .roll] ++
        [.push [0x98, 0x00], .min] := rfl
  rw [split, run_append] at accepted
  cases fixedRun : run hashes [.push [0x43, 0x02], .roll]
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) with
  | none => simp [fixedRun] at accepted
  | some afterFixed =>
      obtain ⟨enough, fixedShape⟩ :=
        accepted_first_bonus_fixed_raw_pair_shape hashes prior gathered
          dummies commitments tail shape seven outcomes cost afterFixed
          fixedRun
      simp only [fixedRun, Option.bind_some] at accepted
      rw [fixedShape] at accepted
      exact accepted_cap_pair_stack hashes tail[283]
        (nextRawFront prior gathered dummies commitments ++
          tail.eraseIdx 283) outcomes (cost + 1) after accepted

/-- Successful bonus OP_MIN records the actual parsed raw value and the
ScriptNum encoding of its cap, including nonminimal raw encodings. -/
theorem accepted_cap_pair_encoding (hashes : Hashes)
    (raw : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push [0x98, 0x00], .min]
      (State.mk (raw :: tail) outcomes cost) = some after) :
    ∃ (value : Int) (retained : Bytes),
      ByteIndex.parseScriptNum raw = some value ∧
      ByteIndex.encodeScriptNum (min 152 value) = some retained ∧
      after.stack = retained :: tail := by
  obtain ⟨afterPush, pushed, _, afterMin⟩ :=
    run_cons_success hashes (.push [0x98, 0x00]) [.min]
      (State.mk (raw :: tail) outcomes cost) after accepted
  have pushShape := push_success_shape hashes [0x98, 0x00]
    (raw :: tail) outcomes cost afterPush pushed
  subst afterPush
  obtain ⟨next, minStep, _, finished⟩ :=
    run_cons_success hashes .min []
      (State.mk ([0x98, 0x00] :: raw :: tail) outcomes cost)
      after afterMin
  change (if cost + 1 > 201 then none else do
    let cap ← ByteIndex.parseScriptNum [0x98, 0x00]
    let value ← ByteIndex.parseScriptNum raw
    let retained ← ByteIndex.encodeScriptNum (min cap value)
    some (State.mk (retained :: tail) outcomes (cost + 1))) =
      some next at minStep
  by_cases budget : cost + 1 > 201
  · simp [budget] at minStep
  · simp [budget, ByteIndex.positive_152] at minStep
    cases parsed : ByteIndex.parseScriptNum raw with
    | none => simp [parsed] at minStep
    | some value =>
        simp only [parsed, Option.bind_some] at minStep
        cases encoded : ByteIndex.encodeScriptNum (min 152 value) with
        | none => simp [encoded] at minStep
        | some retained =>
            simp only [encoded, Option.bind_some, Option.some.injEq] at minStep
            subst next
            simp [run] at finished
            cases finished
            exact ⟨value, retained, rfl, encoded, rfl⟩

/-- A successfully parsed bonus roll depth after OP_MIN cannot exceed 152. -/
theorem accepted_bonus_cap_index_le_152 (hashes : Hashes)
    (raw retained : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push [0x98, 0x00], .min]
      (State.mk (raw :: tail) outcomes cost) = some after)
    (shape : after.stack = retained :: tail)
    (n : Nat)
    (parsed : ByteIndex.parseScriptNum retained = some (Int.ofNat n)) :
    n ≤ 152 := by
  obtain ⟨value, actual, _, encoded, actualShape⟩ :=
    accepted_cap_pair_encoding hashes raw tail outcomes cost after accepted
  have same : actual = retained := by
    injection actualShape.symm.trans shape with same _
  subst actual
  have capBound : min 152 value ≤ (152 : Int) := min_le_left _ _
  have result := encoded_reparse_preserves_upper_bound
    (min 152 value) (Int.ofNat n) 152 retained capBound
    (by omega) (by omega) encoded parsed
  exact Int.ofNat_le.mp (by simpa using result)

/-- Successful modeled OP_ROLL requires a parsed nonnegative ScriptNum,
without assuming a minimal encoding. -/
theorem accepted_roll_index (hashes : Hashes)
    (raw : Bytes) (region : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.roll]
      (State.mk (raw :: region) outcomes cost) = some after) :
    ∃ n : Nat, ByteIndex.parseScriptNum raw = some (Int.ofNat n) := by
  obtain ⟨next, rollStep, _, _⟩ :=
    run_cons_success hashes .roll []
      (State.mk (raw :: region) outcomes cost) after accepted
  change (if cost + 1 > 201 then none else do
    let n ← ByteIndex.parseScriptNum raw
    if n < 0 then none else do
      let x ← region[n.toNat]?
      some (State.mk (x :: region.eraseIdx n.toNat)
        outcomes (cost + 1))) = some next at rollStep
  by_cases budget : cost + 1 > 201
  · simp [budget] at rollStep
  · simp only [if_neg budget] at rollStep
    cases parsed : ByteIndex.parseScriptNum raw with
    | none => simp [parsed] at rollStep
    | some value =>
        by_cases negative : value < 0
        · simp [parsed, negative] at rollStep
        · refine ⟨value.toNat, ?_⟩
          simp [Int.toNat_of_nonneg (by omega : 0 ≤ value)]

/-- A successful modeled roll puts the actual selected source byte on top. -/
theorem accepted_roll_selected_source (hashes : Hashes)
    (raw : Bytes) (region : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (n : Nat)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n))
    (accepted : run hashes [.roll]
      (State.mk (raw :: region) outcomes cost) = some after) :
    ∃ selected : Bytes,
      region[n]? = some selected ∧
      after.stack = selected :: region.eraseIdx n := by
  obtain ⟨next, rollStep, _, finished⟩ :=
    run_cons_success hashes .roll []
      (State.mk (raw :: region) outcomes cost) after accepted
  have budget := roll_success_budget hashes raw region outcomes cost
    next rollStep
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes raw n region
    outcomes cost parsed budget] at rollStep
  cases cell : region[n]? with
  | none =>
      have absent : KeyRolls.rollAt n region = none := by
        simp [KeyRolls.rollAt, cell]
      simp [absent] at rollStep
  | some selected =>
      have moved : KeyRolls.rollAt n region =
          some (selected :: region.eraseIdx n) := by
        simp [KeyRolls.rollAt, cell]
      rw [moved] at rollStep
      simp at rollStep
      cases rollStep
      simp [run] at finished
      cases finished
      exact ⟨selected, rfl, rfl⟩

/-- At the reached first bonus roll, every bounded decoded choice either
selects an unused generated dummy (depth 9–151) or the first surviving HORS
commitment (depth 152). The post-roll top cell is the actual selected byte. -/
theorem accepted_first_bonus_source_role (hashes : Hashes)
    (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat)
    (beforeFirst postFirst : State)
    (prelude : run hashes firstBonusPrelude
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) = some beforeFirst)
    (rawFirst : Bytes) (regionFirst : List Bytes)
    (firstShape : beforeFirst.stack = rawFirst :: regionFirst)
    (n : Nat) (lower : 9 ≤ n) (upper : n ≤ 152)
    (parsed : ByteIndex.parseScriptNum rawFirst = some (Int.ofNat n))
    (firstRoll : run hashes [.roll] beforeFirst = some postFirst) :
    postFirst.stack.head? =
      if n < 152 then dummies[n - 9]?
      else commitments[0]? := by
  obtain ⟨retained, exactShape⟩ :=
    accepted_first_bonus_prelude_exact hashes prior gathered dummies
      commitments tail shape seven outcomes cost beforeFirst prelude
  have same : rawFirst :: regionFirst =
      retained ::
        (nextRawFront prior gathered dummies commitments ++
          tail.eraseIdx 283) := firstShape.symm.trans exactShape
  have rawEq : rawFirst = retained := by
    injection same with h _
  have regionEq : regionFirst =
      nextRawFront prior gathered dummies commitments ++
        tail.eraseIdx 283 := by
    injection same with _ h
  cases beforeFirst with
  | mk firstStack firstOutcomes firstCost =>
      change firstStack = rawFirst :: regionFirst at firstShape
      subst firstStack
      obtain ⟨selected, source, postShape⟩ :=
        accepted_roll_selected_source hashes rawFirst regionFirst
          firstOutcomes firstCost postFirst n parsed firstRoll
      rw [regionEq] at source
      have mapped := first_bonus_source_map prior gathered dummies
        commitments (tail.eraseIdx 283) shape seven n lower upper
      rw [source] at mapped
      rw [postShape]
      exact mapped

/-- The fixed deep roll and cap before the first bonus roll leave the two
post-signed shallow dummy-source cells at region depths nine and ten. -/
theorem accepted_first_bonus_prelude_sources (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (after : State) (nine ten : Bytes)
    (sourceNine : stack[9]? = some nine)
    (sourceTen : stack[10]? = some ten)
    (accepted : run hashes firstBonusPrelude
      (State.mk stack outcomes cost) = some after) :
    ∃ rawFirst : Bytes, ∃ regionFirst : List Bytes,
      after.stack = rawFirst :: regionFirst ∧
      regionFirst[9]? = some nine ∧
      regionFirst[10]? = some ten ∧
      (∀ n : Nat, ByteIndex.parseScriptNum rawFirst =
        some (Int.ofNat n) → n ≤ 152) := by
  rw [generated_first_bonus_prelude] at accepted
  have split : ([.push [0x43, 0x02], .roll,
      .push [0x98, 0x00], .min] : List Op) =
      [.push [0x43, 0x02], .roll] ++
        [.push [0x98, 0x00], .min] := rfl
  rw [split, run_append] at accepted
  cases fixedRun : run hashes [.push [0x43, 0x02], .roll]
      (State.mk stack outcomes cost) with
  | none => simp [fixedRun] at accepted
  | some afterFixed =>
      have keepNine := accepted_pair_preserves_shallower_option hashes
        [0x43, 0x02] 579 9 stack outcomes cost afterFixed
        ByteBonusBetween.between_roll_index_decode (by omega) fixedRun
      have keepTen := accepted_pair_preserves_shallower_option hashes
        [0x43, 0x02] 579 10 stack outcomes cost afterFixed
        ByteBonusBetween.between_roll_index_decode (by omega) fixedRun
      simp only [fixedRun, Option.bind_some] at accepted
      cases afterFixed with
      | mk fixedStack fixedOutcomes fixedCost =>
          cases fixedStack with
          | nil =>
              obtain ⟨afterPush, pushed, _, afterMin⟩ :=
                run_cons_success hashes (.push [0x98, 0x00]) [.min]
                  (State.mk [] fixedOutcomes fixedCost) after accepted
              have pushShape := push_success_shape hashes [0x98, 0x00]
                [] fixedOutcomes fixedCost afterPush pushed
              subst afterPush
              obtain ⟨next, minStep, _, _⟩ :=
                run_cons_success hashes .min []
                  (State.mk [[0x98, 0x00]] fixedOutcomes fixedCost)
                  after afterMin
              change (if fixedCost + 1 > 201 then none else none) =
                some next at minStep
              simp at minStep
          | cons raw region =>
              obtain ⟨retained, shape⟩ :=
                accepted_cap_pair_stack hashes raw region fixedOutcomes
                  fixedCost after accepted
              refine ⟨retained, region, shape, ?_, ?_, ?_⟩
              · simpa using keepNine.trans sourceNine
              · simpa using keepTen.trans sourceTen
              · intro n parsed
                exact accepted_bonus_cap_index_le_152 hashes raw retained
                  region fixedOutcomes fixedCost after accepted shape n parsed

/-- The fixed roll and cap between bonus choices likewise bound the second
decoded roll depth by 152, regardless of its raw ScriptNum encoding. -/
theorem accepted_between_cap_index_le_152 (hashes : Hashes)
    (before after : State) (retained : Bytes) (region : List Bytes)
    (accepted : run hashes ByteBonusBetween.betweenOps before = some after)
    (shape : after.stack = retained :: region)
    (n : Nat)
    (parsed : ByteIndex.parseScriptNum retained = some (Int.ofNat n)) :
    n ≤ 152 := by
  rw [ByteBonusBetween.generated_between_ops] at accepted
  have split : ([.push [0x43, 0x02], .roll,
      .push [0x98, 0x00], .min] : List Op) =
      [.push [0x43, 0x02], .roll] ++
        [.push [0x98, 0x00], .min] := rfl
  rw [split, run_append] at accepted
  cases fixedRun : run hashes [.push [0x43, 0x02], .roll]
      before with
  | none => simp [fixedRun] at accepted
  | some afterFixed =>
      simp only [fixedRun, Option.bind_some] at accepted
      cases afterFixed with
      | mk fixedStack fixedOutcomes fixedCost =>
          cases fixedStack with
          | nil =>
              obtain ⟨afterPush, pushed, _, afterMin⟩ :=
                run_cons_success hashes (.push [0x98, 0x00]) [.min]
                  (State.mk [] fixedOutcomes fixedCost) after accepted
              have pushShape := push_success_shape hashes [0x98, 0x00]
                [] fixedOutcomes fixedCost afterPush pushed
              subst afterPush
              obtain ⟨next, minStep, _, _⟩ :=
                run_cons_success hashes .min []
                  (State.mk [[0x98, 0x00]] fixedOutcomes fixedCost)
                  after afterMin
              change (if fixedCost + 1 > 201 then none else none) =
                some next at minStep
              simp at minStep
          | cons raw tail =>
              obtain ⟨actual, actualShape⟩ :=
                accepted_cap_pair_stack hashes raw tail fixedOutcomes
                  fixedCost after accepted
              have same : actual = retained := by
                injection actualShape.symm.trans shape with same _
              subst actual
              exact accepted_bonus_cap_index_le_152 hashes raw retained
                tail fixedOutcomes fixedCost after accepted
                actualShape n parsed

/-- Nonempty source cells at depths nine and ten before the generated bonus
prefix force both capped bonus rolls past the shallow gathered signatures.
The result is conditional only on successful execution of the exact suffix. -/
theorem accepted_bonus_suffix_index_bounds (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State) (nine ten : Bytes)
    (nineNonempty : nine ≠ []) (tenNonempty : ten ≠ [])
    (sourceNine : stack[9]? = some nine)
    (sourceTen : stack[10]? = some ten)
    (accepted : run hashes (ByteLayout.program.drop 840)
      (State.mk stack outcomes cost) = some final) :
    ∃ firstIndex lastIndex : Nat,
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 := by
  rw [generated_bonus_suffix, run_append] at accepted
  cases prelude : run hashes firstBonusPrelude
      (State.mk stack outcomes cost) with
  | none => simp [prelude] at accepted
  | some beforeFirst =>
      obtain ⟨rawFirst, regionFirst, firstShape, firstNine,
          firstTen, firstCap⟩ :=
        accepted_first_bonus_prelude_sources hashes stack outcomes cost
          beforeFirst nine ten sourceNine sourceTen prelude
      simp only [prelude, Option.bind_some] at accepted
      cases beforeFirst with
      | mk firstStack firstOutcomes firstCost =>
          change firstStack = rawFirst :: regionFirst at firstShape
          subst firstStack
          rw [run_append] at accepted
          cases firstRoll : run hashes [.roll]
              (State.mk (rawFirst :: regionFirst)
                firstOutcomes firstCost) with
          | none => simp [firstRoll] at accepted
          | some postFirst =>
              obtain ⟨firstIndex, decodedFirst⟩ :=
                accepted_roll_index hashes rawFirst regionFirst
                  firstOutcomes firstCost postFirst firstRoll
              have firstUpper := firstCap firstIndex decodedFirst
              simp only [firstRoll, Option.bind_some] at accepted
              rw [run_append] at accepted
              cases between : run hashes ByteBonusBetween.betweenOps
                  postFirst with
              | none => simp [between] at accepted
              | some beforeLast =>
                  simp only [between, Option.bind_some] at accepted
                  rw [run_append] at accepted
                  cases beforeLast with
                  | mk lastStack lastOutcomes lastCost =>
                      cases lastStack with
                      | nil =>
                          have noStep : step hashes .roll
                              (State.mk [] lastOutcomes lastCost) = none := by
                            change (if lastCost + 1 > 201 then none else none) = none
                            split_ifs <;> rfl
                          have noRoll : run hashes [.roll]
                              (State.mk [] lastOutcomes lastCost) = none := by
                            simp [run, noStep]
                          change (run hashes [.roll]
                              (State.mk [] lastOutcomes lastCost)).bind
                              (run hashes (ByteLayout.program.drop 850)) =
                                some final at accepted
                          simp [noRoll] at accepted
                      | cons rawLast regionLast =>
                          cases lastRoll : run hashes [.roll]
                              (State.mk (rawLast :: regionLast)
                                lastOutcomes lastCost) with
                          | none => simp [lastRoll] at accepted
                          | some postLast =>
                              obtain ⟨lastIndex, decodedLast⟩ :=
                                accepted_roll_index hashes rawLast regionLast
                                  lastOutcomes lastCost postLast lastRoll
                              have lastUpper :=
                                accepted_between_cap_index_le_152 hashes
                                  postFirst
                                  (State.mk (rawLast :: regionLast)
                                    lastOutcomes lastCost)
                                  rawLast regionLast between rfl
                                  lastIndex decodedLast
                              simp only [lastRoll, Option.bind_some] at accepted
                              have bounds :=
                                ByteBonusBetween.successful_two_bonus_index_bounds
                                  hashes rawFirst rawLast regionFirst regionLast
                                  firstIndex lastIndex firstOutcomes firstCost
                                  postFirst
                                  (State.mk (rawLast :: regionLast)
                                    lastOutcomes lastCost)
                                  postLast final nine ten
                                  nineNonempty tenNonempty firstNine firstTen
                                  decodedFirst decodedLast firstRoll between
                                  rfl lastRoll accepted
                              exact ⟨firstIndex, lastIndex,
                                bounds.1, firstUpper, bounds.2, lastUpper⟩

/-- In every successful full generated byte-model run, the seven signed
openings target distinct original HORS commitments and the two final bonus
rolls have decoded depths at least nine and ten. Those lower bounds alone do
not classify the chosen bonus bytes: a deep DER-shaped commitment is still a
possible source under an altered setup. -/
theorem accepted_whole_program_signed_and_bonus_bounds (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final) :
    ∃ (trace : List (Fin 150 × Bytes))
      (firstIndex lastIndex : Nat),
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 := by
  rw [FinalSignedChain.generated_whole_signed_boundary,
    run_append] at accepted
  cases preRun : run hashes (ByteLayout.program.take 446) initial with
  | none => simp [preRun] at accepted
  | some beforeCheck =>
      simp only [preRun, Option.bind_some] at accepted
      obtain ⟨afterCheck, checkStep, _, suffix⟩ :=
        run_cons_success hashes .checkmultisig
          (FinalSignedAccepted.finalRoundAllOps ++
            (allSignedBlocks ++ ByteLayout.program.drop 840))
          beforeCheck final accepted
      obtain ⟨result, tail, checkShape⟩ :=
        FinalSignedAccepted.successful_checkmultisig_result_shape
          hashes beforeCheck afterCheck checkStep
      cases afterCheck with
      | mk checkStack checkOutcomes checkCost =>
          change checkStack = boolBytes result :: tail at checkShape
          subst checkStack
          rw [run_append] at suffix
          cases init : run hashes FinalSignedAccepted.finalRoundAllOps
              (State.mk (boolBytes result :: tail)
                checkOutcomes checkCost) with
          | none => simp [init] at suffix
          | some afterInit =>
              have initShape :=
                FinalSignedAccepted.accepted_final_round_init_shape
                  hashes (boolBytes result :: tail) checkOutcomes
                  checkCost afterInit init
              simp only [init, Option.bind_some] at suffix
              rw [initShape] at suffix
              change run hashes (allSignedBlocks ++
                  ByteLayout.program.drop 840)
                (State.mk
                  (FinalSignedAccepted.baseRegion (boolBytes result) tail)
                  checkOutcomes checkCost) = some final at suffix
              rw [run_append] at suffix
              cases signed : run hashes allSignedBlocks
                  (State.mk
                    (FinalSignedAccepted.baseRegion (boolBytes result) tail)
                    checkOutcomes checkCost) with
              | none => simp [signed] at suffix
              | some afterSigned =>
                  obtain ⟨ids', gathered', dummies', commitments', tail',
                    trace, signedShape, pool, aligned, gatheredCount,
                    traceCount, distinct, hits, _tracePerm⟩ :=
                    accepted_all_signed_blocks hashes result tail
                      checkOutcomes checkCost afterSigned signed
                  simp only [signed, Option.bind_some] at suffix
                  rw [signedShape] at suffix
                  obtain ⟨nine, ten, nineNonempty, tenNonempty,
                      atNine, atTen⟩ :=
                    seven_signed_bonus_sources_nonempty
                      (boolBytes result) gathered' dummies' commitments'
                      tail' pool gatheredCount
                  obtain ⟨firstIndex, lastIndex, firstLower,
                    firstUpper, lastLower, lastUpper⟩ :=
                    accepted_bonus_suffix_index_bounds hashes
                      (nextRawFront (boolBytes result)
                        gathered' dummies' commitments' ++ tail')
                      checkOutcomes (checkCost + 63) final nine ten
                      nineNonempty tenNonempty atNine atTen suffix
                  exact ⟨trace, firstIndex, lastIndex, traceCount,
                    distinct, hits, firstLower, firstUpper,
                    lastLower, lastUpper⟩

end QSB.FinalBonusAccepted
