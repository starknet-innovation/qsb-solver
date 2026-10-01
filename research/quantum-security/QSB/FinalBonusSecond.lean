import QSB.FinalBonusAccepted

/-!
Source geometry of the second final-round bonus roll after either kind of
first bonus choice. This is a list-level classification over the generated
post-signed pool shape; execution and Core refinement are separate bridges.
-/
namespace QSB.FinalBonusSecond
open ByteMachine
open FinalSignedLoop
open FinalSignedChain
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def firstBonusOps : List Op :=
  FinalBonusAccepted.firstBonusPrelude ++ [.roll]

def bothBonusOps : List Op :=
  firstBonusOps ++ (ByteBonusBetween.betweenOps ++ [.roll])

theorem generated_bonus_op_segments :
    firstBonusOps = (ByteLayout.program.drop 840).take 5 ∧
    bothBonusOps = (ByteLayout.program.drop 840).take 10 := by decide

theorem generated_to_bonus_prefix :
    ByteLayout.program.take 840 =
      ByteLayout.program.take 446 ++
        ([.checkmultisig] ++
          (FinalSignedAccepted.finalRoundAllOps ++ allSignedBlocks)) := by
  decide

theorem generated_through_both_bonuses :
    ByteLayout.program.take 850 =
      ByteLayout.program.take 840 ++ bothBonusOps := by decide

theorem generated_after_both_bonuses :
    ByteLayout.program =
      ByteLayout.program.take 850 ++ ByteLayout.program.drop 850 := by decide

theorem generated_precheck_prefix :
    ByteLayout.program.take 879 =
      ByteLayout.program.take 850 ++
        (ByteLatePuzzle.lateOps ++ ByteFinalCounts.finalSetup) := by decide

/-- A first bonus draw from the surviving dummy pool keeps every commitment
in place while moving the selected dummy above the gathered signatures. -/
theorem first_dummy_roll_shape (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (seven : gathered.length = 7)
    (j : Nat) (within : j < dummies.length) :
    KeyRolls.rollAt (9 + j)
      (nextRawFront prior gathered dummies commitments ++ tail) =
      some (dummies[j] ::
        (gathered ++ [finalNonce, []]) ++
          dummies.eraseIdx j ++ commitments ++ prior :: tail) := by
  have frontLength : (gathered ++ [finalNonce, []]).length = 9 := by
    simp [seven]
  have moved := roll_from_middle
    (gathered ++ [finalNonce, []]) dummies
    (commitments ++ prior :: tail) j within
  simpa [nextRawFront, frontLength, List.append_assoc] using moved

/-- A first bonus draw at cap depth 152 selects the first surviving HORS
commitment, leaving all 143 dummy bytes in place. -/
theorem first_commitment_roll_shape (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7) :
    KeyRolls.rollAt 152
      (nextRawFront prior gathered dummies commitments ++ tail) =
      some (commitments[0]'(by
        have total := shape.poolCount
        rw [shape.commitmentCount]
        omega) ::
        (gathered ++ [finalNonce, []] ++ dummies) ++
          commitments.eraseIdx 0 ++ prior :: tail) := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have frontLength :
      (gathered ++ [finalNonce, []] ++ dummies).length = 152 := by
    simp [seven, dummyLength]
  have within : 0 < commitments.length := by
    rw [shape.commitmentCount, dummyLength]
    omega
  have moved := roll_from_middle
    (gathered ++ [finalNonce, []] ++ dummies) commitments
    (prior :: tail) 0 within
  simp only [Nat.add_zero] at moved
  rw [frontLength] at moved
  simpa [nextRawFront, List.append_assoc] using moved

/-- After the first bonus selects a dummy, the second roll's depths 10–151
address remaining dummies; depth 152 addresses the first HORS commitment. -/
theorem second_source_after_first_dummy (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (j : Nat) (within : j < dummies.length)
    (m : Nat) (lower : 10 ≤ m) (upper : m ≤ 152) :
    (dummies[j] ::
      (gathered ++ [finalNonce, []]) ++
        dummies.eraseIdx j ++ commitments ++ prior :: tail)[m]? =
      if m < 152 then (dummies.eraseIdx j)[m - 10]?
      else commitments[0]? := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have remainingLength : (dummies.eraseIdx j).length = 142 := by
    rw [List.length_eraseIdx_of_lt within, dummyLength]
  have frontLength : (dummies[j] :: gathered ++ [finalNonce, []]).length =
      10 := by simp [seven]
  have layout :
      dummies[j] :: (gathered ++ [finalNonce, []]) ++
          dummies.eraseIdx j ++ commitments ++ prior :: tail =
        (dummies[j] :: gathered ++ [finalNonce, []]) ++
          (dummies.eraseIdx j ++ (commitments ++ prior :: tail)) := by
    simp [List.append_assoc]
  rw [layout, List.getElem?_append_right (by omega)]
  have offset :
      m - (dummies[j] :: gathered ++ [finalNonce, []]).length =
        m - 10 := by rw [frontLength]
  rw [offset]
  by_cases dummy : m < 152
  · rw [if_pos dummy, List.getElem?_append_left (by omega)]
  · have capped : m = 152 := by omega
    subst m
    rw [if_neg (by omega)]
    rw [List.getElem?_append_right (by omega)]
    simp [remainingLength]
    have commitmentWithin : 0 < commitments.length := by
      rw [shape.commitmentCount, dummyLength]
      omega
    rw [List.getElem_append_left commitmentWithin]
    exact (List.getElem?_eq_getElem commitmentWithin).symm

/-- After the first bonus selects the first HORS commitment, every source
reachable by the second capped roll at depths 10–152 is still a dummy. -/
theorem second_source_after_first_commitment (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (commitmentWithin : 0 < commitments.length)
    (m : Nat) (lower : 10 ≤ m) (upper : m ≤ 152) :
    (commitments[0]'commitmentWithin ::
      (gathered ++ [finalNonce, []] ++ dummies) ++
        commitments.eraseIdx 0 ++ prior :: tail)[m]? =
      dummies[m - 10]? := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have frontLength :
      (commitments[0]'commitmentWithin ::
        gathered ++ [finalNonce, []]).length = 10 := by
    simp [seven]
  have layout :
      commitments[0]'commitmentWithin ::
          (gathered ++ [finalNonce, []] ++ dummies) ++
          commitments.eraseIdx 0 ++ prior :: tail =
        (commitments[0]'commitmentWithin ::
          gathered ++ [finalNonce, []]) ++
          (dummies ++ (commitments.eraseIdx 0 ++ prior :: tail)) := by
    simp [List.append_assoc]
  rw [layout, List.getElem?_append_right (by omega)]
  have offset :
      m - (commitments[0]'commitmentWithin ::
        gathered ++ [finalNonce, []]).length = m - 10 := by
    rw [frontLength]
  rw [offset, List.getElem?_append_left (by omega)]

/-- For any first capped bonus choice and any second capped bonus choice,
the second source is a dummy except when the first choice was a dummy and
the second reaches depth 152. In that one branch it is the first surviving
HORS commitment. -/
theorem second_bonus_source_map (prior : Bytes)
    (gathered dummies commitments tail firstStack : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (n m : Nat)
    (firstLower : 9 ≤ n) (firstUpper : n ≤ 152)
    (lastLower : 10 ≤ m) (lastUpper : m ≤ 152)
    (firstRoll : KeyRolls.rollAt n
      (nextRawFront prior gathered dummies commitments ++ tail) =
        some firstStack) :
    firstStack[m]? =
      if n < 152 then
        if m < 152 then (dummies.eraseIdx (n - 9))[m - 10]?
        else commitments[0]?
      else dummies[m - 10]? := by
  by_cases firstDummy : n < 152
  · let j := n - 9
    have within : j < dummies.length := by
      have total := shape.poolCount
      dsimp [j]
      omega
    have firstDepth : 9 + j = n := by dsimp [j]; omega
    have moved := first_dummy_roll_shape prior gathered dummies
      commitments tail seven j within
    rw [firstDepth] at moved
    have firstShape := Option.some.inj (firstRoll.symm.trans moved)
    subst firstStack
    have source := second_source_after_first_dummy prior gathered
      dummies commitments tail shape seven j within m lastLower lastUpper
    simpa [firstDummy, j] using source
  · have atCap : n = 152 := by omega
    subst n
    have moved := first_commitment_roll_shape prior gathered dummies
      commitments tail shape seven
    have firstShape := Option.some.inj (firstRoll.symm.trans moved)
    subst firstStack
    have commitmentWithin : 0 < commitments.length := by
      rw [shape.commitmentCount]
      have total := shape.poolCount
      omega
    have source := second_source_after_first_commitment prior gathered
      dummies commitments tail shape seven commitmentWithin
      m lastLower lastUpper
    simpa using source

/-- The actual second modeled bonus roll moves the byte given by the
two-branch source map. The fixed deep roll and second cap preserve all
shallow source cells while placing the capped index on top. -/
theorem accepted_second_bonus_source_role (hashes : Hashes)
    (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat)
    (beforeFirst postFirst beforeLast postLast : State)
    (prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) = some beforeFirst)
    (rawFirst : Bytes) (regionFirst : List Bytes)
    (firstShape : beforeFirst.stack = rawFirst :: regionFirst)
    (n : Nat) (firstLower : 9 ≤ n) (firstUpper : n ≤ 152)
    (parsedFirst : ByteIndex.parseScriptNum rawFirst = some (Int.ofNat n))
    (firstRoll : run hashes [.roll] beforeFirst = some postFirst)
    (between : run hashes ByteBonusBetween.betweenOps postFirst =
      some beforeLast)
    (rawLast : Bytes) (regionLast : List Bytes)
    (lastShape : beforeLast.stack = rawLast :: regionLast)
    (m : Nat) (lastLower : 10 ≤ m) (lastUpper : m ≤ 152)
    (parsedLast : ByteIndex.parseScriptNum rawLast = some (Int.ofNat m))
    (lastRoll : run hashes [.roll] beforeLast = some postLast) :
    postLast.stack.head? =
      if n < 152 then
        if m < 152 then (dummies.eraseIdx (n - 9))[m - 10]?
        else commitments[0]?
      else dummies[m - 10]? := by
  obtain ⟨retained, exactShape⟩ :=
    FinalBonusAccepted.accepted_first_bonus_prelude_exact hashes prior
      gathered dummies commitments tail shape seven outcomes cost
      beforeFirst prelude
  have same : rawFirst :: regionFirst =
      retained ::
        (nextRawFront prior gathered dummies commitments ++
          tail.eraseIdx 283) := firstShape.symm.trans exactShape
  have regionEq : regionFirst =
      nextRawFront prior gathered dummies commitments ++
        tail.eraseIdx 283 := by
    injection same with _ h
  cases beforeFirst with
  | mk firstStack firstOutcomes firstCost =>
      change firstStack = rawFirst :: regionFirst at firstShape
      subst firstStack
      obtain ⟨selectedFirst, atFirst, postFirstShape⟩ :=
        FinalBonusAccepted.accepted_roll_selected_source hashes
          rawFirst regionFirst firstOutcomes firstCost postFirst
          n parsedFirst firstRoll
      have keyRoll : KeyRolls.rollAt n regionFirst =
          some postFirst.stack := by
        rw [postFirstShape]
        simp [KeyRolls.rollAt, atFirst]
      rw [regionEq] at keyRoll
      have sourceMap := second_bonus_source_map prior gathered dummies
        commitments (tail.eraseIdx 283) postFirst.stack shape seven
        n m firstLower firstUpper lastLower lastUpper keyRoll
      cases postFirst with
      | mk postStack postOutcomes postCost =>
          have kept := ByteBonusBetween.accepted_between_preserves_shallow
            hashes postStack postOutcomes postCost beforeLast m
            (by omega) between
          cases beforeLast with
          | mk lastStack lastOutcomes lastCost =>
              change lastStack = rawLast :: regionLast at lastShape
              subst lastStack
              have regionKeep : regionLast[m]? = postStack[m]? := by
                simpa using kept
              obtain ⟨selectedLast, atLast, postLastShape⟩ :=
                FinalBonusAccepted.accepted_roll_selected_source hashes
                  rawLast regionLast lastOutcomes lastCost postLast
                  m parsedLast lastRoll
              rw [postLastShape]
              exact atLast.symm.trans (regionKeep.trans sourceMap)

/-- A successful single modeled roll preserves every source cell shallower
than its decoded depth, shifting it one position below the selected byte. -/
theorem accepted_roll_shallow_cell (hashes : Hashes)
    (raw : Bytes) (region : List Bytes)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (n p : Nat) (shallower : p < n)
    (parsed : ByteIndex.parseScriptNum raw = some (Int.ofNat n))
    (accepted : run hashes [.roll]
      (State.mk (raw :: region) outcomes cost) = some after) :
    after.stack[p + 1]? = region[p]? := by
  obtain ⟨selected, _, shape⟩ :=
    FinalBonusAccepted.accepted_roll_selected_source hashes raw region
      outcomes cost after n parsed accepted
  rw [shape]
  simpa using (List.getElem?_eraseIdx_of_lt
    (l := region) (i := n) (j := p) shallower)

/-- The fixed roll/cap before the second bonus choice preserves the first
ten shallow cells; the second roll shifts each one below its selected byte. -/
theorem accepted_second_bonus_preserves_shallow (hashes : Hashes)
    (postFirst beforeLast postLast : State)
    (between : run hashes ByteBonusBetween.betweenOps postFirst =
      some beforeLast)
    (rawLast : Bytes) (regionLast : List Bytes)
    (lastShape : beforeLast.stack = rawLast :: regionLast)
    (m p : Nat) (shallow : p < 10) (belowRoll : p < m)
    (parsedLast : ByteIndex.parseScriptNum rawLast = some (Int.ofNat m))
    (lastRoll : run hashes [.roll] beforeLast = some postLast) :
    postLast.stack[p + 1]? = postFirst.stack[p]? := by
  cases postFirst with
  | mk firstStack firstOutcomes firstCost =>
      have kept := ByteBonusBetween.accepted_between_preserves_shallow
        hashes firstStack firstOutcomes firstCost beforeLast p
        (by omega) between
      cases beforeLast with
      | mk lastStack lastOutcomes lastCost =>
          change lastStack = rawLast :: regionLast at lastShape
          subst lastStack
          have regionKeep : regionLast[p]? = firstStack[p]? := by
            simpa using kept
          exact (accepted_roll_shallow_cell hashes rawLast regionLast
            lastOutcomes lastCost postLast m p belowRoll
            parsedLast lastRoll).trans regionKeep

/-- Across both bonus rolls and their intervening fixed roll/cap, the
original seven gathered signatures, nonce, and zero dummy remain in the
same order at post-second-bonus depths two through ten. -/
theorem accepted_bonus_two_roll_shallow_origin (hashes : Hashes)
    (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat)
    (beforeFirst postFirst beforeLast postLast : State)
    (prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) = some beforeFirst)
    (rawFirst : Bytes) (regionFirst : List Bytes)
    (firstShape : beforeFirst.stack = rawFirst :: regionFirst)
    (n : Nat) (firstLower : 9 ≤ n)
    (parsedFirst : ByteIndex.parseScriptNum rawFirst = some (Int.ofNat n))
    (firstRoll : run hashes [.roll] beforeFirst = some postFirst)
    (between : run hashes ByteBonusBetween.betweenOps postFirst =
      some beforeLast)
    (rawLast : Bytes) (regionLast : List Bytes)
    (lastShape : beforeLast.stack = rawLast :: regionLast)
    (m : Nat) (lastLower : 10 ≤ m)
    (parsedLast : ByteIndex.parseScriptNum rawLast = some (Int.ofNat m))
    (lastRoll : run hashes [.roll] beforeLast = some postLast)
    (p : Nat) (within : p ≤ 8) :
    postLast.stack[p + 2]? =
      (nextRawFront prior gathered dummies commitments ++ tail)[p]? := by
  obtain ⟨retained, exactShape⟩ :=
    FinalBonusAccepted.accepted_first_bonus_prelude_exact hashes prior
      gathered dummies commitments tail shape seven outcomes cost
      beforeFirst prelude
  have same : rawFirst :: regionFirst =
      retained :: (nextRawFront prior gathered dummies commitments ++
        tail.eraseIdx 283) := firstShape.symm.trans exactShape
  have regionEq : regionFirst =
      nextRawFront prior gathered dummies commitments ++
        tail.eraseIdx 283 := by
    injection same with _ h
  have frontLength := next_raw_front_length prior gathered dummies
    commitments shape
  have frontWithin : p <
      (nextRawFront prior gathered dummies commitments).length := by
    rw [frontLength, seven]
    omega
  have regionSource : regionFirst[p]? =
      (nextRawFront prior gathered dummies commitments ++ tail)[p]? := by
    rw [regionEq]
    rw [List.getElem?_append_left frontWithin,
      List.getElem?_append_left frontWithin]
  cases beforeFirst with
  | mk firstStack firstOutcomes firstCost =>
      change firstStack = rawFirst :: regionFirst at firstShape
      subst firstStack
      have firstKeep := accepted_roll_shallow_cell hashes rawFirst
        regionFirst firstOutcomes firstCost postFirst n p
        (by omega) parsedFirst firstRoll
      cases postFirst with
      | mk postStack postOutcomes postCost =>
          have betweenKeep :=
            ByteBonusBetween.accepted_between_preserves_shallow hashes
              postStack postOutcomes postCost beforeLast (p + 1)
              (by omega) between
          cases beforeLast with
          | mk lastStack lastOutcomes lastCost =>
              change lastStack = rawLast :: regionLast at lastShape
              subst lastStack
              have lastKeep := accepted_roll_shallow_cell hashes rawLast
                regionLast lastOutcomes lastCost postLast m (p + 1)
                (by omega) parsedLast lastRoll
              have bridge : regionLast[p + 1]? = postStack[p + 1]? := by
                simpa using betweenKeep
              simpa [Nat.add_assoc] using
                (lastKeep.trans (bridge.trans
                  (firstKeep.trans regionSource)))

/-- The nine shallow cells before the bonus prefix are exactly seven
gathered dummy signatures, the fixed nonce signature, and the empty dummy. -/
theorem signed_front_origins (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (seven : gathered.length = 7) :
    (∀ p : Nat, p < 7 →
      (nextRawFront prior gathered dummies commitments ++ tail)[p]? =
        gathered[p]?) ∧
    (nextRawFront prior gathered dummies commitments ++ tail)[7]? =
      some finalNonce ∧
    (nextRawFront prior gathered dummies commitments ++ tail)[8]? =
      some [] := by
  have layout : nextRawFront prior gathered dummies commitments ++ tail =
      gathered ++ (finalNonce :: [] ::
        (dummies ++ commitments ++ prior :: tail)) := by
    simp [nextRawFront, List.append_assoc]
  constructor
  · intro p hp
    rw [layout, List.getElem?_append_left (by omega)]
  constructor
  · rw [layout, List.getElem?_append_right (by omega)]
    simp [seven]
  · rw [layout, List.getElem?_append_right (by omega)]
    simp [seven]

/-- A completed generated bonus suffix from a seven-signed pool state has
actual reached states after both bonus rolls. Their top bytes obey the
first- and second-source maps under the decoded cap bounds. -/
theorem accepted_bonus_suffix_source_trace (hashes : Hashes)
    (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (ByteLayout.program.drop 840)
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) = some final) :
    ∃ (firstIndex lastIndex : Nat) (postFirst postLast : State),
      run hashes firstBonusOps
        (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
          outcomes cost) = some postFirst ∧
      run hashes bothBonusOps
        (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
          outcomes cost) = some postLast ∧
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 ∧
      postFirst.stack.head? =
        (if firstIndex < 152 then dummies[firstIndex - 9]?
          else commitments[0]?) ∧
      postLast.stack.head? =
        (if firstIndex < 152 then
          if lastIndex < 152 then
            (dummies.eraseIdx (firstIndex - 9))[lastIndex - 10]?
          else commitments[0]?
        else dummies[lastIndex - 10]?) ∧
      postLast.stack[1]? = postFirst.stack.head? ∧
      (∀ p : Nat, p ≤ 8 → postLast.stack[p + 2]? =
        (nextRawFront prior gathered dummies commitments ++ tail)[p]?) := by
  obtain ⟨nine, ten, nineNonempty, tenNonempty,
      sourceNine, sourceTen⟩ :=
    FinalSignedChain.seven_signed_bonus_sources_nonempty prior
      gathered dummies commitments tail shape seven
  rw [FinalBonusAccepted.generated_bonus_suffix, run_append] at accepted
  cases prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFront prior gathered dummies commitments ++ tail)
        outcomes cost) with
  | none => simp [prelude] at accepted
  | some beforeFirst =>
      obtain ⟨rawFirst, regionFirst, firstShape, firstNine,
          firstTen, firstCap⟩ :=
        FinalBonusAccepted.accepted_first_bonus_prelude_sources hashes
          (nextRawFront prior gathered dummies commitments ++ tail)
          outcomes cost beforeFirst nine ten sourceNine sourceTen prelude
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
                FinalBonusAccepted.accepted_roll_index hashes rawFirst
                  regionFirst firstOutcomes firstCost postFirst firstRoll
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
                                FinalBonusAccepted.accepted_roll_index hashes
                                  rawLast regionLast lastOutcomes lastCost
                                  postLast lastRoll
                              have lastUpper :=
                                FinalBonusAccepted.accepted_between_cap_index_le_152
                                  hashes postFirst
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
                              have firstSource :=
                                FinalBonusAccepted.accepted_first_bonus_source_role
                                  hashes prior gathered dummies commitments
                                  tail shape seven outcomes cost
                                  (State.mk (rawFirst :: regionFirst)
                                    firstOutcomes firstCost)
                                  postFirst prelude rawFirst regionFirst rfl
                                  firstIndex bounds.1 firstUpper
                                  decodedFirst firstRoll
                              have lastSource :=
                                accepted_second_bonus_source_role hashes prior
                                  gathered dummies commitments tail shape seven
                                  outcomes cost
                                  (State.mk (rawFirst :: regionFirst)
                                    firstOutcomes firstCost)
                                  postFirst
                                  (State.mk (rawLast :: regionLast)
                                    lastOutcomes lastCost)
                                  postLast prelude rawFirst regionFirst rfl
                                  firstIndex bounds.1 firstUpper decodedFirst
                                  firstRoll between rawLast regionLast rfl
                                  lastIndex bounds.2 lastUpper decodedLast
                                  lastRoll
                              have firstRun : run hashes firstBonusOps
                                  (State.mk (nextRawFront prior gathered
                                    dummies commitments ++ tail) outcomes cost) =
                                    some postFirst := by
                                simp [firstBonusOps, run_append, prelude,
                                  firstRoll]
                              have bothRun : run hashes bothBonusOps
                                  (State.mk (nextRawFront prior gathered
                                    dummies commitments ++ tail) outcomes cost) =
                                    some postLast := by
                                simp [bothBonusOps, run_append, firstRun,
                                  between, lastRoll]
                              have firstCarried : postLast.stack[1]? =
                                  postFirst.stack.head? := by
                                simpa only [List.head?_eq_getElem?] using
                                  (accepted_second_bonus_preserves_shallow
                                  hashes postFirst
                                  (State.mk (rawLast :: regionLast)
                                    lastOutcomes lastCost)
                                  postLast between rawLast regionLast rfl
                                  lastIndex 0 (by omega) (by omega)
                                  decodedLast lastRoll)
                              have shallow : ∀ p : Nat, p ≤ 8 →
                                  postLast.stack[p + 2]? =
                                    (nextRawFront prior gathered dummies
                                      commitments ++ tail)[p]? := by
                                intro p hp
                                exact accepted_bonus_two_roll_shallow_origin
                                  hashes prior gathered dummies commitments
                                  tail shape seven outcomes cost
                                  (State.mk (rawFirst :: regionFirst)
                                    firstOutcomes firstCost)
                                  postFirst
                                  (State.mk (rawLast :: regionLast)
                                    lastOutcomes lastCost)
                                  postLast prelude rawFirst regionFirst rfl
                                  firstIndex bounds.1 decodedFirst firstRoll
                                  between rawLast regionLast rfl lastIndex
                                  bounds.2 decodedLast lastRoll p hp
                              exact ⟨firstIndex, lastIndex, postFirst, postLast,
                                firstRun, bothRun, bounds.1, firstUpper,
                                bounds.2, lastUpper, firstSource, lastSource,
                                firstCarried, shallow⟩

/-- Every successful full generated byte-model run reaches the seven-signed
pool state and then two concrete bonus-roll states. The two selected top
bytes satisfy the mutually exclusive commitment-source cases. -/
theorem accepted_whole_program_bonus_source_trace (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final) :
    ∃ (result : Bool)
      (gathered dummies commitments tail : List Bytes)
      (outcomes : List Bool) (cost : Nat)
      (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150))
      (firstIndex lastIndex : Nat) (postFirst postLast : State),
      run hashes (ByteLayout.program.take 840) initial =
        some (State.mk (nextRawFront (boolBytes result)
          gathered dummies commitments ++ tail) outcomes cost) ∧
      PoolShape gathered dummies commitments ∧
      gathered.length = 7 ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      AlignedPool remainingIds dummies commitments ∧
      List.Perm (trace.map Prod.fst ++ remainingIds)
        (List.finRange 150) ∧
      gathered =
        (trace.map (fun p => generatedDummyAt p.1)).reverse ∧
      run hashes firstBonusOps
        (State.mk (nextRawFront (boolBytes result)
          gathered dummies commitments ++ tail) outcomes cost) =
            some postFirst ∧
      run hashes bothBonusOps
        (State.mk (nextRawFront (boolBytes result)
          gathered dummies commitments ++ tail) outcomes cost) =
            some postLast ∧
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 ∧
      postFirst.stack.head? =
        (if firstIndex < 152 then dummies[firstIndex - 9]?
          else commitments[0]?) ∧
      postLast.stack.head? =
        (if firstIndex < 152 then
          if lastIndex < 152 then
            (dummies.eraseIdx (firstIndex - 9))[lastIndex - 10]?
          else commitments[0]?
        else dummies[lastIndex - 10]?) ∧
      postLast.stack[1]? = postFirst.stack.head? ∧
      (∀ p : Nat, p ≤ 8 → postLast.stack[p + 2]? =
        (nextRawFront (boolBytes result)
          gathered dummies commitments ++ tail)[p]?) ∧
      FinalSignedChain.extractWholeFinal hashes initial = some trace ∧
      FinalSignedChain.extractWholeRemaining hashes initial =
        some remainingIds := by
  rw [FinalSignedChain.generated_whole_signed_boundary,
    run_append] at accepted
  cases preRun : run hashes (ByteLayout.program.take 446) initial with
  | none => simp [preRun] at accepted
  | some beforeCheck =>
      simp only [preRun, Option.bind_some] at accepted
      obtain ⟨afterCheck, checkStep, checkWithin, suffix⟩ :=
        FirstAcceptedOrigin.run_cons_success hashes .checkmultisig
          (FinalSignedAccepted.finalRoundAllOps ++
            (allSignedBlocks ++ ByteLayout.program.drop 840))
          beforeCheck final accepted
      have checkRun : run hashes [.checkmultisig] beforeCheck =
          some afterCheck := by
        simp [run, checkStep,
          show ¬afterCheck.stack.length > 1000 by omega]
      obtain ⟨result, earlyTail, checkShape⟩ :=
        FinalSignedAccepted.successful_checkmultisig_result_shape
          hashes beforeCheck afterCheck checkStep
      cases afterCheck with
      | mk checkStack checkOutcomes checkCost =>
          change checkStack = boolBytes result :: earlyTail at checkShape
          subst checkStack
          rw [run_append] at suffix
          cases init : run hashes FinalSignedAccepted.finalRoundAllOps
              (State.mk (boolBytes result :: earlyTail)
                checkOutcomes checkCost) with
          | none => simp [init] at suffix
          | some afterInit =>
              have initShape :=
                FinalSignedAccepted.accepted_final_round_init_shape
                  hashes (boolBytes result :: earlyTail) checkOutcomes
                  checkCost afterInit init
              simp only [init, Option.bind_some] at suffix
              rw [initShape] at suffix
              change run hashes (allSignedBlocks ++
                  ByteLayout.program.drop 840)
                (State.mk
                  (FinalSignedAccepted.baseRegion (boolBytes result) earlyTail)
                  checkOutcomes checkCost) = some final at suffix
              rw [run_append] at suffix
              cases signed : run hashes allSignedBlocks
                  (State.mk
                    (FinalSignedAccepted.baseRegion (boolBytes result) earlyTail)
                    checkOutcomes checkCost) with
              | none => simp [signed] at suffix
              | some afterSigned =>
                  obtain ⟨ids', gathered', dummies', commitments', tail',
                    trace, signedShape, pool, aligned, gatheredCount,
                    traceCount, traceExtract, remainingExtract,
                    distinct, hits, tracePerm,
                    gatheredTrace⟩ :=
                    FinalSignedChain.accepted_all_signed_blocks hashes result
                      earlyTail checkOutcomes checkCost afterSigned signed
                  have prefixRun : run hashes (ByteLayout.program.take 840)
                      initial = some afterSigned := by
                    rw [generated_to_bonus_prefix, run_append]
                    simp only [preRun, Option.bind_some]
                    rw [run_append]
                    simp only [checkRun, Option.bind_some]
                    rw [run_append]
                    simpa [init, initShape] using signed
                  have signedPrefixRun : run hashes
                      (ByteLayout.program.take 749) initial =
                      some afterInit := by
                    rw [FinalSignedChain.generated_to_signed_prefix,
                      run_append]
                    simp only [preRun, Option.bind_some]
                    rw [run_append]
                    simp only [checkRun, Option.bind_some]
                    simpa [initShape] using init
                  have afterDrop : afterInit.stack.drop 303 = earlyTail := by
                    rw [initShape]
                    change (FinalSignedAccepted.baseRegion
                      (boolBytes result) earlyTail).drop 303 = earlyTail
                    exact FinalSignedChain.baseRegion_drop_tail
                      (boolBytes result) earlyTail
                  have traceComputed :
                      FinalSignedChain.extractWholeFinal hashes initial =
                        some trace := by
                    simp [FinalSignedChain.extractWholeFinal,
                      signedPrefixRun, afterDrop, traceExtract]
                  have remainingComputed :
                      FinalSignedChain.extractWholeRemaining hashes initial =
                        some ids' := by
                    simp [FinalSignedChain.extractWholeRemaining,
                      signedPrefixRun, afterDrop, remainingExtract]
                  simp only [signed, Option.bind_some] at suffix
                  rw [signedShape] at suffix
                  obtain ⟨firstIndex, lastIndex, postFirst, postLast,
                    firstRun, bothRun, firstLower, firstUpper,
                    lastLower, lastUpper, firstSource, lastSource,
                    firstCarried, shallow⟩ :=
                    accepted_bonus_suffix_source_trace hashes
                      (boolBytes result) gathered' dummies' commitments'
                      tail' pool gatheredCount checkOutcomes
                      (checkCost + 63) final suffix
                  refine ⟨result, gathered', dummies', commitments', tail',
                    checkOutcomes, checkCost + 63, trace, ids', firstIndex,
                    lastIndex, postFirst, postLast, ?_, pool, gatheredCount,
                    traceCount, distinct, hits, aligned, tracePerm,
                    gatheredTrace,
                    firstRun, bothRun,
                    firstLower, firstUpper, lastLower, lastUpper,
                    firstSource, lastSource, firstCarried, shallow,
                    traceComputed, remainingComputed⟩
                  rw [prefixRun, signedShape]

/-- From the reached post-bonus stack, the final CHECKMULTISIG witness
contains the last bonus byte, first bonus byte, seven gathered bytes, and
fixed nonce in that order, followed by the empty dummy. -/
theorem accepted_postbonus_final_signature_origins (hashes : Hashes)
    (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (seven : gathered.length = 7)
    (postFirst postLast final : State)
    (firstCarried : postLast.stack[1]? = postFirst.stack.head?)
    (shallow : ∀ p : Nat, p ≤ 8 → postLast.stack[p + 2]? =
      (nextRawFront prior gathered dummies commitments ++ tail)[p]?)
    (suffix : run hashes (ByteLayout.program.drop 850)
      postLast = some final) :
    ∃ beforeCheck : State,
      run hashes (ByteLatePuzzle.lateOps ++ ByteFinalCounts.finalSetup)
        postLast = some beforeCheck ∧
      beforeCheck.stack[12]? = postLast.stack.head? ∧
      beforeCheck.stack[13]? = postFirst.stack.head? ∧
      (∀ j : Nat, j < 7 →
        beforeCheck.stack[j + 14]? = gathered[j]?) ∧
      beforeCheck.stack[21]? = some finalNonce ∧
      beforeCheck.stack[22]? = some [] := by
  obtain ⟨gatheredCells, nonceCell, dummyCell⟩ :=
    signed_front_origins prior gathered dummies commitments tail seven
  cases postLast with
  | mk postStack postOutcomes postCost =>
      obtain ⟨beforeCheck, prefixRun, origin⟩ :=
        ByteLatePuzzle.accepted_generated_final_witness_origins hashes
          postStack postOutcomes postCost final suffix
      refine ⟨beforeCheck, prefixRun, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.head?_eq_getElem?] using origin 0 (by omega)
      · have firstSlot : beforeCheck.stack[13]? = postStack[1]? := by
          simpa using origin 1 (by omega)
        exact firstSlot.trans firstCarried
      · intro j within
        have source := (origin (j + 2) (by omega)).trans
          ((shallow j (by omega)).trans (gatheredCells j within))
        simpa [Nat.add_assoc] using source
      · have source := (origin 9 (by omega)).trans
          ((shallow 7 (by omega)).trans nonceCell)
        simpa using source
      · have source := (origin 10 (by omega)).trans
          ((shallow 8 (by omega)).trans dummyCell)
        simpa using source

/-- The first surviving commitment is paired with one original HORS position
that was not among the seven opening comparisons. This follows from the
pool's aligned erase operations, without assuming distinct hash outputs. -/
theorem first_remaining_commitment_unopened
    (trace : List (Fin 150 × Bytes))
    (remainingIds : List (Fin 150))
    (dummies commitments : List Bytes)
    (aligned : AlignedPool remainingIds dummies commitments)
    (permutation : List.Perm (trace.map Prod.fst ++ remainingIds)
      (List.finRange 150))
    (nonempty : 0 < commitments.length) :
    ∃ candidate : Fin 150,
      commitments[0]? = some (generatedCommitmentAt candidate) ∧
      candidate ∉ trace.map Prod.fst := by
  have idsNonempty : 0 < remainingIds.length := by
    rw [aligned.commitmentMap] at nonempty
    simpa using nonempty
  let candidate : Fin 150 := remainingIds[0]
  have source : commitments[0]? =
      some (generatedCommitmentAt candidate) := by
    simp [aligned.commitmentMap, candidate, idsNonempty]
  have allDistinct : (trace.map Prod.fst ++ remainingIds).Nodup :=
    permutation.nodup_iff.mpr (List.nodup_finRange 150)
  have disjoint := (List.nodup_append.mp allDistinct).2.2
  have notOpened : candidate ∉ trace.map Prod.fst := by
    intro opened
    exact disjoint candidate opened candidate
      (List.getElem_mem idsNonempty) rfl
  exact ⟨candidate, source, notOpened⟩

/-- An arbitrary completed generated byte-model run reaches CHECKMULTISIG
with its ten signature-source cells in exact order: second bonus, first
bonus, seven gathered generated dummy signatures, and fixed nonce. The
following dummy is empty. The theorem retains both bonus-source equations
and the seven distinct signed HORS openings from that same run. -/
theorem accepted_whole_program_final_signature_origins (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final) :
    ∃ (result : Bool)
      (gathered dummies commitments tail : List Bytes)
      (outcomes : List Bool) (cost : Nat)
      (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150))
      (candidate : Fin 150)
      (firstIndex lastIndex : Nat)
      (postFirst postLast beforeCheck : State),
      run hashes (ByteLayout.program.take 840) initial =
        some (State.mk (nextRawFront (boolBytes result)
          gathered dummies commitments ++ tail) outcomes cost) ∧
      run hashes (ByteLayout.program.take 850) initial = some postLast ∧
      run hashes (ByteLayout.program.take 879) initial =
        some beforeCheck ∧
      PoolShape gathered dummies commitments ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
      AlignedPool remainingIds dummies commitments ∧
      List.Perm (trace.map Prod.fst ++ remainingIds)
        (List.finRange 150) ∧
      gathered =
        (trace.map (fun p => generatedDummyAt p.1)).reverse ∧
      commitments[0]? = some (generatedCommitmentAt candidate) ∧
      candidate ∉ trace.map Prod.fst ∧
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 ∧
      postFirst.stack.head? =
        (if firstIndex < 152 then dummies[firstIndex - 9]?
          else commitments[0]?) ∧
      postLast.stack.head? =
        (if firstIndex < 152 then
          if lastIndex < 152 then
            (dummies.eraseIdx (firstIndex - 9))[lastIndex - 10]?
          else commitments[0]?
        else dummies[lastIndex - 10]?) ∧
      run hashes (ByteLatePuzzle.lateOps ++ ByteFinalCounts.finalSetup)
        postLast = some beforeCheck ∧
      beforeCheck.stack[12]? = postLast.stack.head? ∧
      beforeCheck.stack[13]? = postFirst.stack.head? ∧
      (∀ j : Nat, j < 7 →
        beforeCheck.stack[j + 14]? = gathered[j]?) ∧
      beforeCheck.stack[21]? = some finalNonce ∧
      beforeCheck.stack[22]? = some [] ∧
      (firstIndex = 152 →
        beforeCheck.stack[13]? =
          some (generatedCommitmentAt candidate)) ∧
      (firstIndex < 152 ∧ lastIndex = 152 →
        beforeCheck.stack[12]? =
          some (generatedCommitmentAt candidate)) ∧
      FinalSignedChain.extractWholeFinal hashes initial = some trace ∧
      FinalSignedChain.extractWholeRemaining hashes initial =
        some remainingIds := by
  obtain ⟨result, gathered, dummies, commitments, tail,
      outcomes, cost, trace, remainingIds, firstIndex, lastIndex,
      postFirst, postLast,
      prefixRun, pool, seven, traceCount, distinct, hits,
      aligned, tracePerm, gatheredTrace,
      firstRun, bothRun, firstLower, firstUpper,
      lastLower, lastUpper, firstSource, lastSource,
      firstCarried, shallow, traceComputed, remainingComputed⟩ :=
    accepted_whole_program_bonus_source_trace hashes initial final accepted
  have through : run hashes (ByteLayout.program.take 850) initial =
      some postLast := by
    rw [generated_through_both_bonuses, run_append]
    simp [prefixRun, bothRun]
  have full := accepted
  rw [generated_after_both_bonuses, run_append] at full
  have suffix : run hashes (ByteLayout.program.drop 850)
      postLast = some final := by
    simpa [through] using full
  obtain ⟨beforeCheck, beforeRun, lastSlot, firstSlot,
      gatheredSlots, nonceSlot, dummySlot⟩ :=
    accepted_postbonus_final_signature_origins hashes
      (boolBytes result) gathered dummies commitments tail seven
      postFirst postLast final firstCarried shallow suffix
  have beforePrefix : run hashes (ByteLayout.program.take 879) initial =
      some beforeCheck := by
    rw [generated_precheck_prefix, run_append]
    simp [through, beforeRun]
  have commitmentNonempty : 0 < commitments.length := by
    rw [pool.commitmentCount]
    have count := pool.poolCount
    omega
  obtain ⟨candidate, candidateSource, candidateUnopened⟩ :=
    first_remaining_commitment_unopened trace remainingIds dummies
      commitments aligned tracePerm commitmentNonempty
  have firstException : firstIndex = 152 →
      beforeCheck.stack[13]? =
        some (generatedCommitmentAt candidate) := by
    intro atCap
    rw [firstSlot, firstSource]
    simp [atCap, candidateSource]
  have lastException : firstIndex < 152 ∧ lastIndex = 152 →
      beforeCheck.stack[12]? =
        some (generatedCommitmentAt candidate) := by
    intro ⟨firstShallow, atCap⟩
    rw [lastSlot, lastSource]
    simp [firstShallow, atCap, candidateSource]
  exact ⟨result, gathered, dummies, commitments, tail,
    outcomes, cost, trace, remainingIds, candidate, firstIndex, lastIndex,
    postFirst, postLast,
    beforeCheck, prefixRun, through, beforePrefix, pool, traceCount, distinct,
    hits, aligned, tracePerm, gatheredTrace,
    candidateSource, candidateUnopened,
    firstLower, firstUpper, lastLower, lastUpper,
    firstSource, lastSource, beforeRun, lastSlot, firstSlot,
    gatheredSlots, nonceSlot, dummySlot,
    firstException, lastException, traceComputed, remainingComputed⟩

/-- A conditional byte-model setup reduction. If both reached final bonus
signature slots must satisfy `sigSyntax`, then excluding that syntax from every
generated second-round HORS commitment rules out either capped-depth bonus
selection. Applying this to Bitcoin Core requires a separate refinement from
its real signature parser and CHECKMULTISIG verification to `checkedSyntax`. -/
theorem no_bonus_commitment_of_signature_syntax (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (sigSyntax : Bytes → Prop)
    (noCommitmentSyntax :
      ∀ id : Fin 150, ¬ sigSyntax (generatedCommitmentAt id))
    (checkedSyntax : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      (∀ sig, beforeCheck.stack[12]? = some sig → sigSyntax sig) ∧
      (∀ sig, beforeCheck.stack[13]? = some sig → sigSyntax sig)) :
    ∃ firstIndex lastIndex : Nat,
      9 ≤ firstIndex ∧ firstIndex < 152 ∧
      10 ≤ lastIndex ∧ lastIndex < 152 := by
  obtain ⟨result, gathered, dummies, commitments, tail,
    outcomes, cost, trace, remainingIds, candidate, firstIndex, lastIndex,
    postFirst, postLast, beforeCheck,
    _prefixRun, _through, beforePrefix, _pool, _traceCount, _distinct,
    _hits, _aligned, _tracePerm, _gatheredTrace,
    _candidateSource, _candidateUnopened,
    firstLower, firstUpper, lastLower, lastUpper,
    _firstSource, _lastSource, _beforeRun, _lastSlot, _firstSlot,
    _gatheredSlots, _nonceSlot, _dummySlot,
    firstException, lastException, _traceComputed,
    _remainingComputed⟩ :=
      accepted_whole_program_final_signature_origins
        hashes initial final accepted
  obtain ⟨lastSyntax, firstSyntax⟩ :=
    checkedSyntax beforeCheck beforePrefix
  have firstShallow : firstIndex < 152 := by
    by_contra h
    have atCap : firstIndex = 152 := by omega
    exact noCommitmentSyntax candidate
      (firstSyntax _ (firstException atCap))
  have lastShallow : lastIndex < 152 := by
    by_contra h
    have atCap : lastIndex = 152 := by omega
    exact noCommitmentSyntax candidate
      (lastSyntax _ (lastException ⟨firstShallow, atCap⟩))
  exact ⟨firstIndex, lastIndex, firstLower, firstShallow,
    lastLower, lastShallow⟩

/-- With ten signatures and ten keys present, success of the Core-shaped
matching loop forces the syntax predicate on each corresponding signature,
provided every successful pair verification implies that predicate. This
does not assert that the supplied verifier is Bitcoin Core's verifier. -/
theorem matched_final_signature_has_syntax
    (verify : Bytes → Bytes → Bool) (sigSyntax : Bytes → Prop)
    (verifySound : ∀ sig key, verify sig key = true → sigSyntax sig)
    (stack : List Bytes) (enough : 22 ≤ stack.length)
    (matched : Multisig.matchSigs verify
      ((stack.drop 12).take 10) ((stack.drop 1).take 10) = true)
    (p : Nat) (within : p < 10) :
    ∀ sig, stack[p + 12]? = some sig → sigSyntax sig := by
  have sigLength : ((stack.drop 12).take 10).length = 10 := by
    simp [List.length_take, List.length_drop]
    omega
  have keyLength : ((stack.drop 1).take 10).length = 10 := by
    simp [List.length_take]
    omega
  have pairs :=
    (Multisig.equal_counts_success_iff_pairs verify
      (by rw [sigLength, keyLength])).mp matched
  intro sig atSlot
  have atMatched : ((stack.drop 12).take 10)[p]? = some sig := by
    rw [List.getElem?_take, if_pos within, List.getElem?_drop]
    simpa [Nat.add_comm] using atSlot
  have sigWithin : p < ((stack.drop 12).take 10).length := by omega
  have keyWithin : p < ((stack.drop 1).take 10).length := by omega
  have same : ((stack.drop 12).take 10)[p] = sig :=
    Option.some.inj
      ((List.getElem?_eq_getElem sigWithin).symm.trans atMatched)
  have checked := pairs.get sigWithin keyWithin
  change verify ((stack.drop 12).take 10)[p]
    ((stack.drop 1).take 10)[p] = true at checked
  rw [same] at checked
  exact verifySound sig _ checked

/-- A matched final scan can use a commitment in a bonus signature slot only
if the first still-unopened generated commitment itself passes the supplied
signature syntax. The witness identifies its original pool position and the
two executable signed-pool extractions. This is the explicit bad-setup branch
for the literal byte model; dynamic setup and Core refinement remain separate. -/
theorem matched_bonus_overshoot_has_unopened_syntax (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool) (sigSyntax : Bytes → Prop)
    (verifySound : ∀ sig key, verify sig key = true → sigSyntax sig)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150)) (candidate : Fin 150)
      (firstIndex lastIndex : Nat),
      trace.length = 7 ∧
      candidate ∉ trace.map Prod.fst ∧
      9 ≤ firstIndex ∧ firstIndex ≤ 152 ∧
      10 ≤ lastIndex ∧ lastIndex ≤ 152 ∧
      FinalSignedChain.extractWholeFinal hashes initial = some trace ∧
      FinalSignedChain.extractWholeRemaining hashes initial =
        some remainingIds ∧
      (firstIndex = 152 ∨ lastIndex = 152 →
        sigSyntax (generatedCommitmentAt candidate)) := by
  obtain ⟨result, gathered, dummies, commitments, tail,
    outcomes, cost, trace, remainingIds, candidate, firstIndex, lastIndex,
    postFirst, postLast, beforeCheck,
    _prefixRun, _through, beforePrefix, _pool, traceCount, _distinct,
    _hits, _aligned, _tracePerm, _gatheredTrace,
    _candidateSource, candidateUnopened,
    firstLower, firstUpper, lastLower, lastUpper,
    _firstSource, _lastSource, _beforeRun, _lastSlot, _firstSlot,
    _gatheredSlots, _nonceSlot, dummySlot,
    firstException, lastException, traceComputed,
    remainingComputed⟩ :=
      accepted_whole_program_final_signature_origins
        hashes initial final accepted
  have enough : 22 ≤ beforeCheck.stack.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp dummySlot
    omega
  have success := matched beforeCheck beforePrefix
  have firstSyntax :=
    matched_final_signature_has_syntax verify sigSyntax verifySound
      beforeCheck.stack enough success 1 (by omega)
  have lastSyntax :=
    matched_final_signature_has_syntax verify sigSyntax verifySound
      beforeCheck.stack enough success 0 (by omega)
  refine ⟨trace, remainingIds, candidate, firstIndex, lastIndex,
    traceCount, candidateUnopened, firstLower, firstUpper,
    lastLower, lastUpper, traceComputed, remainingComputed, ?_⟩
  intro overshoot
  rcases overshoot with firstCap | lastCap
  · exact firstSyntax _ (firstException firstCap)
  · by_cases firstShallow : firstIndex < 152
    · exact lastSyntax _ (lastException ⟨firstShallow, lastCap⟩)
    · have firstCap : firstIndex = 152 := by omega
      exact firstSyntax _ (firstException firstCap)

/-- A second conditional interface isolates what Core refinement must supply:
the reached final CHECKMULTISIG must behave like a successful ten-pair scan,
and successful pair checks must imply the chosen signature syntax. The byte
model itself still supplies only Boolean signature outcomes. -/
theorem no_bonus_commitment_of_matching_verifier (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool) (sigSyntax : Bytes → Prop)
    (verifySound : ∀ sig key, verify sig key = true → sigSyntax sig)
    (noCommitmentSyntax :
      ∀ id : Fin 150, ¬ sigSyntax (generatedCommitmentAt id))
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ firstIndex lastIndex : Nat,
      9 ≤ firstIndex ∧ firstIndex < 152 ∧
      10 ≤ lastIndex ∧ lastIndex < 152 := by
  obtain ⟨result, gathered, dummies, commitments, tail,
    outcomes, cost, trace, remainingIds, candidate, firstIndex, lastIndex,
    postFirst, postLast, beforeCheck,
    _prefixRun, _through, beforePrefix, _pool, _traceCount, _distinct,
    _hits, _aligned, _tracePerm, _gatheredTrace,
    _candidateSource, _candidateUnopened,
    _firstLower, _firstUpper, _lastLower, _lastUpper,
    _firstSource, _lastSource, _beforeRun, _lastSlot, _firstSlot,
    _gatheredSlots, _nonceSlot, dummySlot,
    _firstException, _lastException, _traceComputed,
    _remainingComputed⟩ :=
      accepted_whole_program_final_signature_origins
        hashes initial final accepted
  have enough : 22 ≤ beforeCheck.stack.length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp dummySlot
    omega
  apply no_bonus_commitment_of_signature_syntax hashes initial final
    accepted sigSyntax noCommitmentSyntax
  intro reached reachedPrefix
  have same : reached = beforeCheck :=
    Option.some.inj (reachedPrefix.symm.trans beforePrefix)
  subst reached
  have success := matched beforeCheck beforePrefix
  constructor
  · exact matched_final_signature_has_syntax verify sigSyntax
      verifySound beforeCheck.stack enough success 0 (by omega)
  · exact matched_final_signature_has_syntax verify sigSyntax
      verifySound beforeCheck.stack enough success 1 (by omega)

end QSB.FinalBonusSecond
