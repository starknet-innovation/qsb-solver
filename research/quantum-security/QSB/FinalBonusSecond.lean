import QSB.FinalBonusAccepted

/-!
Source geometry of the second final-round bonus roll after either kind of
first bonus choice. This is a list-level classification over the generated
post-signed pool shape; execution and Core refinement are separate bridges.
-/
namespace QSB.FinalBonusSecond
open ByteMachine
open FinalSignedLoop
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

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

end QSB.FinalBonusSecond
