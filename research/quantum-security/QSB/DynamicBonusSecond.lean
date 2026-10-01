import QSB.DynamicBonusFirst

/-!
Parameterized stack-source geometry through both generated bonus rolls.
The two cap indices remain bounded only when the stated executable suffix
succeeds; this file isolates the value-independent roll transitions.
-/
namespace QSB.DynamicBonusSecond
open ByteMachine
open FinalSignedLoop
open PoolRollInvariant
open DynamicSignedSource
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem first_dummy_roll_shape (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (seven : gathered.length = 7)
    (j : Nat) (within : j < dummies.length) :
    KeyRolls.rollAt (9 + j)
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail) =
      some (dummies[j] ::
        (gathered ++ [nonce, []]) ++
          dummies.eraseIdx j ++ commitments ++ prior :: tail) := by
  have frontLength : (gathered ++ [nonce, []]).length = 9 := by
    simp [seven]
  have moved := roll_from_middle
    (gathered ++ [nonce, []]) dummies
    (commitments ++ prior :: tail) j within
  simpa [nextRawFrontN, frontLength, List.append_assoc] using moved

/-- A first bonus draw at cap depth 152 selects the first surviving HORS
commitment, leaving all 143 dummy bytes in place. -/
theorem first_commitment_roll_shape (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7) :
    KeyRolls.rollAt 152
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail) =
      some (commitments[0]'(by
        have total := shape.poolCount
        rw [shape.commitmentCount]
        omega) ::
        (gathered ++ [nonce, []] ++ dummies) ++
          commitments.eraseIdx 0 ++ prior :: tail) := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have frontLength :
      (gathered ++ [nonce, []] ++ dummies).length = 152 := by
    simp [seven, dummyLength]
  have within : 0 < commitments.length := by
    rw [shape.commitmentCount, dummyLength]
    omega
  have moved := roll_from_middle
    (gathered ++ [nonce, []] ++ dummies) commitments
    (prior :: tail) 0 within
  simp only [Nat.add_zero] at moved
  rw [frontLength] at moved
  simpa [nextRawFrontN, List.append_assoc] using moved

/-- After the first bonus selects a dummy, the second roll's depths 10–151
address remaining dummies; depth 152 addresses the first HORS commitment. -/
theorem second_source_after_first_dummy (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (j : Nat) (within : j < dummies.length)
    (m : Nat) (lower : 10 ≤ m) (upper : m ≤ 152) :
    (dummies[j] ::
      (gathered ++ [nonce, []]) ++
        dummies.eraseIdx j ++ commitments ++ prior :: tail)[m]? =
      if m < 152 then (dummies.eraseIdx j)[m - 10]?
      else commitments[0]? := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have remainingLength : (dummies.eraseIdx j).length = 142 := by
    rw [List.length_eraseIdx_of_lt within, dummyLength]
  have frontLength : (dummies[j] :: gathered ++ [nonce, []]).length =
      10 := by simp [seven]
  have layout :
      dummies[j] :: (gathered ++ [nonce, []]) ++
          dummies.eraseIdx j ++ commitments ++ prior :: tail =
        (dummies[j] :: gathered ++ [nonce, []]) ++
          (dummies.eraseIdx j ++ (commitments ++ prior :: tail)) := by
    simp [List.append_assoc]
  rw [layout, List.getElem?_append_right (by omega)]
  have offset :
      m - (dummies[j] :: gathered ++ [nonce, []]).length =
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
theorem second_source_after_first_commitment (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (commitmentWithin : 0 < commitments.length)
    (m : Nat) (lower : 10 ≤ m) (upper : m ≤ 152) :
    (commitments[0]'commitmentWithin ::
      (gathered ++ [nonce, []] ++ dummies) ++
        commitments.eraseIdx 0 ++ prior :: tail)[m]? =
      dummies[m - 10]? := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have frontLength :
      (commitments[0]'commitmentWithin ::
        gathered ++ [nonce, []]).length = 10 := by
    simp [seven]
  have layout :
      commitments[0]'commitmentWithin ::
          (gathered ++ [nonce, []] ++ dummies) ++
          commitments.eraseIdx 0 ++ prior :: tail =
        (commitments[0]'commitmentWithin ::
          gathered ++ [nonce, []]) ++
          (dummies ++ (commitments.eraseIdx 0 ++ prior :: tail)) := by
    simp [List.append_assoc]
  rw [layout, List.getElem?_append_right (by omega)]
  have offset :
      m - (commitments[0]'commitmentWithin ::
        gathered ++ [nonce, []]).length = m - 10 := by
    rw [frontLength]
  rw [offset, List.getElem?_append_left (by omega)]

/-- For any first capped bonus choice and any second capped bonus choice,
the second source is a dummy except when the first choice was a dummy and
the second reaches depth 152. In that one branch it is the first surviving
HORS commitment. -/
theorem second_bonus_source_map (nonce prior : Bytes)
    (gathered dummies commitments tail firstStack : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (n m : Nat)
    (firstLower : 9 ≤ n) (firstUpper : n ≤ 152)
    (lastLower : 10 ≤ m) (lastUpper : m ≤ 152)
    (firstRoll : KeyRolls.rollAt n
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail) =
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
    have moved := first_dummy_roll_shape nonce prior gathered dummies
      commitments tail seven j within
    rw [firstDepth] at moved
    have firstShape := Option.some.inj (firstRoll.symm.trans moved)
    subst firstStack
    have source := second_source_after_first_dummy nonce prior gathered
      dummies commitments tail shape seven j within m lastLower lastUpper
    simpa [firstDummy, j] using source
  · have atCap : n = 152 := by omega
    subst n
    have moved := first_commitment_roll_shape nonce prior gathered dummies
      commitments tail shape seven
    have firstShape := Option.some.inj (firstRoll.symm.trans moved)
    subst firstStack
    have commitmentWithin : 0 < commitments.length := by
      rw [shape.commitmentCount]
      have total := shape.poolCount
      omega
    have source := second_source_after_first_commitment nonce prior gathered
      dummies commitments tail shape seven commitmentWithin
      m lastLower lastUpper
    simpa using source

/-- The actual second modeled bonus roll moves the byte given by the
two-branch source map. The fixed deep roll and second cap preserve all
shallow source cells while placing the capped index on top. -/
theorem accepted_second_bonus_source_role (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat)
    (beforeFirst postFirst beforeLast postLast : State)
    (prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
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
    DynamicBonusFirst.accepted_first_bonus_prelude_exact hashes nonce prior
      gathered dummies commitments tail shape seven outcomes cost
      beforeFirst prelude
  have same : rawFirst :: regionFirst =
      retained ::
        (nextRawFrontN nonce prior gathered dummies commitments ++
          tail.eraseIdx 283) := firstShape.symm.trans exactShape
  have regionEq : regionFirst =
      nextRawFrontN nonce prior gathered dummies commitments ++
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
      have sourceMap := second_bonus_source_map nonce prior gathered dummies
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

theorem accepted_bonus_two_roll_shallow_origin (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat)
    (beforeFirst postFirst beforeLast postLast : State)
    (prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
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
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[p]? := by
  obtain ⟨retained, exactShape⟩ :=
    DynamicBonusFirst.accepted_first_bonus_prelude_exact hashes nonce prior
      gathered dummies commitments tail shape seven outcomes cost
      beforeFirst prelude
  have same : rawFirst :: regionFirst =
      retained :: (nextRawFrontN nonce prior gathered dummies commitments ++
        tail.eraseIdx 283) := firstShape.symm.trans exactShape
  have regionEq : regionFirst =
      nextRawFrontN nonce prior gathered dummies commitments ++
        tail.eraseIdx 283 := by
    injection same with _ h
  have frontLength := next_raw_front_length nonce prior gathered dummies
    commitments shape
  have frontWithin : p <
      (nextRawFrontN nonce prior gathered dummies commitments).length := by
    rw [frontLength, seven]
    omega
  have regionSource : regionFirst[p]? =
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[p]? := by
    rw [regionEq]
    rw [List.getElem?_append_left frontWithin,
      List.getElem?_append_left frontWithin]
  cases beforeFirst with
  | mk firstStack firstOutcomes firstCost =>
      change firstStack = rawFirst :: regionFirst at firstShape
      subst firstStack
      have firstKeep := FinalBonusSecond.accepted_roll_shallow_cell hashes rawFirst
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
              have lastKeep := FinalBonusSecond.accepted_roll_shallow_cell hashes rawLast
                regionLast lastOutcomes lastCost postLast m (p + 1)
                (by omega) parsedLast lastRoll
              have bridge : regionLast[p + 1]? = postStack[p + 1]? := by
                simpa using betweenKeep
              simpa [Nat.add_assoc] using
                (lastKeep.trans (bridge.trans
                  (firstKeep.trans regionSource)))


/-- After seven checked signed draws, source depths nine and ten are the
first two surviving nonempty generated dummy signatures, for any nonce. -/
theorem seven_signed_bonus_sources_nonempty (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7) :
    ∃ nine ten : Bytes,
      nine ≠ [] ∧ ten ≠ [] ∧
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[9]? =
        some nine ∧
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[10]? =
        some ten := by
  have enough : 2 ≤ dummies.length := by
    have total := shape.poolCount
    omega
  let nine := dummies[0]'(by omega)
  let ten := dummies[1]'(by omega)
  have nineNonempty : nine ≠ [] := by
    have width := shape.dummyWidth nine (List.getElem_mem (by omega))
    intro empty
    rw [empty] at width
    simp at width
  have tenNonempty : ten ≠ [] := by
    have width := shape.dummyWidth ten (List.getElem_mem (by omega))
    intro empty
    rw [empty] at width
    simp at width
  have frontLength : (gathered ++ [nonce, []]).length = 9 := by
    simp [seven]
  have layout : nextRawFrontN nonce prior gathered dummies commitments ++ tail =
      (gathered ++ [nonce, []]) ++
        (dummies ++ (commitments ++ (prior :: tail))) := by
    simp [nextRawFrontN, List.append_assoc]
  refine ⟨nine, ten, nineNonempty, tenNonempty, ?_, ?_⟩
  · rw [layout]
    rw [List.getElem?_append_right (by omega)]
    simp only [frontLength, Nat.sub_self]
    rw [List.getElem?_append_left (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  · rw [layout]
    rw [List.getElem?_append_right (by omega)]
    have atOne : 10 - (gathered ++ [nonce, []]).length = 1 := by
      omega
    rw [atOne, List.getElem?_append_left (by omega)]
    exact List.getElem?_eq_getElem (by omega)

/-- The nine shallow cells before the bonus prefix are exactly seven
gathered dummy signatures, the parameterized nonce, and the empty dummy. -/
theorem signed_front_origins (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (seven : gathered.length = 7) :
    (∀ p : Nat, p < 7 →
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[p]? =
        gathered[p]?) ∧
    (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[7]? =
      some nonce ∧
    (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[8]? =
      some [] := by
  have layout : nextRawFrontN nonce prior gathered dummies commitments ++ tail =
      gathered ++ (nonce :: [] ::
        (dummies ++ commitments ++ prior :: tail)) := by
    simp [nextRawFrontN, List.append_assoc]
  constructor
  · intro p hp
    rw [layout, List.getElem?_append_left (by omega)]
  constructor
  · rw [layout, List.getElem?_append_right (by omega)]
    simp [seven]
  · rw [layout, List.getElem?_append_right (by omega)]
    simp [seven]

end QSB.DynamicBonusSecond
