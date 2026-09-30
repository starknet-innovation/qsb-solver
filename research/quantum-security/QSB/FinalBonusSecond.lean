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
        else dummies[lastIndex - 10]?) := by
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
                              exact ⟨firstIndex, lastIndex, postFirst, postLast,
                                firstRun, bothRun, bounds.1, firstUpper,
                                bounds.2, lastUpper, firstSource, lastSource⟩

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
      (firstIndex lastIndex : Nat) (postFirst postLast : State),
      run hashes (ByteLayout.program.take 840) initial =
        some (State.mk (nextRawFront (boolBytes result)
          gathered dummies commitments ++ tail) outcomes cost) ∧
      PoolShape gathered dummies commitments ∧
      gathered.length = 7 ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) ∧
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
        else dummies[lastIndex - 10]?) := by
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
                    traceCount, distinct, hits⟩ :=
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
                  simp only [signed, Option.bind_some] at suffix
                  rw [signedShape] at suffix
                  obtain ⟨firstIndex, lastIndex, postFirst, postLast,
                    firstRun, bothRun, firstLower, firstUpper,
                    lastLower, lastUpper, firstSource, lastSource⟩ :=
                    accepted_bonus_suffix_source_trace hashes
                      (boolBytes result) gathered' dummies' commitments'
                      tail' pool gatheredCount checkOutcomes
                      (checkCost + 63) final suffix
                  refine ⟨result, gathered', dummies', commitments', tail',
                    checkOutcomes, checkCost + 63, trace, firstIndex,
                    lastIndex, postFirst, postLast, ?_, pool, gatheredCount,
                    traceCount, distinct, hits, firstRun, bothRun,
                    firstLower, firstUpper, lastLower, lastUpper,
                    firstSource, lastSource⟩
                  rw [prefixRun, signedShape]

end QSB.FinalBonusSecond
