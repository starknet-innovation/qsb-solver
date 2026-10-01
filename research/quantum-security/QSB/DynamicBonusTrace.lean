import QSB.DynamicBonusSecond

/-!
Both generated bonus draws after a dynamically parameterized signed pool.
Successful execution of the complete literal suffix supplies the lower bounds
on both capped indices; those bounds identify the source roles of actual
reached roll states. The nonce and commitment bytes remain arbitrary.
-/
namespace QSB.DynamicBonusTrace
open ByteMachine
open FinalSignedLoop
open PoolRollInvariant
open DynamicSignedSource
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem accepted_bonus_suffix_source_trace (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (ByteLayout.program.drop 840)
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
        outcomes cost) = some final) :
    ∃ (firstIndex lastIndex : Nat) (postFirst postLast : State),
      run hashes FinalBonusSecond.firstBonusOps
        (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
          outcomes cost) = some postFirst ∧
      run hashes FinalBonusSecond.bothBonusOps
        (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
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
        (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[p]?) := by
  obtain ⟨nine, ten, nineNonempty, tenNonempty,
      sourceNine, sourceTen⟩ :=
    DynamicBonusSecond.seven_signed_bonus_sources_nonempty nonce prior
      gathered dummies commitments tail shape seven
  rw [FinalBonusAccepted.generated_bonus_suffix, run_append] at accepted
  cases prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
        outcomes cost) with
  | none => simp [prelude] at accepted
  | some beforeFirst =>
      obtain ⟨rawFirst, regionFirst, firstShape, firstNine,
          firstTen, firstCap⟩ :=
        FinalBonusAccepted.accepted_first_bonus_prelude_sources hashes
          (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
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
                                DynamicBonusFirst.accepted_first_bonus_source_role
                                  hashes nonce prior gathered dummies commitments
                                  tail shape seven outcomes cost
                                  (State.mk (rawFirst :: regionFirst)
                                    firstOutcomes firstCost)
                                  postFirst prelude rawFirst regionFirst rfl
                                  firstIndex bounds.1 firstUpper
                                  decodedFirst firstRoll
                              have lastSource :=
                                DynamicBonusSecond.accepted_second_bonus_source_role hashes nonce prior
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
                              have firstRun : run hashes FinalBonusSecond.firstBonusOps
                                  (State.mk (nextRawFrontN nonce prior gathered
                                    dummies commitments ++ tail) outcomes cost) =
                                    some postFirst := by
                                simp [FinalBonusSecond.firstBonusOps, run_append, prelude,
                                  firstRoll]
                              have bothRun : run hashes FinalBonusSecond.bothBonusOps
                                  (State.mk (nextRawFrontN nonce prior gathered
                                    dummies commitments ++ tail) outcomes cost) =
                                    some postLast := by
                                simp [FinalBonusSecond.bothBonusOps, run_append, firstRun,
                                  between, lastRoll]
                              have firstCarried : postLast.stack[1]? =
                                  postFirst.stack.head? := by
                                simpa only [List.head?_eq_getElem?] using
                                  (FinalBonusSecond.accepted_second_bonus_preserves_shallow
                                  hashes postFirst
                                  (State.mk (rawLast :: regionLast)
                                    lastOutcomes lastCost)
                                  postLast between rawLast regionLast rfl
                                  lastIndex 0 (by omega) (by omega)
                                  decodedLast lastRoll)
                              have shallow : ∀ p : Nat, p ≤ 8 →
                                  postLast.stack[p + 2]? =
                                    (nextRawFrontN nonce prior gathered dummies
                                      commitments ++ tail)[p]? := by
                                intro p hp
                                exact DynamicBonusSecond.accepted_bonus_two_roll_shallow_origin
                                  hashes nonce prior gathered dummies commitments
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

end QSB.DynamicBonusTrace

