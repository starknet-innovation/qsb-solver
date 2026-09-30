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
          simpa [Int.toNat_of_nonneg (by omega : 0 ≤ value)] using parsed

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
      regionFirst[10]? = some ten := by
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
              refine ⟨retained, region, shape, ?_, ?_⟩
              · simpa using keepNine.trans sourceNine
              · simpa using keepTen.trans sourceTen

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
      9 ≤ firstIndex ∧ 10 ≤ lastIndex := by
  rw [generated_bonus_suffix, run_append] at accepted
  cases prelude : run hashes firstBonusPrelude
      (State.mk stack outcomes cost) with
  | none => simp [prelude] at accepted
  | some beforeFirst =>
      obtain ⟨rawFirst, regionFirst, firstShape, firstNine, firstTen⟩ :=
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
                              exact ⟨firstIndex, lastIndex, bounds⟩

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
      9 ≤ firstIndex ∧ 10 ≤ lastIndex := by
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
                    traceCount, distinct, hits⟩ :=
                    accepted_all_signed_blocks hashes result tail
                      checkOutcomes checkCost afterSigned signed
                  simp only [signed, Option.bind_some] at suffix
                  rw [signedShape] at suffix
                  obtain ⟨nine, ten, nineNonempty, tenNonempty,
                      atNine, atTen⟩ :=
                    seven_signed_bonus_sources_nonempty
                      (boolBytes result) gathered' dummies' commitments'
                      tail' pool gatheredCount
                  obtain ⟨firstIndex, lastIndex, firstBound, lastBound⟩ :=
                    accepted_bonus_suffix_index_bounds hashes
                      (nextRawFront (boolBytes result)
                        gathered' dummies' commitments' ++ tail')
                      checkOutcomes (checkCost + 63) final nine ten
                      nineNonempty tenNonempty atNine atTen suffix
                  exact ⟨trace, firstIndex, lastIndex, traceCount,
                    distinct, hits, firstBound, lastBound⟩

end QSB.FinalBonusAccepted
