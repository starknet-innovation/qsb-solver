import QSB.DynamicSignedChain
import QSB.FinalBonusSecond

/-!
The first bonus draw after seven dynamically parameterized signed blocks.
The bonus opcodes remain the literal generated suffix, while the second-round
nonce and commitments are arbitrary bytes satisfying the pool-width premise.
-/
namespace QSB.DynamicBonusFirst
open ByteMachine
open FinalSignedLoop
open PoolRollInvariant
open DynamicSignedSource
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem accepted_first_bonus_fixed_raw_pair (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push [0x43, 0x02], .roll]
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
        outcomes cost) = some after) :
    ∃ enough : 283 < tail.length,
      after = State.mk
        (tail[283] :: nextRawFrontN nonce prior gathered dummies commitments ++
          tail.eraseIdx 283) outcomes (cost + 1) := by
  have frontLength := next_raw_front_length nonce prior gathered dummies
    commitments shape
  have depthNat :
      (nextRawFrontN nonce prior gathered dummies commitments).length + 283 =
        579 := by
    rw [frontLength, seven]
  have parsed : ByteIndex.parseScriptNum [0x43, 0x02] =
      some (Int.ofNat
        ((nextRawFrontN nonce prior gathered dummies commitments).length +
          283)) := by
    simpa only [depthNat] using
      ByteBonusBetween.between_roll_index_decode
  exact accepted_push_roll_tail_shape hashes [0x43, 0x02]
    (nextRawFrontN nonce prior gathered dummies commitments) tail
    outcomes cost after 283 parsed accepted

theorem accepted_first_bonus_prelude_exact (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
        outcomes cost) = some after) :
    ∃ retained : Bytes,
      after.stack = retained ::
        (nextRawFrontN nonce prior gathered dummies commitments ++
          tail.eraseIdx 283) := by
  rw [FinalBonusAccepted.generated_first_bonus_prelude] at accepted
  have split : ([.push [0x43, 0x02], .roll,
      .push [0x98, 0x00], .min] : List Op) =
      [.push [0x43, 0x02], .roll] ++
        [.push [0x98, 0x00], .min] := rfl
  rw [split, run_append] at accepted
  cases fixedRun : run hashes [.push [0x43, 0x02], .roll]
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
        outcomes cost) with
  | none => simp [fixedRun] at accepted
  | some afterFixed =>
      obtain ⟨enough, fixedShape⟩ :=
        accepted_first_bonus_fixed_raw_pair hashes nonce prior gathered
          dummies commitments tail shape seven outcomes cost afterFixed
          fixedRun
      simp only [fixedRun, Option.bind_some] at accepted
      rw [fixedShape] at accepted
      exact FinalBonusAccepted.accepted_cap_pair_stack hashes tail[283]
        (nextRawFrontN nonce prior gathered dummies commitments ++
          tail.eraseIdx 283) outcomes (cost + 1) after accepted

theorem first_bonus_source_map (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (n : Nat) (lower : 9 ≤ n) (upper : n ≤ 152) :
    (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[n]? =
      if n < 152 then dummies[n - 9]?
      else commitments[0]? := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have commitmentLength : commitments.length = 143 := by
    rw [shape.commitmentCount, dummyLength]
  have frontLength : (gathered ++ [nonce, []]).length = 9 := by
    simp [seven]
  have layout : nextRawFrontN nonce prior gathered dummies commitments ++ tail =
      (gathered ++ [nonce, []]) ++
        (dummies ++ (commitments ++ (prior :: tail))) := by
    simp [nextRawFrontN, List.append_assoc]
  rw [layout, List.getElem?_append_right (by omega)]
  have offset : n - (gathered ++ [nonce, []]).length = n - 9 := by
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
    exact (List.getElem?_eq_getElem
      (by omega : 0 < commitments.length)).symm

theorem accepted_first_bonus_source_role (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat)
    (beforeFirst postFirst : State)
    (prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
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
    accepted_first_bonus_prelude_exact hashes nonce prior gathered dummies
      commitments tail shape seven outcomes cost beforeFirst prelude
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
      obtain ⟨selected, source, postShape⟩ :=
        FinalBonusAccepted.accepted_roll_selected_source hashes rawFirst
          regionFirst firstOutcomes firstCost postFirst n parsed firstRoll
      rw [regionEq] at source
      have mapped := first_bonus_source_map nonce prior gathered dummies
        commitments (tail.eraseIdx 283) shape seven n lower upper
      rw [source] at mapped
      rw [postShape]
      exact mapped

/-- A successful first bonus segment reaches its actual selected byte. If
the decoded index is at least nine, the selected byte is either a surviving
dummy or the first still-unopened commitment. Later signature checks are
needed to exclude indices below nine. -/
theorem accepted_first_bonus_reached (hashes : Hashes)
    (nonce prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (seven : gathered.length = 7)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes FinalBonusSecond.firstBonusOps
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
        outcomes cost) = some final) :
    ∃ n : Nat, n ≤ 152 ∧
      (9 ≤ n → final.stack.head? =
        if n < 152 then dummies[n - 9]?
        else commitments[0]?) := by
  have dummyLength : dummies.length = 143 := by
    have total := shape.poolCount
    omega
  have sourceNine :
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[9]? =
        some dummies[0] := by
    have mapped := first_bonus_source_map nonce prior gathered dummies
      commitments tail shape seven 9 (by omega) (by omega)
    simpa [List.getElem?_eq_getElem (by omega : 0 < dummies.length)]
      using mapped
  have sourceTen :
      (nextRawFrontN nonce prior gathered dummies commitments ++ tail)[10]? =
        some dummies[1] := by
    have mapped := first_bonus_source_map nonce prior gathered dummies
      commitments tail shape seven 10 (by omega) (by omega)
    simpa [List.getElem?_eq_getElem (by omega : 1 < dummies.length)]
      using mapped
  change run hashes (FinalBonusAccepted.firstBonusPrelude ++ [.roll])
    (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
      outcomes cost) = some final at accepted
  rw [run_append] at accepted
  cases prelude : run hashes FinalBonusAccepted.firstBonusPrelude
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
        outcomes cost) with
  | none => simp [prelude] at accepted
  | some beforeFirst =>
      obtain ⟨rawFirst, regionFirst, firstShape, _, _, cap⟩ :=
        FinalBonusAccepted.accepted_first_bonus_prelude_sources hashes
          (nextRawFrontN nonce prior gathered dummies commitments ++ tail)
          outcomes cost beforeFirst dummies[0] dummies[1]
          sourceNine sourceTen prelude
      simp only [prelude, Option.bind_some] at accepted
      cases beforeFirst with
      | mk firstStack firstOutcomes firstCost =>
          change firstStack = rawFirst :: regionFirst at firstShape
          subst firstStack
          obtain ⟨n, parsed⟩ :=
            FinalBonusAccepted.accepted_roll_index hashes rawFirst
              regionFirst firstOutcomes firstCost final accepted
          refine ⟨n, cap n parsed, ?_⟩
          intro lower
          exact accepted_first_bonus_source_role hashes nonce prior
            gathered dummies commitments tail shape seven outcomes cost
            (State.mk (rawFirst :: regionFirst) firstOutcomes firstCost)
            final prelude rawFirst regionFirst rfl n lower (cap n parsed)
            parsed accepted

/-- The arbitrary data pushes, seven signed blocks, and first bonus segment
form one executable transition. The signed openings and residual pool come
from this same run; the bonus source is classified whenever its decoded
index is at least nine. -/
theorem accepted_data_signed_first_bonus (hashes : Hashes)
    (nonce prior : Bytes) (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes
      (DynamicSignedChain.dataAndSignedProgram nonce commitmentAt ++
        FinalBonusSecond.firstBonusOps)
      (State.mk (prior :: tail) outcomes cost) = some final) :
    ∃ (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150))
      (dummies commitments : List Bytes)
      (candidate : Fin 150) (n : Nat),
      DynamicFinalInit.AlignedPool commitmentAt remainingIds
        dummies commitments ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ remainingIds)
        (List.finRange 150) ∧
      FinalSignedChain.extractOrdered (List.finRange 7)
        (List.finRange 150) 0 tail = some trace ∧
      candidate ∉ trace.map Prod.fst ∧
      commitments[0]? = some (commitmentAt candidate) ∧
      n ≤ 152 ∧
      (9 ≤ n → final.stack.head? =
        if n < 152 then dummies[n - 9]?
        else commitments[0]?) ∧
      (n = 152 → final.stack.head? =
        some (commitmentAt candidate)) := by
  rw [run_append] at accepted
  cases signedRun : run hashes
      (DynamicSignedChain.dataAndSignedProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) with
  | none => simp [signedRun] at accepted
  | some afterSigned =>
      simp only [signedRun, Option.bind_some] at accepted
      unfold DynamicSignedChain.dataAndSignedProgram at signedRun
      rw [run_append] at signedRun
      cases dataRun : run hashes (DynamicFinalInit.dataOps nonce commitmentAt)
          (State.mk (prior :: tail) outcomes cost) with
      | none => simp [dataRun] at signedRun
      | some afterData =>
          have dataShape := DynamicFinalInit.accepted_data_shape hashes
            nonce commitmentAt (prior :: tail) outcomes cost afterData dataRun
          simp only [dataRun, Option.bind_some] at signedRun
          rw [dataShape] at signedRun
          obtain ⟨remainingIds, gathered, dummies, commitments, tail',
              trace, signedShape, poolShape, aligned, gatheredCount,
              traceCount, traceExtract, _remainingExtract, distinct,
              hits, permutation, _gatheredTrace⟩ :=
            DynamicSignedChain.accepted_all_signed_blocks hashes
              commitmentAt nonce prior width priorWrong tail outcomes cost
              afterSigned signedRun
          rw [signedShape] at accepted
          obtain ⟨n, upper, source⟩ :=
            accepted_first_bonus_reached hashes nonce prior gathered
              dummies commitments tail' poolShape gatheredCount
              outcomes (cost + 63) final accepted
          have nonempty : 0 < commitments.length := by
            rw [poolShape.commitmentCount]
            have dummyCount := poolShape.poolCount
            omega
          obtain ⟨candidate, candidateSource, unopened⟩ :=
            FinalBonusSecond.first_remaining_commitment_unopened_of_map
              commitmentAt trace remainingIds commitments
              aligned.commitmentMap permutation nonempty
          exact ⟨trace, remainingIds, dummies, commitments,
            candidate, n, aligned, traceCount, distinct, hits,
            permutation, traceExtract, unopened, candidateSource,
            upper, source, by
              intro capped
              have selected := source (by omega : 9 ≤ n)
              simpa [capped, candidateSource] using selected⟩

end QSB.DynamicBonusFirst
