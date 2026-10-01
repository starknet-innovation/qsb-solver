import QSB.DynamicBonusChain
import QSB.FinalBonusDER

/-!
A parameterized byte-model extraction boundary for the final bonus scan.
The final matching-verifier premise is explicit. If a bonus draw reaches the
first surviving commitment, the same run exposes an unopened commitment whose
bytes pass strict DER syntax. This does not prove Core matching or the joint
quantum probability bound.
-/
namespace QSB.DynamicBonusDER
open ByteMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem accepted_dynamic_bonus_der_alternative (hashes : Hashes)
    (nonce prior : Bytes) (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes
      (DynamicFinalInit.finalRoundProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) = some final)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes (DynamicBonusChain.finalCheckPrefix nonce commitmentAt)
        (State.mk (prior :: tail) outcomes cost) = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (trace : List (Fin 150 × Bytes))
      (firstIndex lastIndex : Nat),
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      FinalSignedChain.extractOrdered (List.finRange 7)
        (List.finRange 150) 0 tail = some trace ∧
      ((9 ≤ firstIndex ∧ firstIndex < 152 ∧
          10 ≤ lastIndex ∧ lastIndex < 152) ∨
        (∃ candidate : Fin 150,
          candidate ∉ trace.map Prod.fst ∧
          DERSyntax.valid (commitmentAt candidate) = true)) := by
  obtain ⟨trace, remainingIds, gathered, dummies, commitments,
      candidate, firstIndex, lastIndex, beforeCheck, checkRun,
      aligned, permutation, traceCount, distinct, hits, traceExtract,
      _gatheredTrace, _unopened, candidateSource,
      firstLower, firstUpper, lastLower, lastUpper,
      _lastSlot, _firstSlot, _gatheredSlots, _nonceSlot, dummySlot,
      firstCap, lastCap⟩ :=
    DynamicBonusChain.accepted_data_signed_final_signature_origins
      hashes nonce prior commitmentAt width priorWrong tail outcomes cost
      final accepted
  have nonempty : 0 < commitments.length := by
    obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp candidateSource
    exact within
  have enough : 22 ≤ beforeCheck.stack.length := by
    obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp dummySlot
    omega
  have firstCapPool : firstIndex = 152 →
      beforeCheck.stack[13]? = commitments[0]? := by
    intro capped
    exact (firstCap capped).trans candidateSource.symm
  have lastCapPool : firstIndex < 152 ∧ lastIndex = 152 →
      beforeCheck.stack[12]? = commitments[0]? := by
    intro capped
    exact (lastCap capped).trans candidateSource.symm
  have alternative :=
    FinalBonusDER.aligned_bonus_dummies_or_unopened_der
      commitmentAt trace remainingIds commitments beforeCheck.stack
      firstIndex lastIndex aligned.commitmentMap permutation nonempty
      firstLower firstUpper lastLower lastUpper firstCapPool lastCapPool
      enough verify verifySound (matched beforeCheck checkRun)
  exact ⟨trace, firstIndex, lastIndex, traceCount, distinct, hits,
    traceExtract, alternative⟩

end QSB.DynamicBonusDER
