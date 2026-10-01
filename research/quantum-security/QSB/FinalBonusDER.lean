import QSB.FinalBonusSecond
import QSB.DERSyntax

/-!
Specialize the abstract final-bonus syntax boundary to strict DER syntax for
the literal, disposable Config A lock encoded in `ByteLayout.program`. This
does not quantify over all honestly generated locks or establish Core binary
equivalence to the source-shaped predicate.
-/
namespace QSB.FinalBonusDER
open ByteMachine

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- None of the 150 literal second-round HORS commitments in the generated
test lock has the source-shaped strict DER encoding. This is a property of
this one lock's public bytes, not a distributional security statement. -/
theorem generated_final_commitments_not_der :
    ∀ id : Fin 150,
      DERSyntax.valid (FinalSignedLoop.generatedCommitmentAt id) = false := by
  decide

/-- For this literal test lock, the only remaining bonus-overshoot premise is
that a successful final ten-pair scan uses a verifier whose success implies
the source-shaped DER predicate. Neither that scan premise nor Core binary
refinement follows from `ByteMachine`'s supplied Boolean outcomes. -/
theorem no_final_bonus_overshoot_of_der_matching (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ firstIndex lastIndex : Nat,
      9 ≤ firstIndex ∧ firstIndex < 152 ∧
      10 ≤ lastIndex ∧ lastIndex < 152 := by
  apply FinalBonusSecond.no_bonus_commitment_of_matching_verifier
    hashes initial final accepted verify
    (fun sig => DERSyntax.valid sig = true) verifySound
  · intro id
    simp [generated_final_commitments_not_der id]
  · exact matched

/-- Keep the setup exception visible instead of assuming it away: a matched
modeled run either draws both bonus signatures from surviving dummies or
exhibits an unopened second-round commitment accepted by the strict DER
syntax predicate. The second branch is impossible for this literal fixture,
but is the branch that a dynamic-setup argument must account for. -/
theorem bonus_dummies_or_unopened_der (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    (∃ firstIndex lastIndex : Nat,
      9 ≤ firstIndex ∧ firstIndex < 152 ∧
      10 ≤ lastIndex ∧ lastIndex < 152) ∨
    (∃ (trace : List (Fin 150 × Bytes)) (candidate : Fin 150),
      FinalSignedChain.extractWholeFinal hashes initial = some trace ∧
      trace.length = 7 ∧
      candidate ∉ trace.map Prod.fst ∧
      DERSyntax.valid (FinalSignedLoop.generatedCommitmentAt candidate) =
        true) := by
  obtain ⟨trace, _remainingIds, candidate, firstIndex, lastIndex,
    seven, unopened, firstLower, firstUpper, lastLower, lastUpper,
    traceComputed, _remainingComputed, exception⟩ :=
    FinalBonusSecond.matched_bonus_overshoot_has_unopened_syntax
      hashes initial final accepted verify
      (fun sig => DERSyntax.valid sig = true) verifySound matched
  by_cases firstShallow : firstIndex < 152
  · by_cases lastShallow : lastIndex < 152
    · exact Or.inl ⟨firstIndex, lastIndex, firstLower, firstShallow,
        lastLower, lastShallow⟩
    · have lastCap : lastIndex = 152 := by omega
      exact Or.inr ⟨trace, candidate, traceComputed, seven,
        unopened, exception (Or.inr lastCap)⟩
  · have firstCap : firstIndex = 152 := by omega
    exact Or.inr ⟨trace, candidate, traceComputed, seven,
      unopened, exception (Or.inl firstCap)⟩

end QSB.FinalBonusDER
