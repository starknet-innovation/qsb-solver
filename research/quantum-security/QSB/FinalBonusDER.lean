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

end QSB.FinalBonusDER
