import QSB.FinalBonusSecond
import QSB.DERSyntax
import QSB.DERHeaderBound

/-!
Specialize the abstract final-bonus syntax boundary to strict DER syntax.
Generic aligned-pool theorems allow arbitrary commitment bytes under explicit
reached-stack premises; literal-lock theorems then use the disposable Config A
bytes encoded in `ByteLayout.program`. Neither proves that every honestly
generated lock supplies those premises or establishes Core binary equivalence.
-/
namespace QSB.FinalBonusDER
open ByteMachine

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- At any reached final-scan boundary with an aligned 150-position residual
pool, arbitrary dynamic commitment bytes satisfy this exact alternative. The
structural alignment and signature-slot equations remain premises; this does
not assert that a generated dynamic lock or compiled Core supplies them. -/
theorem aligned_bonus_dummies_or_unopened_der
    (commitmentAt : Fin 150 → Bytes)
    (trace : List (Fin 150 × Bytes))
    (remainingIds : List (Fin 150)) (commitments stack : List Bytes)
    (firstIndex lastIndex : Nat)
    (aligned : commitments = remainingIds.map commitmentAt)
    (permutation : List.Perm (trace.map Prod.fst ++ remainingIds)
      (List.finRange 150))
    (nonempty : 0 < commitments.length)
    (firstLower : 9 ≤ firstIndex) (firstUpper : firstIndex ≤ 152)
    (lastLower : 10 ≤ lastIndex) (lastUpper : lastIndex ≤ 152)
    (firstCap : firstIndex = 152 → stack[13]? = commitments[0]?)
    (lastCap : firstIndex < 152 ∧ lastIndex = 152 →
      stack[12]? = commitments[0]?)
    (enough : 22 ≤ stack.length)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : Multisig.matchSigs verify
      ((stack.drop 12).take 10) ((stack.drop 1).take 10) = true) :
    (9 ≤ firstIndex ∧ firstIndex < 152 ∧
      10 ≤ lastIndex ∧ lastIndex < 152) ∨
    (∃ candidate : Fin 150,
      candidate ∉ trace.map Prod.fst ∧
      DERSyntax.valid (commitmentAt candidate) = true) := by
  by_cases firstShallow : firstIndex < 152
  · by_cases lastShallow : lastIndex < 152
    · exact Or.inl ⟨firstLower, firstShallow,
        lastLower, lastShallow⟩
    · have lastAtCap : lastIndex = 152 := by omega
      exact Or.inr <|
        FinalBonusSecond.matched_bonus_boundary_has_unopened_syntax
          commitmentAt trace remainingIds commitments stack
          firstIndex lastIndex aligned permutation nonempty firstUpper
          firstCap lastCap enough verify
          (fun sig => DERSyntax.valid sig = true) verifySound matched
          (Or.inr lastAtCap)
  · have firstAtCap : firstIndex = 152 := by omega
    exact Or.inr <|
      FinalBonusSecond.matched_bonus_boundary_has_unopened_syntax
        commitmentAt trace remainingIds commitments stack
        firstIndex lastIndex aligned permutation nonempty firstUpper
        firstCap lastCap enough verify
        (fun sig => DERSyntax.valid sig = true) verifySound matched
        (Or.inl firstAtCap)

/-- A bonus overshoot in an aligned dynamic setup implies an actual hit in
the same twenty-byte-output function used to form all commitments. Combined
with `DERHeaderBound.final_bonus_uniform_setup_count`, this identifies the
setup event to charge, conditional on the reached geometry and matched scan.
It does not prove those premises for Core-accepted dynamic locks. -/
theorem aligned_bonus_overshoot_uniform_setup_hit
    {Ξ X : Type*} (source : Fin 150 → Ξ → X)
    (R : X → (Fin 20 → UInt8)) (ξ : Ξ)
    (trace : List (Fin 150 × Bytes))
    (remainingIds : List (Fin 150)) (commitments stack : List Bytes)
    (firstIndex lastIndex : Nat)
    (aligned : commitments = remainingIds.map
      (fun i => List.ofFn (R (source i ξ))))
    (permutation : List.Perm (trace.map Prod.fst ++ remainingIds)
      (List.finRange 150))
    (nonempty : 0 < commitments.length)
    (firstUpper : firstIndex ≤ 152)
    (firstCap : firstIndex = 152 → stack[13]? = commitments[0]?)
    (lastCap : firstIndex < 152 ∧ lastIndex = 152 →
      stack[12]? = commitments[0]?)
    (enough : 22 ≤ stack.length)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : Multisig.matchSigs verify
      ((stack.drop 12).take 10) ((stack.drop 1).take 10) = true)
    (overshoot : firstIndex = 152 ∨ lastIndex = 152) :
    ∃ i : Fin 150,
      i ∉ trace.map Prod.fst ∧
      DERSyntax.valid (List.ofFn (R (source i ξ))) = true := by
  exact FinalBonusSecond.matched_bonus_boundary_has_unopened_syntax
    (fun i => List.ofFn (R (source i ξ))) trace remainingIds
    commitments stack firstIndex lastIndex aligned permutation nonempty
    firstUpper firstCap lastCap enough verify
    (fun sig => DERSyntax.valid sig = true) verifySound matched overshoot

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
