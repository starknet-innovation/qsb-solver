import QSB.DynamicBonusIndices
import QSB.DERHeaderBound

/-!
Compose the parameterized final-round extraction result with the finite
uniform-setup count. This is a setup-event bound, not an unauthorized-spend
or quantum-query bound. The same sampled twenty-byte function is used for all
150 commitment values, and its input-selecting material is independent of it.
-/
namespace QSB.DynamicBonusSetup
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def commitmentAt {Ξ X : Type*} (source : Fin 150 → Ξ → X)
    (p : Ξ × (X → (Fin 20 → UInt8))) (i : Fin 150) : Bytes :=
  List.ofFn (p.2 (source i p.1))

def BadDERSetup {Ξ X : Type*} (source : Fin 150 → Ξ → X)
    (p : Ξ × (X → (Fin 20 → UInt8))) : Prop :=
  ∃ i : Fin 150, DERSyntax.valid (commitmentAt source p i) = true

/-- Outside the bad setup event, any successful modeled final round with a
matched DER-sound scan yields nine distinct original positions. The witness
and signature outcomes may depend on the sampled function; only the setup
input-selection material must be independent of that function for the count
below. -/
theorem good_setup_nine_positions {Ξ X : Type*}
    (source : Fin 150 → Ξ → X)
    (p : Ξ × (X → (Fin 20 → UInt8)))
    (good : ¬BadDERSetup source p)
    (hashes : Hashes) (nonce prior : Bytes)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes
      (DynamicFinalInit.finalRoundProgram nonce (commitmentAt source p))
      (State.mk (prior :: tail) outcomes cost) = some final)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes
        (DynamicBonusChain.finalCheckPrefix nonce (commitmentAt source p))
        (State.mk (prior :: tail) outcomes cost) = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : State),
      run hashes
        (DynamicBonusChain.finalCheckPrefix nonce (commitmentAt source p))
        (State.mk (prior :: tail) outcomes cost) = some beforeCheck ∧
      beforeCheck.stack[13]? = some (FinalSignedLoop.generatedDummyAt a) ∧
      beforeCheck.stack[12]? = some (FinalSignedLoop.generatedDummyAt b) ∧
      trace.length = 7 ∧
      (∀ opening ∈ trace,
        hashes.h160 opening.2 = commitmentAt source p opening.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
      FinalSignedChain.extractOrdered (List.finRange 7)
        (List.finRange 150) 0 tail = some trace := by
  have width : ∀ i, (commitmentAt source p i).length = 20 := by
    intro i
    simp [commitmentAt]
  have noDER : ∀ id : Fin 150,
      DERSyntax.valid (commitmentAt source p id) = false := by
    intro id
    cases h : DERSyntax.valid (commitmentAt source p id) with
    | false => rfl
    | true =>
        exact False.elim (good ⟨id, h⟩)
  obtain ⟨trace, a, b, beforeCheck, checkRun, firstAt, lastAt,
      _signedSlots, _nonceSlot, _dummySlot, traceCount, hits,
      _different, _aUnopened, _bUnopened, distinct, nine,
      traceExtract⟩ :=
    DynamicBonusIndices.matched_dynamic_nine_positions hashes nonce prior
      (commitmentAt source p) width priorWrong tail outcomes cost final
      accepted verify verifySound noDER matched
  exact ⟨trace, a, b, beforeCheck, checkRun, firstAt, lastAt,
    traceCount, hits, distinct, nine, traceExtract⟩

/-- A shared uniform twenty-byte-output setup function assigns a DER-shaped
value to at least one of the 150 final-round commitment positions in at most
`150·12/256^6` of the setup product space. This bound covers every failure
of the good-setup premise above, even when the later witness is adaptive to
the sampled setup. -/
theorem bad_der_setup_count {Ξ X : Type*}
    [Fintype Ξ] [DecidableEq Ξ] [Fintype X] [DecidableEq X]
    (source : Fin 150 → Ξ → X)
    [DecidablePred (BadDERSetup source)] :
    ((Finset.univ.filter fun p : Ξ × (X → (Fin 20 → UInt8)) =>
      BadDERSetup source p).card) *
        Fintype.card (Fin 20 → UInt8) ≤
      150 * (Fintype.card (Ξ × (X → (Fin 20 → UInt8))) *
        (12 * 256 ^ 14)) := by
  classical
  simpa only [BadDERSetup, commitmentAt] using
    DERHeaderBound.final_bonus_uniform_setup_count source

end QSB.DynamicBonusSetup
