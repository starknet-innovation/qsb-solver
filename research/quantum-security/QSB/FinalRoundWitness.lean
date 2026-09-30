import QSB.FinalBonusIndices
import QSB.Attack

/-!
Turn the seven byte-model opening pairs and two disjoint bonus positions into
the abstract final-round shape and valid-opening interface. The lookup of
opening bytes is executable on the trace. This module does not supply the
transaction-bound nonce key, the hash-to-DER puzzle, or a Core transaction
extractor.
-/
namespace QSB.FinalRoundWitness
open ByteMachine
open FinalSignedLoop

def openingAt : List (Fin 150 × Bytes) → Fin 150 → Option Bytes
  | [], _ => none
  | (j, value) :: rest, i =>
      if i = j then some value else openingAt rest i

theorem openingAt_sound (trace : List (Fin 150 × Bytes))
    (i : Fin 150) (value : Bytes)
    (found : openingAt trace i = some value) :
    (i, value) ∈ trace := by
  induction trace with
  | nil => simp [openingAt] at found
  | cons pair rest ih =>
      rcases pair with ⟨j, cell⟩
      by_cases same : i = j
      · simp [openingAt, same] at found
        subst i
        simp [found]
      · simp [openingAt, same] at found
        exact List.mem_cons_of_mem _ (ih found)

theorem openingAt_complete (trace : List (Fin 150 × Bytes))
    (i : Fin 150) (present : i ∈ trace.map Prod.fst) :
    ∃ value, openingAt trace i = some value := by
  induction trace with
  | nil => simp at present
  | cons pair rest ih =>
      rcases pair with ⟨j, cell⟩
      by_cases same : i = j
      · exact ⟨cell, by simp [openingAt, same]⟩
      · have tail : i ∈ rest.map Prod.fst := by
          simpa [same, eq_comm] using present
        obtain ⟨value, found⟩ := ih tail
        exact ⟨value, by simp [openingAt, same, found]⟩

def traceValue (trace : List (Fin 150 × Bytes)) (i : Fin 150) : Bytes :=
  (openingAt trace i).getD []

def witnessFromTrace (trace : List (Fin 150 × Bytes))
    (a b : Fin 150) (key : Bytes) : RoundWitness (Fin 150) Bytes Bytes :=
  { signed := (trace.map Prod.fst).toFinset
    bonus := {a, b}
    opening := fun i _ => traceValue trace i
    key := key }

/-- The trace-to-abstract bridge retains real opening bytes and the exact
seven-plus-two shape; it makes no claim about the arbitrary `key` argument. -/
theorem witnessFromTrace_shape_and_openings
    (hashes : Hashes) (trace : List (Fin 150 × Bytes))
    (a b : Fin 150) (key : Bytes)
    (seven : trace.length = 7)
    (distinct : (a :: b :: trace.map Prod.fst).Nodup)
    (hits : ∀ p ∈ trace, hashes.h160 p.2 = generatedCommitmentAt p.1) :
    FinalRoundShape (witnessFromTrace trace a b key) ∧
    OpeningsValid hashes.h160 generatedCommitmentAt
      (witnessFromTrace trace a b key).signed
      (witnessFromTrace trace a b key).opening := by
  classical
  obtain ⟨aAbsent, restDistinct⟩ := List.nodup_cons.mp distinct
  obtain ⟨bAbsent, traceDistinct⟩ := List.nodup_cons.mp restDistinct
  have aNeB : a ≠ b := by
    intro same
    exact aAbsent (by simp [same])
  have aNotTrace : a ∉ trace.map Prod.fst := by
    intro h
    exact aAbsent (by simp [h])
  have signedCard : (trace.map Prod.fst).toFinset.card = 7 := by
    rw [List.toFinset_card_of_nodup traceDistinct]
    simpa using seven
  have bonusCard : ({a, b} : Finset (Fin 150)).card = 2 := by
    simp [aNeB]
  have disjoint : Disjoint (trace.map Prod.fst).toFinset
      ({a, b} : Finset (Fin 150)) := by
    apply Finset.disjoint_left.mpr
    intro i inTrace inBonus
    simp only [Finset.mem_insert, Finset.mem_singleton] at inBonus
    rcases inBonus with rfl | rfl
    · exact aNotTrace (List.mem_toFinset.mp inTrace)
    · exact bAbsent (List.mem_toFinset.mp inTrace)
  constructor
  · exact ⟨signedCard, bonusCard, disjoint⟩
  · intro i inSigned
    have present : i ∈ trace.map Prod.fst :=
      List.mem_toFinset.mp inSigned
    obtain ⟨value, found⟩ := openingAt_complete trace i present
    have inTrace := openingAt_sound trace i value found
    have matched := hits (i, value) inTrace
    simpa [witnessFromTrace, traceValue, found] using matched

/-- The literal full byte-model run supplies the shape and opening-equality
fields of the reduction's `RoundWitness`. The caller supplies `key` freely:
this theorem establishes no nonce binding, puzzle hit, transaction extractor,
or Bitcoin Core acceptance. -/
theorem matched_run_shape_and_openings (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool)
    (verifySound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true)
    (key : Bytes) :
    ∃ w : RoundWitness (Fin 150) Bytes Bytes,
      w.key = key ∧ FinalRoundShape w ∧
      OpeningsValid hashes.h160 generatedCommitmentAt w.signed w.opening := by
  obtain ⟨trace, a, b, beforeCheck,
    _reached, _firstSlot, _lastSlot, _signedSlots,
    _nonceSlot, _dummySlot, seven, hits,
    _different, _aUnopened, _bUnopened, distinct, _nine⟩ :=
      FinalBonusIndices.matched_full_run_nine_positions_der
        hashes initial final accepted verify verifySound matched
  refine ⟨witnessFromTrace trace a b key, rfl, ?_⟩
  exact witnessFromTrace_shape_and_openings hashes trace a b key
    seven distinct hits

/-- The round-witness bridge with Core's empty-signature encoding exception
made explicit. It still requires an external refinement proving that the
reached real CHECKMULTISIG is the stated successful scan. -/
theorem matched_run_shape_and_openings_verify_all (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (verify : Bytes → Bytes → Bool)
    (verifyNonempty : ∀ sig key, verify sig key = true → sig ≠ [])
    (verifyEncoding : ∀ sig key, verify sig key = true →
      DERSyntax.verifyAllEncoding sig = true)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true)
    (key : Bytes) :
    ∃ w : RoundWitness (Fin 150) Bytes Bytes,
      w.key = key ∧ FinalRoundShape w ∧
      OpeningsValid hashes.h160 generatedCommitmentAt w.signed w.opening := by
  apply matched_run_shape_and_openings hashes initial final accepted verify
    ?_ matched key
  intro sig pub success
  have encoded := verifyEncoding sig pub success
  rw [DERSyntax.verifyAllEncoding_nonempty sig
    (verifyNonempty sig pub success)] at encoded
  exact encoded

end QSB.FinalRoundWitness
