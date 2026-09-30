import QSB.FindAndDelete
import QSB.FinalBonusIndices

/-!
Connect the ten reached final signature slots in a successful byte-model run
to the ten serialized signature patterns removed by the source-shaped
FindAndDelete model. The successful verifier remains an explicit premise;
there is no claim here about arbitrary Bitcoin Core transactions.
-/
namespace QSB.FinalScriptCode
open ByteMachine
open FinalSignedLoop
open ScriptCodeSelection
open EncodedScript

def reachedSignatures (stack : List Bytes) : List Bytes :=
  (stack.drop 12).take 10

def expectedSignatures (trace : List (Fin 150 × Bytes))
    (a b : Fin 150) : List Bytes :=
  [generatedDummyAt b, generatedDummyAt a] ++
    (trace.map (fun p => generatedDummyAt p.1)).reverse ++
    [PoolRollInvariant.finalNonce]

theorem reached_signatures_exact (stack : List Bytes)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
    (h12 : stack[12]? = some (generatedDummyAt b))
    (h13 : stack[13]? = some (generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some PoolRollInvariant.finalNonce)
    (seven : trace.length = 7) :
    reachedSignatures stack = expectedSignatures trace a b := by
  apply List.ext_getElem?
  intro i
  by_cases within : i < 10
  · interval_cases i
    all_goals simp [reachedSignatures, expectedSignatures,
      List.getElem?_drop, h12, h13, h21, signed, seven]
  · have expectedLength : (expectedSignatures trace a b).length = 10 := by
      simp [expectedSignatures, seven]
    have leftNone : (reachedSignatures stack)[i]? = none := by
      simp [reachedSignatures, within]
    have rightNone : (expectedSignatures trace a b)[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    exact leftNone.trans rightNone.symm

theorem expected_signatures_perm (trace : List (Fin 150 × Bytes))
    (a b : Fin 150) :
    (expectedSignatures trace a b).Perm
      (finalSignatureBytes (a :: b :: trace.map Prod.fst)) := by
  let dummies := trace.map (fun p => generatedDummyAt p.1)
  have reverse : dummies.reverse.Perm dummies := List.reverse_perm dummies
  have reordered :
      ([generatedDummyAt b, generatedDummyAt a] ++ dummies.reverse ++
        [PoolRollInvariant.finalNonce]).Perm
      ([generatedDummyAt b, generatedDummyAt a] ++ dummies ++
        [PoolRollInvariant.finalNonce]) := by
    exact (reverse.append_left _).append_right _
  have swapped :
      ([generatedDummyAt b, generatedDummyAt a] ++ dummies ++
        [PoolRollInvariant.finalNonce]).Perm
      ([generatedDummyAt a, generatedDummyAt b] ++ dummies ++
        [PoolRollInvariant.finalNonce]) := by
    exact (List.Perm.swap (generatedDummyAt a) (generatedDummyAt b)
      dummies).append_right _
  simpa [expectedSignatures, finalSignatureBytes, dummies, List.map_map,
    List.append_assoc] using reordered.trans swapped

/-- The nine reached dummy signatures have the SINGLE flag and the tenth,
fixed nonce signature has the ALL flag, for any seven-position trace. -/
theorem expected_signature_flags (trace : List (Fin 150 × Bytes))
    (a b : Fin 150) (seven : trace.length = 7) :
    ((expectedSignatures trace a b).take 9).all
      (fun sig => sig.getLast? == some 0x03) = true ∧
    (expectedSignatures trace a b)[9]? =
      some PoolRollInvariant.finalNonce := by
  constructor
  · simp [expectedSignatures, seven,
      generatedDummyAt_sighash_single, List.all_eq_true]
  · simp [expectedSignatures, seven]

theorem reached_signature_flags (stack : List Bytes)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
    (h12 : stack[12]? = some (generatedDummyAt b))
    (h13 : stack[13]? = some (generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some PoolRollInvariant.finalNonce)
    (seven : trace.length = 7) :
    ((reachedSignatures stack).take 9).all
      (fun sig => sig.getLast? == some 0x03) = true ∧
    (reachedSignatures stack)[9]? = some PoolRollInvariant.finalNonce := by
  rw [reached_signatures_exact stack trace a b h12 h13 signed h21 seven]
  exact expected_signature_flags trace a b seven

/-- The raw deletion loop applied to the ten signature bytes actually
reached by the modeled final CHECKMULTISIG returns the scriptCode selected by
their nine original dummy indices. The reached-slot premises are explicit. -/
theorem reached_scriptCode (stack : List Bytes)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
    (h12 : stack[12]? = some (generatedDummyAt b))
    (h13 : stack[13]? = some (generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some PoolRollInvariant.finalNonce)
    (seven : trace.length = 7) :
    FindAndDelete.scanMany 880 EncodedLayout.chunks.flatten
      ((reachedSignatures stack).map directPushPattern) =
      finalEncodedScriptCode (a :: b :: trace.map Prod.fst) := by
  let ids := a :: b :: trace.map Prod.fst
  have exact := reached_signatures_exact stack trace a b
    h12 h13 signed h21 seven
  have signaturePerm : (reachedSignatures stack).Perm
      (finalSignatureBytes ids) := by
    rw [exact]
    exact expected_signatures_perm trace a b
  have patternPerm := signaturePerm.map directPushPattern
  have selected : ∀ p ∈ (reachedSignatures stack).map directPushPattern,
      p ∈ finalPatterns := by
    intro p present
    exact FindAndDelete.selected_patterns_subset ids p
      ((patternPerm.mem_iff).mp present)
  calc
    FindAndDelete.scanMany 880 EncodedLayout.chunks.flatten
        ((reachedSignatures stack).map directPushPattern) =
      stripEncodedChunks ((reachedSignatures stack).map directPushPattern)
        EncodedLayout.chunks :=
          FindAndDelete.literal_many_delete _ selected
    _ = stripEncodedChunks ((finalSignatureBytes ids).map directPushPattern)
          EncodedLayout.chunks :=
            stripEncodedChunks_perm EncodedLayout.chunks patternPerm
    _ = finalEncodedScriptCode ids := rfl

/-- A successful ten-against-ten scan verifies each reached signature against
its corresponding reached key. In particular, the fixed final nonce must
verify against the last key. This remains conditional on the supplied pair
verifier, not Core's ECDSA checker. -/
theorem matched_reached_pairs (stack : List Bytes)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
    (h12 : stack[12]? = some (generatedDummyAt b))
    (h13 : stack[13]? = some (generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some PoolRollInvariant.finalNonce)
    (seven : trace.length = 7)
    (verify : Bytes → Bytes → Bool)
    (matched : Multisig.matchSigs verify
      (reachedSignatures stack) ((stack.drop 1).take 10) = true) :
    List.Forall₂ (fun sig key => verify sig key = true)
      (expectedSignatures trace a b) ((stack.drop 1).take 10) ∧
    ∃ key, stack[10]? = some key ∧
      verify PoolRollInvariant.finalNonce key = true := by
  have stackLength : 22 ≤ stack.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h21
    omega
  have sigLength : (reachedSignatures stack).length = 10 := by
    simp [reachedSignatures, List.length_take]
    omega
  have keyLength : ((stack.drop 1).take 10).length = 10 := by
    simp [List.length_take]
    omega
  have pairs := (Multisig.equal_counts_success_iff_pairs verify
    (sigLength.trans keyLength.symm)).mp matched
  rw [reached_signatures_exact stack trace a b h12 h13 signed h21 seven]
    at pairs
  refine ⟨pairs, ?_⟩
  have nonceAt : (expectedSignatures trace a b)[9]? =
      some PoolRollInvariant.finalNonce :=
    (expected_signature_flags trace a b seven).2
  have stackIndex : 10 < stack.length := by omega
  let key := stack[10]
  have keyAt : stack[10]? = some key :=
    List.getElem?_eq_getElem stackIndex
  have keyAtList : ((stack.drop 1).take 10)[9]? = some key := by
    simpa [List.getElem?_drop] using keyAt
  have sigIndex : 9 < (expectedSignatures trace a b).length := by
    simp [expectedSignatures, seven]
  have keyIndex : 9 < ((stack.drop 1).take 10).length := by
    omega
  have pairAt := pairs.get sigIndex keyIndex
  have sigValue : (expectedSignatures trace a b)[9]'sigIndex =
      PoolRollInvariant.finalNonce := by
    rw [List.getElem?_eq_getElem sigIndex] at nonceAt
    exact Option.some.inj nonceAt
  have keyValue : ((stack.drop 1).take 10)[9]'keyIndex = key := by
    rw [List.getElem?_eq_getElem keyIndex] at keyAtList
    exact Option.some.inj keyAtList
  exact ⟨key, keyAt, by simpa [sigValue, keyValue] using pairAt⟩

/-- A successful full byte-model run with an encoding-sound, nonempty final
ten-pair scan determines the serialized scriptCode from its *reached* final
signature bytes. The scan and verifier still require Core refinement. -/
theorem matched_run_reached_scriptCode_verify_all (hashes : Hashes)
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
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : State),
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      trace.length = 7 ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      ((reachedSignatures beforeCheck.stack).take 9).all
        (fun sig => sig.getLast? == some 0x03) = true ∧
      (reachedSignatures beforeCheck.stack)[9]? =
        some PoolRollInvariant.finalNonce ∧
      FindAndDelete.scanMany 880 EncodedLayout.chunks.flatten
        ((reachedSignatures beforeCheck.stack).map directPushPattern) =
        finalEncodedScriptCode (a :: b :: trace.map Prod.fst) ∧
      List.Forall₂ (fun sig key => verify sig key = true)
        (expectedSignatures trace a b)
        ((beforeCheck.stack.drop 1).take 10) ∧
      (∃ key, beforeCheck.stack[10]? = some key ∧
        verify PoolRollInvariant.finalNonce key = true) := by
  obtain ⟨trace, a, b, beforeCheck, reached, first, last, signed,
    nonce, _dummy, seven, _hits, _different, _aFresh, _bFresh,
    distinct, _nine⟩ :=
      FinalBonusIndices.matched_full_run_nine_positions_verify_all
        hashes initial final accepted verify verifyNonempty verifyEncoding matched
  have flags := reached_signature_flags beforeCheck.stack trace a b
    last first signed nonce seven
  have pairs := matched_reached_pairs beforeCheck.stack trace a b
    last first signed nonce seven verify (matched beforeCheck reached)
  exact ⟨trace, a, b, beforeCheck, reached, seven, distinct,
    flags.1, flags.2,
    reached_scriptCode beforeCheck.stack trace a b last first signed nonce seven,
    pairs.1, pairs.2⟩

end QSB.FinalScriptCode
