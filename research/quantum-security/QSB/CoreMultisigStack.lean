import QSB.CoreRoll
import QSB.FinalScriptCode

/-!
Core v27.2 `OP_CHECKMULTISIG` uses a bottom-first vector and
`stacktop(-i)` with one-based `i`. This module translates its source indices
to the top-first byte stack used by `ByteMachine`. The result concerns stack
addressing, not the actual Core signature parser or ECDSA checker.
-/
namespace QSB.CoreMultisigStack
open ByteMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def stacktopNeg (bottom : List Bytes) (i : Nat) : Option Bytes :=
  bottom[bottom.length - i]?

theorem stacktopNeg_reverse (top : List Bytes) (i : Nat)
    (valid : 1 ≤ i ∧ i ≤ top.length) :
    stacktopNeg top.reverse i = top[i - 1]? := by
  have depth : i - 1 < top.length := by omega
  have index : top.length - i = top.length - 1 - (i - 1) := by omega
  simpa [stacktopNeg, index] using
    CoreRoll.getElem_reverse_at_depth top (i - 1) depth

/-- In Core's source, `ikey = 2`, while `isig = nKeysCount + 3`. -/
def keyAt (bottom : List Bytes) (j : Nat) : Option Bytes :=
  stacktopNeg bottom (2 + j)

def signatureAt (bottom : List Bytes) (nKeys j : Nat) : Option Bytes :=
  stacktopNeg bottom (nKeys + 3 + j)

theorem keyAt_reverse (top : List Bytes) (j : Nat)
    (valid : 2 + j ≤ top.length) :
    keyAt top.reverse j = top[1 + j]? := by
  have one : 1 ≤ 2 + j := by omega
  simpa [keyAt, show 2 + j - 1 = 1 + j by omega] using
    stacktopNeg_reverse top (2 + j) ⟨one, valid⟩

theorem signatureAt_reverse (top : List Bytes) (nKeys j : Nat)
    (valid : nKeys + 3 + j ≤ top.length) :
    signatureAt top.reverse nKeys j = top[nKeys + 2 + j]? := by
  have one : 1 ≤ nKeys + 3 + j := by omega
  simpa [signatureAt,
    show nKeys + 3 + j - 1 = nKeys + 2 + j by omega] using
    stacktopNeg_reverse top (nKeys + 3 + j) ⟨one, valid⟩

/-- The two count cells Core reads at depths 1 and `nKeysCount + 2`
are top-first positions zero and `nKeysCount + 1`. -/
theorem count_cells_reverse (top : List Bytes) (nKeys : Nat)
    (nonempty : 1 ≤ top.length)
    (sigCountPresent : nKeys + 2 ≤ top.length) :
    stacktopNeg top.reverse 1 = top[0]? ∧
      stacktopNeg top.reverse (nKeys + 2) = top[nKeys + 1]? := by
  constructor
  · simpa using stacktopNeg_reverse top 1 ⟨by omega, nonempty⟩
  · simpa [show nKeys + 2 - 1 = nKeys + 1 by omega] using
      stacktopNeg_reverse top (nKeys + 2)
        ⟨by omega, sigCountPresent⟩

theorem final_key_slot (top : List Bytes) (j : Nat)
    (valid : 2 + j ≤ top.length) :
    keyAt top.reverse j = top[1 + j]? :=
  keyAt_reverse top j valid

theorem final_signature_slot (top : List Bytes) (j : Nat)
    (valid : 13 + j ≤ top.length) :
    signatureAt top.reverse 10 j = top[12 + j]? := by
  simpa using signatureAt_reverse top 10 j valid

/-- Every one of Core's ten scan pairs addresses exactly the corresponding
reached key and signature in the Lean top-first lists. This also covers the
preceding FindAndDelete loop, which reads signatures in the same order. -/
theorem final_pair_slots (top : List Bytes) (enough : 22 ≤ top.length)
    (j : Fin 10) :
    keyAt top.reverse j.val = ((top.drop 1).take 10)[j.val]? ∧
    signatureAt top.reverse 10 j.val =
      (FinalScriptCode.reachedSignatures top)[j.val]? := by
  have keyValid : 2 + j.val ≤ top.length := by omega
  have sigValid : 13 + j.val ≤ top.length := by omega
  constructor
  · rw [final_key_slot top j.val keyValid]
    simp [j.isLt, Nat.add_comm]
  · rw [final_signature_slot top j.val sigValid]
    simp [FinalScriptCode.reachedSignatures, List.getElem?_drop, j.isLt]

/-- After reading ten keys and ten signatures, Core's source variable `i`
is 23. Its stack cleanup pops the 22 counted arguments, then the extra
NULLDUMMY item at depth 23. -/
def sourceArgumentDepth (nKeys nSigs : Nat) : Nat :=
  nKeys + nSigs + 3

theorem final_argument_depth : sourceArgumentDepth 10 10 = 23 := by decide

theorem final_source_layout (top : List Bytes) (enough : 23 ≤ top.length) :
    stacktopNeg top.reverse 1 = top[0]? ∧
    stacktopNeg top.reverse 12 = top[11]? ∧
    stacktopNeg top.reverse (sourceArgumentDepth 10 10) = top[22]? ∧
    (∀ j : Fin 10,
      keyAt top.reverse j.val = ((top.drop 1).take 10)[j.val]? ∧
      signatureAt top.reverse 10 j.val =
        (FinalScriptCode.reachedSignatures top)[j.val]?) := by
  obtain ⟨keyCount, sigCount⟩ :=
    count_cells_reverse top 10 (by omega) (by omega)
  have dummy := stacktopNeg_reverse top 23 ⟨by omega, enough⟩
  refine ⟨keyCount, sigCount, ?_, ?_⟩
  · simpa [sourceArgumentDepth] using dummy
  · intro j
    exact final_pair_slots top (by omega) j

/-- Any successful modeled final check with the two generated count cells
has the exact source-facing count, pair, and NULLDUMMY addressing. It does
not identify Core's real ECDSA outcome with the model's supplied Boolean. -/
theorem reached_check_source_layout (hashes : Hashes)
    (beforeCheck final : State)
    (keyCount : beforeCheck.stack[0]? = some [0x0a])
    (sigCount : beforeCheck.stack[11]? = some [0x0a])
    (executed : run hashes [.checkmultisig] beforeCheck = some final) :
    stacktopNeg beforeCheck.stack.reverse 1 = some [0x0a] ∧
    stacktopNeg beforeCheck.stack.reverse 12 = some [0x0a] ∧
    stacktopNeg beforeCheck.stack.reverse 23 = some [] ∧
    (∀ j : Fin 10,
      keyAt beforeCheck.stack.reverse j.val =
        ((beforeCheck.stack.drop 1).take 10)[j.val]? ∧
      signatureAt beforeCheck.stack.reverse 10 j.val =
        (FinalScriptCode.reachedSignatures beforeCheck.stack)[j.val]?) := by
  have dummy := ByteFinalCounts.successful_final_check_dummy_empty
    hashes beforeCheck final keyCount sigCount executed
  have enough : 23 ≤ beforeCheck.stack.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp dummy
    omega
  obtain ⟨sourceKeys, sourceSigs, sourceDummy, pairs⟩ :=
    final_source_layout beforeCheck.stack enough
  exact ⟨sourceKeys.trans keyCount, sourceSigs.trans sigCount,
    by simpa [sourceArgumentDepth] using sourceDummy.trans dummy, pairs⟩

/-- Under an equal-count successful abstract matching scan, every Core
source-addressed signature/key pair satisfies the supplied verifier. The
premise still has to be obtained from Core's real CHECKMULTISIG execution. -/
theorem matched_source_pair (top : List Bytes)
    (enough : 23 ≤ top.length)
    (verify : Bytes → Bytes → Bool)
    (matched : Multisig.matchSigs verify
      (FinalScriptCode.reachedSignatures top)
      ((top.drop 1).take 10) = true)
    (j : Fin 10) :
    ∃ sig key,
      signatureAt top.reverse 10 j.val = some sig ∧
      keyAt top.reverse j.val = some key ∧
      verify sig key = true := by
  have sigLength : (FinalScriptCode.reachedSignatures top).length = 10 := by
    simp [FinalScriptCode.reachedSignatures, List.length_take]
    omega
  have keyLength : ((top.drop 1).take 10).length = 10 := by
    simp [List.length_take]
    omega
  have pairProof := (Multisig.equal_counts_success_iff_pairs verify
    (sigLength.trans keyLength.symm)).mp matched
  have sigIndex : j.val < (FinalScriptCode.reachedSignatures top).length := by
    omega
  have keyIndex : j.val < ((top.drop 1).take 10).length := by omega
  let sig := (FinalScriptCode.reachedSignatures top)[j.val]
  let key := ((top.drop 1).take 10)[j.val]
  have sigAt : (FinalScriptCode.reachedSignatures top)[j.val]? =
      some sig := List.getElem?_eq_getElem sigIndex
  have keyAtList : ((top.drop 1).take 10)[j.val]? =
      some key := List.getElem?_eq_getElem keyIndex
  have sourceSlots := (final_pair_slots top (by omega) j)
  have pairAt := pairProof.get sigIndex keyIndex
  exact ⟨sig, key, sourceSlots.2.trans sigAt,
    sourceSlots.1.trans keyAtList, pairAt⟩

/-- Every truthy successful run of the full literal byte program reaches
Core-shaped final count, signature, key, and NULLDUMMY addresses. This is
still inside `ByteMachine`; real Core acceptance and checker refinement are
the remaining bridge. -/
theorem accepted_whole_byte_run_source_layout (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (truth : finalTruth final = true) :
    ∃ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      23 ≤ beforeCheck.stack.length ∧
      stacktopNeg beforeCheck.stack.reverse 1 = some [0x0a] ∧
      stacktopNeg beforeCheck.stack.reverse 12 = some [0x0a] ∧
      stacktopNeg beforeCheck.stack.reverse 23 = some [] ∧
      (∀ j : Fin 10,
        keyAt beforeCheck.stack.reverse j.val =
          ((beforeCheck.stack.drop 1).take 10)[j.val]? ∧
        signatureAt beforeCheck.stack.reverse 10 j.val =
          (FinalScriptCode.reachedSignatures beforeCheck.stack)[j.val]?) := by
  obtain ⟨beforeSuffix, beforeCheck, prefixRun, setup,
    keyCount, sigCount, _lastTrue⟩ :=
    ByteFinalCounts.accepted_true_whole_program_final_counts
      hashes initial final accepted truth
  have suffix : run hashes (ByteLayout.program.drop 857) beforeSuffix =
      some final := by
    have split : ByteLayout.program = ByteLayout.program.take 857 ++
        ByteLayout.program.drop 857 := by decide
    rw [split, run_append, prefixRun] at accepted
    simpa using accepted
  have checked : run hashes [.checkmultisig] beforeCheck = some final := by
    rw [ByteFinalCounts.generated_final_setup_suffix, run_append,
      setup] at suffix
    simpa using suffix
  have before : run hashes (ByteLayout.program.take 879) initial =
      some beforeCheck := by
    have split : ByteLayout.program.take 879 =
        ByteLayout.program.take 857 ++ ByteFinalCounts.finalSetup := by decide
    rw [split, run_append, prefixRun]
    simpa using setup
  have dummy := ByteFinalCounts.successful_final_check_dummy_empty
    hashes beforeCheck final keyCount sigCount checked
  have enough : 23 ≤ beforeCheck.stack.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp dummy
    omega
  exact ⟨beforeCheck, before, enough,
    reached_check_source_layout hashes beforeCheck final
      keyCount sigCount checked⟩

/-- Combining the full byte trace with an externally justified successful
ten-pair scan yields a verifier hit at every Core source-addressed final pair.
The external scan premise is exactly where Core ECDSA, DER, and scriptCode
refinement must enter. -/
theorem matched_whole_byte_run_source_pairs (hashes : Hashes)
    (initial final : State)
    (accepted : run hashes ByteLayout.program initial = some final)
    (truth : finalTruth final = true)
    (verify : Bytes → Bytes → Bool)
    (matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        (FinalScriptCode.reachedSignatures beforeCheck.stack)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      ∀ j : Fin 10, ∃ sig key,
        signatureAt beforeCheck.stack.reverse 10 j.val = some sig ∧
        keyAt beforeCheck.stack.reverse j.val = some key ∧
        verify sig key = true := by
  obtain ⟨beforeCheck, prefixRun, enough, _, _, _, _⟩ :=
    accepted_whole_byte_run_source_layout hashes initial final
      accepted truth
  exact ⟨beforeCheck, prefixRun, fun j =>
    matched_source_pair beforeCheck.stack enough verify
      (matched beforeCheck prefixRun) j⟩

end QSB.CoreMultisigStack
