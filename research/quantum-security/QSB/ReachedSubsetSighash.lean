import QSB.FinalSubsetInjective
import QSB.FinalScriptCode
import QSB.CoreMultisigSourceScan

/-!
The selected-set ALL-preimage classification is applied to signatures read
from the modeled final CHECKMULTISIG stack, rather than to a caller-chosen
deletion list. The slot premises come from a successful modeled final-round
trace; they are not a compiled Bitcoin Core acceptance theorem.
-/
namespace QSB.ReachedSubsetSighash
open ByteMachine
open ScriptCodeSelection
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- At the stated reached final slots, the generic source-shaped Core
FindAndDelete loop removes precisely the selected dummy pushes and fixed
nonce push, even though the reached signature order differs from index order.
This is a statement about the literal generated lock and the Lean source
model, not a C++ refinement theorem. -/
theorem reached_deleted_script
    (stack : List Bytes) (trace : List (Fin 150 × Bytes))
    (a b : Fin 150)
    (h12 : stack[12]? = some (FinalSignedLoop.generatedDummyAt b))
    (h13 : stack[13]? = some (FinalSignedLoop.generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some PoolRollInvariant.finalNonce)
    (seven : trace.length = 7) :
    CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
      stack 10 10 =
    ScriptSigSighash.tenDeletedScript
      (a :: b :: trace.map Prod.fst) := by
  let ids := a :: b :: trace.map Prod.fst
  have signaturePerm :
      (CoreMultisigSourceScan.reachedSignatures stack 10 10).Perm
        (finalSignatureBytes ids) := by
    change (FinalScriptCode.reachedSignatures stack).Perm
      (finalSignatureBytes ids)
    rw [FinalScriptCode.reached_signatures_exact stack trace a b
      h12 h13 signed h21 seven]
    exact FinalScriptCode.expected_signatures_perm trace a b
  have patternPerm := signaturePerm.map CorePushSerialize.pushPattern
  calc
    CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
        stack 10 10 =
      stripEncodedChunks
        ((CoreMultisigSourceScan.reachedSignatures stack 10 10).map
          CorePushSerialize.pushPattern) EncodedLayout.chunks :=
        CoreMultisigSourceScan.deletedScript_literal stack 10 10
    _ = stripEncodedChunks
          ((finalSignatureBytes ids).map CorePushSerialize.pushPattern)
          EncodedLayout.chunks :=
        stripEncodedChunks_perm EncodedLayout.chunks patternPerm
    _ = ScriptSigSighash.tenDeletedScript ids := by
        exact (CorePushFindAndDelete.literal_many_pushes
          (finalSignatureBytes ids)).symm

/-- Two modeled reached final stacks have identical source-shaped
FindAndDelete scripts exactly when their selected dummy-position sets agree.
Permutation of the nine choices or repeated positions does not affect this
classification. -/
theorem reached_script_eq_iff_selected_set_eq
    (left right : List Bytes)
    (leftTrace rightTrace : List (Fin 150 × Bytes))
    (leftA leftB rightA rightB : Fin 150)
    (left12 : left[12]? = some (FinalSignedLoop.generatedDummyAt leftB))
    (left13 : left[13]? = some (FinalSignedLoop.generatedDummyAt leftA))
    (leftSigned : ∀ j : Nat, j < 7 → left[j + 14]? =
      (leftTrace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (left21 : left[21]? = some PoolRollInvariant.finalNonce)
    (leftSeven : leftTrace.length = 7)
    (right12 : right[12]? = some (FinalSignedLoop.generatedDummyAt rightB))
    (right13 : right[13]? = some (FinalSignedLoop.generatedDummyAt rightA))
    (rightSigned : ∀ j : Nat, j < 7 → right[j + 14]? =
      (rightTrace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (right21 : right[21]? = some PoolRollInvariant.finalNonce)
    (rightSeven : rightTrace.length = 7) :
    CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
      left 10 10 =
    CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
      right 10 10 ↔
    (leftA :: leftB :: leftTrace.map Prod.fst).toFinset =
      (rightA :: rightB :: rightTrace.map Prod.fst).toFinset := by
  rw [reached_deleted_script left leftTrace leftA leftB
      left12 left13 leftSigned left21 leftSeven,
    reached_deleted_script right rightTrace rightA rightB
      right12 right13 rightSigned right21 rightSeven]
  exact FinalSubsetInjective.scriptCode_eq_iff_selected_set_eq

/-- With the same valid transaction fields and signed input, exact ALL
preimage equality for two reached modeled final stacks has the same selected
dummy-set equality classes. The SHA256d digests need not be injective. -/
theorem reached_all_preimage_eq_iff_selected_set_eq
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    (left right : List Bytes)
    (leftTrace rightTrace : List (Fin 150 × Bytes))
    (leftA leftB rightA rightB : Fin 150)
    (left12 : left[12]? = some (FinalSignedLoop.generatedDummyAt leftB))
    (left13 : left[13]? = some (FinalSignedLoop.generatedDummyAt leftA))
    (leftSigned : ∀ j : Nat, j < 7 → left[j + 14]? =
      (leftTrace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (left21 : left[21]? = some PoolRollInvariant.finalNonce)
    (leftSeven : leftTrace.length = 7)
    (right12 : right[12]? = some (FinalSignedLoop.generatedDummyAt rightB))
    (right13 : right[13]? = some (FinalSignedLoop.generatedDummyAt rightA))
    (rightSigned : ∀ j : Nat, j < 7 → right[j + 14]? =
      (rightTrace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (right21 : right[21]? = some PoolRollInvariant.finalNonce)
    (rightSeven : rightTrace.length = 7) :
    SighashAllWire.sourceAllPreimage tx selected
      (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
        left 10 10) =
    SighashAllWire.sourceAllPreimage tx selected
      (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
        right 10 10) ↔
    (leftA :: leftB :: leftTrace.map Prod.fst).toFinset =
      (rightA :: rightB :: rightTrace.map Prod.fst).toFinset := by
  rw [reached_deleted_script left leftTrace leftA leftB
      left12 left13 leftSigned left21 leftSeven,
    reached_deleted_script right rightTrace rightA rightB
      right12 right13 rightSigned right21 rightSeven]
  constructor
  · intro same
    by_contra different
    exact (FinalSubsetInjective.distinct_selected_sets_distinct_all_preimages
      tx selected txValid selectedValid different) same
  · intro same
    rw [FinalSubsetInjective.same_selected_set_equal_scriptCode same]

/-- Two successful full literal byte-model runs with explicit successful
ten-pair scans expose nine distinct selected positions each. Their reached
source-shaped final ALL preimages, when formed from the same valid transaction
and selected input, agree exactly when those position sets agree. The
verifier and modeled execution still require refinement to compiled Core. -/
theorem matched_runs_reached_all_preimage_classification
    (hashes : Hashes)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    (leftInitial leftFinal rightInitial rightFinal : State)
    (leftAccepted : run hashes ByteLayout.program leftInitial =
      some leftFinal)
    (rightAccepted : run hashes ByteLayout.program rightInitial =
      some rightFinal)
    (verify : Bytes → Bytes → Bool)
    (verifyNonempty : ∀ sig key, verify sig key = true → sig ≠ [])
    (verifyEncoding : ∀ sig key, verify sig key = true →
      DERSyntax.verifyAllEncoding sig = true)
    (leftMatched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) leftInitial =
        some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true)
    (rightMatched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) rightInitial =
        some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true) :
    ∃ (leftTrace rightTrace : List (Fin 150 × Bytes))
      (leftA leftB rightA rightB : Fin 150)
      (leftBefore rightBefore : State),
      run hashes (ByteLayout.program.take 879) leftInitial =
        some leftBefore ∧
      run hashes (ByteLayout.program.take 879) rightInitial =
        some rightBefore ∧
      (leftA :: leftB :: leftTrace.map Prod.fst).Nodup ∧
      (rightA :: rightB :: rightTrace.map Prod.fst).Nodup ∧
      (leftA :: leftB :: leftTrace.map Prod.fst).toFinset.card = 9 ∧
      (rightA :: rightB :: rightTrace.map Prod.fst).toFinset.card = 9 ∧
      (SighashAllWire.sourceAllPreimage tx selected
        (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
          leftBefore.stack 10 10) =
       SighashAllWire.sourceAllPreimage tx selected
        (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
          rightBefore.stack 10 10) ↔
       (leftA :: leftB :: leftTrace.map Prod.fst).toFinset =
         (rightA :: rightB :: rightTrace.map Prod.fst).toFinset) := by
  obtain ⟨leftTrace, leftA, leftB, leftBefore, leftReached,
    left13, left12, leftSigned, left21, _leftDummy,
    leftSeven, _leftHits, _leftDifferent, _leftAFresh, _leftBFresh,
    leftNodup, leftCard, _leftExtract⟩ :=
      FinalBonusIndices.matched_full_run_nine_positions_verify_all
        hashes leftInitial leftFinal leftAccepted verify
        verifyNonempty verifyEncoding leftMatched
  obtain ⟨rightTrace, rightA, rightB, rightBefore, rightReached,
    right13, right12, rightSigned, right21, _rightDummy,
    rightSeven, _rightHits, _rightDifferent, _rightAFresh, _rightBFresh,
    rightNodup, rightCard, _rightExtract⟩ :=
      FinalBonusIndices.matched_full_run_nine_positions_verify_all
        hashes rightInitial rightFinal rightAccepted verify
        verifyNonempty verifyEncoding rightMatched
  exact ⟨leftTrace, rightTrace, leftA, leftB, rightA, rightB,
    leftBefore, rightBefore, leftReached, rightReached,
    leftNodup, rightNodup, leftCard, rightCard,
    reached_all_preimage_eq_iff_selected_set_eq tx selected
      txValid selectedValid leftBefore.stack rightBefore.stack
      leftTrace rightTrace leftA leftB rightA rightB
      left12 left13 leftSigned left21 leftSeven
      right12 right13 rightSigned right21 rightSeven⟩

end QSB.ReachedSubsetSighash
