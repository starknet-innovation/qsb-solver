import QSB.FinalSubsetInjective
import QSB.FinalScriptCode
import QSB.CoreMultisigSourceScan
import QSB.CoreCheckedStep
import QSB.CoreCheckedWire

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

/-- The original scriptSig bytes may differ between the two attempts. If
erasing them makes the source transaction fields equal, then the reached
final ALL preimages still agree exactly when the selected dummy sets agree.
This says nothing about actual SHA256d digest equality or Core parsing of
either raw transaction. -/
theorem reached_all_preimage_eq_iff_selected_set_eq_of_erased
    (leftTx rightTx : SighashAllWire.TxFields) (selected : Nat)
    (leftValid : SighashAllWire.valid leftTx)
    (selectedValid : selected < leftTx.inputs.length)
    (sameErased : ScriptSigSighash.eraseScripts leftTx =
      ScriptSigSighash.eraseScripts rightTx)
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
    SighashAllWire.sourceAllPreimage leftTx selected
      (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
        left 10 10) =
    SighashAllWire.sourceAllPreimage rightTx selected
      (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
        right 10 10) ↔
    (leftA :: leftB :: leftTrace.map Prod.fst).toFinset =
      (rightA :: rightB :: rightTrace.map Prod.fst).toFinset := by
  have eraseRight :=
    ScriptSigSighash.sourceAllPreimage_eq_of_erased_scripts_eq
      leftTx rightTx selected
      (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
        right 10 10) sameErased
  rw [← eraseRight]
  exact reached_all_preimage_eq_iff_selected_set_eq leftTx selected
    leftValid selectedValid left right leftTrace rightTrace
    leftA leftB rightA rightB
    left12 left13 leftSigned left21 leftSeven
    right12 right13 rightSigned right21 rightSeven

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

/-- The literal checked-source interpreter computes its own signature-site
outcomes. Two truthy checked runs therefore yield reached nine-position sets
whose source-shaped final ALL preimages agree exactly when those sets agree,
without separately postulating a successful pair scan. The remaining bridge
is from arbitrary compiled-Core acceptance to this checked source run. -/
theorem checked_runs_reached_all_preimage_classification
    (hashes : Hashes)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (leftInitial leftFinal rightInitial rightFinal : CoreCheckedStep.State)
    (leftRecords rightRecords : List Bool)
    (leftSuccess : CoreCheckedStep.run hashes
      EncodedLayout.chunks.flatten validKey verify ByteLayout.program
      leftInitial = some (leftFinal, leftRecords))
    (rightSuccess : CoreCheckedStep.run hashes
      EncodedLayout.chunks.flatten validKey verify ByteLayout.program
      rightInitial = some (rightFinal, rightRecords))
    (leftAccepted : CoreFinalTruth.castToBool
      (leftFinal.stack.getLast?.getD []) = true)
    (rightAccepted : CoreFinalTruth.castToBool
      (rightFinal.stack.getLast?.getD []) = true) :
    ∃ (leftTrace rightTrace : List (Fin 150 × Bytes))
      (leftA leftB rightA rightB : Fin 150)
      (leftBefore rightBefore : ByteMachine.State),
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨leftInitial.stack.reverse, leftRecords, leftInitial.ops⟩ =
          some leftBefore ∧
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨rightInitial.stack.reverse, rightRecords, rightInitial.ops⟩ =
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
      CoreCheckedStep.literal_checked_run_nine_positions hashes
        validKey verify leftInitial leftFinal leftRecords
        leftSuccess leftAccepted
  obtain ⟨rightTrace, rightA, rightB, rightBefore, rightReached,
    right13, right12, rightSigned, right21, _rightDummy,
    rightSeven, _rightHits, _rightDifferent, _rightAFresh, _rightBFresh,
    rightNodup, rightCard, _rightExtract⟩ :=
      CoreCheckedStep.literal_checked_run_nine_positions hashes
        validKey verify rightInitial rightFinal rightRecords
        rightSuccess rightAccepted
  exact ⟨leftTrace, rightTrace, leftA, leftB, rightA, rightB,
    leftBefore, rightBefore, leftReached, rightReached,
    leftNodup, rightNodup, leftCard, rightCard,
    reached_all_preimage_eq_iff_selected_set_eq tx selected
      txValid selectedValid leftBefore.stack rightBefore.stack
      leftTrace rightTrace leftA leftB rightA rightB
      left12 left13 leftSigned left21 leftSeven
      right12 right13 rightSigned right21 rightSeven⟩

private theorem literal_wire_eq :
    DynamicCheckedCertificate.wire CoreCheckedWire.literalLock =
      EncodedLayout.chunks.flatten :=
  (CoreCheckedWire.matchesWire_sound EncodedLayout.chunks.flatten
    CoreCheckedWire.literalLock
    CoreCheckedWire.literal_fixture_matches).symm

private theorem literal_program_eq :
    DynamicCheckedCertificate.program CoreCheckedWire.literalLock =
      ByteLayout.program := by
  change DynamicWholeSource.fullProgram
    (DynamicFullSerialized.priorOps
      DynamicFullSerialized.literalPin
      DynamicFullSerialized.literalFirstNonce
      DynamicFullSerialized.literalFirstCommitment)
    PoolRollInvariant.finalNonce
    FinalSignedLoop.generatedCommitmentAt = ByteLayout.program
  rw [DynamicFullSerialized.literal_prior_ops]
  exact DynamicWholeSource.literal_full_program

private theorem literal_first_width :
    ∀ i : Fin 150,
      (CoreCheckedWire.literalLock.firstCommitment i).length = 20 := by
  decide

private theorem literal_second_width :
    ∀ i : Fin 150,
      (CoreCheckedWire.literalLock.secondCommitment i).length = 20 := by
  decide

private theorem literal_pin_short :
    CoreCheckedWire.literalLock.pin.length < 76 := by decide

private theorem literal_nonce0_short :
    CoreCheckedWire.literalLock.nonce0.length < 76 := by decide

private theorem literal_nonce1_short :
    CoreCheckedWire.literalLock.nonce1.length < 76 := by decide

/-- Exact byte validation of a supplied literal lock makes the parsed
checked-wire run identical to the fixed 880-opcode checked-source run. The
validator does not assert that a real spent output supplied these bytes or
that compiled Core executes the Lean transition function. -/
theorem literal_validated_run_eq_static
    (hashes : Hashes) (supplied : Bytes)
    (wireMatched : CoreCheckedWire.matchesWire supplied
      CoreCheckedWire.literalLock = true)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) :
    CoreCheckedWire.run hashes CoreCheckedWire.literalLock supplied
      stack validKey verify =
    CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program ⟨stack.reverse, 0⟩ := by
  rw [CoreCheckedWire.run_eq_model hashes CoreCheckedWire.literalLock
    supplied wireMatched literal_first_width literal_second_width
    literal_pin_short literal_nonce0_short literal_nonce1_short
    stack validKey verify]
  rw [literal_wire_eq, literal_program_eq]

/-- Two accepted *source-model* runs of supplied, exactly validated literal
locking bytes have final ALL preimages classified by the nine selected dummy
positions. This closes byte identity and caller-chosen scan/list premises
inside the model. A compiled-Core acceptance implication is still required. -/
theorem validated_runs_reached_all_preimage_classification
    (hashes : Hashes)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    (leftScript rightScript : Bytes)
    (leftMatched : CoreCheckedWire.matchesWire leftScript
      CoreCheckedWire.literalLock = true)
    (rightMatched : CoreCheckedWire.matchesWire rightScript
      CoreCheckedWire.literalLock = true)
    (leftStack rightStack : List Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (leftFinal rightFinal : CoreCheckedStep.State)
    (leftRecords rightRecords : List Bool)
    (leftSuccess : CoreCheckedWire.run hashes CoreCheckedWire.literalLock
      leftScript leftStack validKey verify = some (leftFinal, leftRecords))
    (rightSuccess : CoreCheckedWire.run hashes CoreCheckedWire.literalLock
      rightScript rightStack validKey verify = some (rightFinal, rightRecords))
    (leftAccepted : CoreFinalTruth.castToBool
      (leftFinal.stack.getLast?.getD []) = true)
    (rightAccepted : CoreFinalTruth.castToBool
      (rightFinal.stack.getLast?.getD []) = true) :
    ∃ (leftTrace rightTrace : List (Fin 150 × Bytes))
      (leftA leftB rightA rightB : Fin 150)
      (leftBefore rightBefore : ByteMachine.State),
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨leftStack, leftRecords, 0⟩ = some leftBefore ∧
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨rightStack, rightRecords, 0⟩ = some rightBefore ∧
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
  rw [literal_validated_run_eq_static hashes leftScript leftMatched
    leftStack validKey verify] at leftSuccess
  rw [literal_validated_run_eq_static hashes rightScript rightMatched
    rightStack validKey verify] at rightSuccess
  simpa using checked_runs_reached_all_preimage_classification
    hashes tx selected txValid selectedValid validKey verify
    ⟨leftStack.reverse, 0⟩ leftFinal ⟨rightStack.reverse, 0⟩ rightFinal
    leftRecords rightRecords leftSuccess rightSuccess
    leftAccepted rightAccepted

/-- The validated-byte result permits different original scriptSig programs
in the two source transactions. Equal erased transaction fields preserve
every ALL-committed field, while the reached selected set determines the
remaining final scriptCode bytes. The scriptSig evaluators and any real Core
acceptance relation are still outside this theorem. -/
theorem validated_runs_erased_scriptSig_classification
    (hashes : Hashes)
    (leftTx rightTx : SighashAllWire.TxFields) (selected : Nat)
    (leftValid : SighashAllWire.valid leftTx)
    (selectedValid : selected < leftTx.inputs.length)
    (sameErased : ScriptSigSighash.eraseScripts leftTx =
      ScriptSigSighash.eraseScripts rightTx)
    (leftScript rightScript : Bytes)
    (leftMatched : CoreCheckedWire.matchesWire leftScript
      CoreCheckedWire.literalLock = true)
    (rightMatched : CoreCheckedWire.matchesWire rightScript
      CoreCheckedWire.literalLock = true)
    (leftStack rightStack : List Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (leftFinal rightFinal : CoreCheckedStep.State)
    (leftRecords rightRecords : List Bool)
    (leftSuccess : CoreCheckedWire.run hashes CoreCheckedWire.literalLock
      leftScript leftStack validKey verify = some (leftFinal, leftRecords))
    (rightSuccess : CoreCheckedWire.run hashes CoreCheckedWire.literalLock
      rightScript rightStack validKey verify = some (rightFinal, rightRecords))
    (leftAccepted : CoreFinalTruth.castToBool
      (leftFinal.stack.getLast?.getD []) = true)
    (rightAccepted : CoreFinalTruth.castToBool
      (rightFinal.stack.getLast?.getD []) = true) :
    ∃ (leftTrace rightTrace : List (Fin 150 × Bytes))
      (leftA leftB rightA rightB : Fin 150)
      (leftBefore rightBefore : ByteMachine.State),
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨leftStack, leftRecords, 0⟩ = some leftBefore ∧
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨rightStack, rightRecords, 0⟩ = some rightBefore ∧
      (leftA :: leftB :: leftTrace.map Prod.fst).Nodup ∧
      (rightA :: rightB :: rightTrace.map Prod.fst).Nodup ∧
      (leftA :: leftB :: leftTrace.map Prod.fst).toFinset.card = 9 ∧
      (rightA :: rightB :: rightTrace.map Prod.fst).toFinset.card = 9 ∧
      (SighashAllWire.sourceAllPreimage leftTx selected
        (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
          leftBefore.stack 10 10) =
       SighashAllWire.sourceAllPreimage rightTx selected
        (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
          rightBefore.stack 10 10) ↔
       (leftA :: leftB :: leftTrace.map Prod.fst).toFinset =
         (rightA :: rightB :: rightTrace.map Prod.fst).toFinset) := by
  obtain ⟨leftTrace, rightTrace, leftA, leftB, rightA, rightB,
    leftBefore, rightBefore, leftReached, rightReached,
    leftNodup, rightNodup, leftCard, rightCard, classification⟩ :=
      validated_runs_reached_all_preimage_classification
        hashes leftTx selected leftValid selectedValid
        leftScript rightScript leftMatched rightMatched
        leftStack rightStack validKey verify leftFinal rightFinal
        leftRecords rightRecords leftSuccess rightSuccess
        leftAccepted rightAccepted
  refine ⟨leftTrace, rightTrace, leftA, leftB, rightA, rightB,
    leftBefore, rightBefore, leftReached, rightReached,
    leftNodup, rightNodup, leftCard, rightCard, ?_⟩
  have eraseRight :=
    ScriptSigSighash.sourceAllPreimage_eq_of_erased_scripts_eq
      leftTx rightTx selected
      (CoreMultisigSourceScan.deletedScript EncodedLayout.chunks.flatten
        rightBefore.stack 10 10) sameErased
  rw [← eraseRight]
  exact classification

end QSB.ReachedSubsetSighash
