import QSB.ParameterizedFinalSubset
import QSB.DynamicCheckedCertificate
import QSB.FinalScriptCode

/-!
Relate final signature bytes reached by the parameterized checked-source
interpreter to the candidate-list scriptCode classification. The checked
source model and its external signature verifier are not compiled Core.
-/
namespace QSB.ParameterizedReachedSubsetSighash
open ByteMachine ScriptCodeSelection
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

private theorem reached_signatures_exact (stack : List Bytes)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150) (nonce : Bytes)
    (h12 : stack[12]? = some (FinalSignedLoop.generatedDummyAt b))
    (h13 : stack[13]? = some (FinalSignedLoop.generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some nonce)
    (seven : trace.length = 7) :
    CoreMultisigSourceScan.reachedSignatures stack 10 10 =
      [FinalSignedLoop.generatedDummyAt b,
        FinalSignedLoop.generatedDummyAt a] ++
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse ++
      [nonce] := by
  apply List.ext_getElem?
  intro i
  by_cases within : i < 10
  · interval_cases i
    all_goals simp [CoreMultisigSourceScan.reachedSignatures,
      List.getElem?_drop,
      h12, h13, h21, signed, seven]
  · have rightLength :
        ([FinalSignedLoop.generatedDummyAt b,
            FinalSignedLoop.generatedDummyAt a] ++
          (trace.map (fun p =>
            FinalSignedLoop.generatedDummyAt p.1)).reverse ++
          [nonce]).length = 10 := by simp [seven]
    have leftNone :
        (CoreMultisigSourceScan.reachedSignatures stack 10 10)[i]? =
          none := by
      simp [CoreMultisigSourceScan.reachedSignatures, within]
    have rightNone :
        ([FinalSignedLoop.generatedDummyAt b,
            FinalSignedLoop.generatedDummyAt a] ++
          (trace.map (fun p =>
            FinalSignedLoop.generatedDummyAt p.1)).reverse ++
          [nonce])[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    exact leftNone.trans rightNone.symm

private theorem reached_signatures_perm (stack : List Bytes)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150) (nonce : Bytes)
    (h12 : stack[12]? = some (FinalSignedLoop.generatedDummyAt b))
    (h13 : stack[13]? = some (FinalSignedLoop.generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some nonce)
    (seven : trace.length = 7) :
    (CoreMultisigSourceScan.reachedSignatures stack 10 10).Perm
      ((a :: b :: trace.map Prod.fst).map
        FinalSignedLoop.generatedDummyAt ++ [nonce]) := by
  rw [reached_signatures_exact stack trace a b nonce
    h12 h13 signed h21 seven]
  let dummies := trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)
  have reverse : dummies.reverse.Perm dummies := List.reverse_perm dummies
  have reordered :
      ([FinalSignedLoop.generatedDummyAt b,
          FinalSignedLoop.generatedDummyAt a] ++ dummies.reverse ++
        [nonce]).Perm
      ([FinalSignedLoop.generatedDummyAt b,
          FinalSignedLoop.generatedDummyAt a] ++ dummies ++
        [nonce]) :=
    (reverse.append_left _).append_right _
  have swapped :
      ([FinalSignedLoop.generatedDummyAt b,
          FinalSignedLoop.generatedDummyAt a] ++ dummies ++
        [nonce]).Perm
      ([FinalSignedLoop.generatedDummyAt a,
          FinalSignedLoop.generatedDummyAt b] ++ dummies ++
        [nonce]) :=
    (List.Perm.swap (FinalSignedLoop.generatedDummyAt a)
      (FinalSignedLoop.generatedDummyAt b) dummies).append_right _
  simpa [dummies, List.map_map, List.append_assoc] using
    reordered.trans swapped

/-- The generic ten-signature source scan at reached final slots computes
the parameterized candidate scriptCode of those nine original dummy
positions. The reached stack supplies the deletion bytes, rather than the
caller choosing a deletion list. -/
theorem reached_deleted_script
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (stack : List Bytes) (trace : List (Fin 150 × Bytes))
    (a b : Fin 150)
    (h12 : stack[12]? = some (FinalSignedLoop.generatedDummyAt b))
    (h13 : stack[13]? = some (FinalSignedLoop.generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (h21 : stack[21]? = some nonce1)
    (seven : trace.length = 7) :
    CoreMultisigSourceScan.deletedScript
      (DynamicFullSerialized.fullWire pin nonce0 nonce1
        firstCommitment secondCommitment) stack 10 10 =
    ParameterizedFinalSubset.deletedScript pin nonce0 nonce1
      firstCommitment secondCommitment
      (a :: b :: trace.map Prod.fst) := by
  let ids := a :: b :: trace.map Prod.fst
  have signatures := reached_signatures_perm stack trace a b nonce1
    h12 h13 signed h21 seven
  have patterns := signatures.map CorePushSerialize.pushPattern
  calc
    CoreMultisigSourceScan.deletedScript
        (DynamicFullSerialized.fullWire pin nonce0 nonce1
          firstCommitment secondCommitment) stack 10 10 =
      stripEncodedChunks
        ((CoreMultisigSourceScan.reachedSignatures stack 10 10).map
          CorePushSerialize.pushPattern)
        (ParameterizedFindAndDelete.chunks pin nonce0 nonce1
          firstCommitment secondCommitment) :=
      ParameterizedFindAndDelete.reached_ten_deleted_script
        pin nonce0 nonce1 firstCommitment secondCommitment
        firstWidth secondWidth pinShort nonce0Short nonce1Short stack
    _ = stripEncodedChunks
          (ParameterizedFinalSubset.selectedPatterns nonce1 ids)
          (ParameterizedFindAndDelete.chunks pin nonce0 nonce1
            firstCommitment secondCommitment) := by
      exact stripEncodedChunks_perm _ patterns
    _ = ParameterizedFinalSubset.deletedScript pin nonce0 nonce1
          firstCommitment secondCommitment ids := by
      exact (ParameterizedFindAndDelete.runMany_eq_chunk_filter
        pin nonce0 nonce1 firstCommitment secondCommitment
        firstWidth secondWidth pinShort nonce0Short nonce1Short
        (ids.map FinalSignedLoop.generatedDummyAt ++ [nonce1])).symm

/-- The reached final stack cells and their original dummy indices. A checked
source run on a good setup constructs this record; its fields are also useful
for keeping the preimage theorem independent of the interpreter. -/
structure Reached (nonce : Bytes) where
  stack : List Bytes
  trace : List (Fin 150 × Bytes)
  a : Fin 150
  b : Fin 150
  slotB : stack[12]? = some (FinalSignedLoop.generatedDummyAt b)
  slotA : stack[13]? = some (FinalSignedLoop.generatedDummyAt a)
  signed : ∀ j : Nat, j < 7 → stack[j + 14]? =
    (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?
  nonceSlot : stack[21]? = some nonce
  seven : trace.length = 7

def selectedIds {nonce : Bytes} (w : Reached nonce) : List (Fin 150) :=
  w.a :: w.b :: w.trace.map Prod.fst

/-- In a parameterized Config A lock, a reached witness's source-shaped
final scriptCode is exactly the one selected by its nine dummy indices. -/
theorem reached_deleted_script_of_witness
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (w : Reached nonce1) :
    CoreMultisigSourceScan.deletedScript
      (DynamicFullSerialized.fullWire pin nonce0 nonce1
        firstCommitment secondCommitment) w.stack 10 10 =
    ParameterizedFinalSubset.deletedScript pin nonce0 nonce1
      firstCommitment secondCommitment (selectedIds w) :=
  reached_deleted_script pin nonce0 nonce1 firstCommitment
    secondCommitment firstWidth secondWidth pinShort nonce0Short
    nonce1Short w.stack w.trace w.a w.b
    w.slotB w.slotA w.signed w.nonceSlot w.seven

/-- Two reached modeled final stacks for one parameterized Config A lock
have equal source-shaped ALL preimages iff their selected dummy sets agree.
The nonce ALL flag excludes aliasing with a generated SINGLE dummy. -/
theorem reached_all_preimage_eq_iff_selected_set_eq
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (nonceAll : nonce1.getLast? = some 0x01)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    (left right : Reached nonce1) :
    SighashAllWire.sourceAllPreimage tx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicFullSerialized.fullWire pin nonce0 nonce1
          firstCommitment secondCommitment) left.stack 10 10) =
    SighashAllWire.sourceAllPreimage tx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicFullSerialized.fullWire pin nonce0 nonce1
          firstCommitment secondCommitment) right.stack 10 10) ↔
    (selectedIds left).toFinset = (selectedIds right).toFinset := by
  rw [reached_deleted_script_of_witness pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short left,
    reached_deleted_script_of_witness pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short right]
  exact ParameterizedFinalSubset.all_preimage_eq_iff_selected_set_eq
    pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short
    nonceAll tx selected txValid selectedValid

/-- Original scriptSig changes do not affect the classification if the two
source transactions agree after erasing those scripts. -/
theorem reached_all_preimage_eq_iff_selected_set_eq_of_erased
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (nonceAll : nonce1.getLast? = some 0x01)
    (leftTx rightTx : SighashAllWire.TxFields) (selected : Nat)
    (leftValid : SighashAllWire.valid leftTx)
    (selectedValid : selected < leftTx.inputs.length)
    (sameErased : ScriptSigSighash.eraseScripts leftTx =
      ScriptSigSighash.eraseScripts rightTx)
    (left right : Reached nonce1) :
    SighashAllWire.sourceAllPreimage leftTx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicFullSerialized.fullWire pin nonce0 nonce1
          firstCommitment secondCommitment) left.stack 10 10) =
    SighashAllWire.sourceAllPreimage rightTx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicFullSerialized.fullWire pin nonce0 nonce1
          firstCommitment secondCommitment) right.stack 10 10) ↔
    (selectedIds left).toFinset = (selectedIds right).toFinset := by
  rw [reached_deleted_script_of_witness pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short left,
    reached_deleted_script_of_witness pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short right]
  exact ParameterizedFinalSubset.all_preimage_eq_iff_selected_set_eq_of_erased
    pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short nonceAll
    leftTx rightTx selected leftValid selectedValid sameErased

/-- A successful parameterized checked-source search on a good setup
constructs the reached final signature record from the actual source-model
pre-CHECKMULTISIG stack. This carries the nine distinct selected indices. -/
theorem checked_search_reached (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search hashes lock stack
      validKey verify = some (firstRound, final))
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false) :
    ∃ (beforeCheck : CoreOpcodeStep.State)
      (w : Reached lock.nonce1),
      CoreStructuralRun.run hashes
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      w.stack = beforeCheck.stack.reverse ∧
      (selectedIds w).Nodup := by
  obtain ⟨trace, a, b, beforeCheck, reached, slotB, slotA,
    signed, nonceSlot, seven, _hits, distinct, _extracted⟩ :=
    DynamicCheckedCertificate.search_good_setup_reached_final_slots
      hashes lock stack validKey verify firstRound final found
      secondWidth noCommitmentDER
  refine ⟨beforeCheck,
    { stack := beforeCheck.stack.reverse
      trace := trace
      a := a
      b := b
      slotB := slotB
      slotA := slotA
      signed := signed
      nonceSlot := nonceSlot
      seven := seven }, reached, rfl, ?_⟩
  simpa [selectedIds] using distinct

/-- Two successful parameterized checked-source searches against the same
lock and hash functions have reached final ALL preimages in exact
selected-set equality classes for supplied transactions equal after original
scriptSig erasure. The source transaction fields are not yet derived from the
search inputs. The good-setup, width, and external checker premises are
explicit; compiled-Core acceptance and hash collision resistance are not
consequences of this theorem. -/
theorem checked_search_pair_all_preimage_classification
    (hashes : Hashes) (lock : DynamicCheckedCertificate.Lock)
    (leftStack rightStack : List Bytes)
    (leftValidKey rightValidKey : Bytes → Bool)
    (leftVerify rightVerify : CoreChecksigEval.VerifyECDSA)
    (leftRound rightRound : Bool)
    (leftFinal rightFinal : CoreOpcodeStep.State)
    (leftFound : DynamicCheckedCertificate.search hashes lock
      leftStack leftValidKey leftVerify = some (leftRound, leftFinal))
    (rightFound : DynamicCheckedCertificate.search hashes lock
      rightStack rightValidKey rightVerify = some (rightRound, rightFinal))
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false)
    (leftTx rightTx : SighashAllWire.TxFields) (selected : Nat)
    (leftValid : SighashAllWire.valid leftTx)
    (selectedValid : selected < leftTx.inputs.length)
    (sameErased : ScriptSigSighash.eraseScripts leftTx =
      ScriptSigSighash.eraseScripts rightTx) :
    ∃ (leftBefore rightBefore : CoreOpcodeStep.State)
      (left right : Reached lock.nonce1),
      CoreStructuralRun.run hashes
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial leftStack leftRound) =
          some leftBefore ∧
      CoreStructuralRun.run hashes
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial rightStack rightRound) =
          some rightBefore ∧
      left.stack = leftBefore.stack.reverse ∧
      right.stack = rightBefore.stack.reverse ∧
      (selectedIds left).Nodup ∧ (selectedIds right).Nodup ∧
      (SighashAllWire.sourceAllPreimage leftTx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          leftBefore.stack.reverse 10 10) =
       SighashAllWire.sourceAllPreimage rightTx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          rightBefore.stack.reverse 10 10) ↔
       (selectedIds left).toFinset = (selectedIds right).toFinset) := by
  obtain ⟨leftBefore, left, leftReached, leftStackEq, leftDistinct⟩ :=
    checked_search_reached hashes lock leftStack leftValidKey
      leftVerify leftRound leftFinal leftFound secondWidth
      noCommitmentDER
  obtain ⟨rightBefore, right, rightReached, rightStackEq,
    rightDistinct⟩ :=
    checked_search_reached hashes lock rightStack rightValidKey
      rightVerify rightRound rightFinal rightFound secondWidth
      noCommitmentDER
  refine ⟨leftBefore, rightBefore, left, right, leftReached,
    rightReached, leftStackEq, rightStackEq, leftDistinct,
    rightDistinct, ?_⟩
  rw [← leftStackEq, ← rightStackEq]
  change SighashAllWire.sourceAllPreimage leftTx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicFullSerialized.fullWire lock.pin lock.nonce0
          lock.nonce1 lock.firstCommitment lock.secondCommitment)
        left.stack 10 10) =
    SighashAllWire.sourceAllPreimage rightTx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicFullSerialized.fullWire lock.pin lock.nonce0
          lock.nonce1 lock.firstCommitment lock.secondCommitment)
        right.stack 10 10) ↔
    (selectedIds left).toFinset = (selectedIds right).toFinset
  exact reached_all_preimage_eq_iff_selected_set_eq_of_erased
    lock.pin lock.nonce0 lock.nonce1
    lock.firstCommitment lock.secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short nonceAll
    leftTx rightTx selected leftValid selectedValid sameErased
    left right

end QSB.ParameterizedReachedSubsetSighash
