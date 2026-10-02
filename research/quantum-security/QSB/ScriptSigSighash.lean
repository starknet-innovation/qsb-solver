import QSB.CorePushFindAndDelete
import QSB.SighashAllWireFixture

/-!
Separate two legacy ALL facts that must not be conflated in the QSB game.
The original scriptSig bytes are removed from the source-shaped ALL preimage
when a fixed `scriptCode` is supplied. But final CHECKMULTISIG's FindAndDelete
scriptCode may itself depend on which generated dummy signatures the scriptSig
causes the lock to select. These are source-model facts, not Core refinement.
-/
namespace QSB.ScriptSigSighash
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def eraseScripts (tx : SighashAllWire.TxFields) :
    SighashAllWire.TxFields :=
  { tx with inputs := tx.inputs.map (fun input =>
      SighashAllWire.withScript input []) }

private theorem withScript_overwrites (input : SighashAllWire.InputFields)
    (first second : Bytes) :
    SighashAllWire.withScript
      (SighashAllWire.withScript input first) second =
        SighashAllWire.withScript input second := by
  rcases input with ⟨txid, index, oldScript, sequence⟩
  rfl

private theorem prepareInputsAt_erase (selected : Nat) (scriptCode : Bytes)
    (position : Nat) (inputs : List SighashAllWire.InputFields) :
    SighashAllWire.prepareInputsAt selected scriptCode position
        (inputs.map (fun input => SighashAllWire.withScript input [])) =
      SighashAllWire.prepareInputsAt selected scriptCode position inputs := by
  induction inputs generalizing position with
  | nil => rfl
  | cons input rest ih =>
      simp [SighashAllWire.prepareInputsAt, withScript_overwrites, ih]

/-- At a fixed selected input and fixed scriptCode, changing any original
scriptSig cannot change the source-shaped ALL preimage. -/
theorem sourceAllPreimage_eraseScripts
    (tx : SighashAllWire.TxFields) (selected : Nat) (scriptCode : Bytes) :
    SighashAllWire.sourceAllPreimage (eraseScripts tx) selected scriptCode =
      SighashAllWire.sourceAllPreimage tx selected scriptCode := by
  unfold SighashAllWire.sourceAllPreimage SighashAllWire.prepareAll
  cases tx with
  | mk version inputs outputs locktime =>
      simp [eraseScripts, prepareInputsAt_erase]

theorem sourceAllPreimage_eq_of_erased_scripts_eq
    (left right : SighashAllWire.TxFields)
    (selected : Nat) (scriptCode : Bytes)
    (same : eraseScripts left = eraseScripts right) :
    SighashAllWire.sourceAllPreimage left selected scriptCode =
      SighashAllWire.sourceAllPreimage right selected scriptCode := by
  rw [← sourceAllPreimage_eraseScripts left,
    same, sourceAllPreimage_eraseScripts right]

private theorem prepared_selected_script
    (selected position index : Nat) (scriptCode : Bytes)
    (inputs : List SighashAllWire.InputFields)
    (atSelected : selected = position + index)
    (within : index < inputs.length) :
    ((SighashAllWire.prepareInputsAt selected scriptCode position
      inputs)[index]?).map (fun input => input.2.2.1) =
        some scriptCode := by
  induction inputs generalizing position index with
  | nil => simp at within
  | cons input rest ih =>
      cases index with
      | zero =>
          have same : selected = position := by simpa using atSelected
          simp [SighashAllWire.prepareInputsAt, same,
            SighashAllWire.withScript]
      | succ next =>
          have later : selected = position + 1 + next := by omega
          have restWithin : next < rest.length := by simpa using within
          simpa [SighashAllWire.prepareInputsAt] using
            ih (position + 1) next later restWithin

private theorem prepared_other_script
    (selected position index : Nat) (scriptCode : Bytes)
    (inputs : List SighashAllWire.InputFields)
    (other : selected ≠ position + index)
    (within : index < inputs.length) :
    ((SighashAllWire.prepareInputsAt selected scriptCode position
      inputs)[index]?).map (fun input => input.2.2.1) =
        some [] := by
  induction inputs generalizing position index with
  | nil => simp at within
  | cons input rest ih =>
      cases index with
      | zero =>
          have different : selected ≠ position := by simpa using other
          have reversed : position ≠ selected := Ne.symm different
          simp [SighashAllWire.prepareInputsAt, reversed,
            SighashAllWire.withScript]
      | succ next =>
          have later : selected ≠ position + 1 + next := by omega
          have restWithin : next < rest.length := by simpa using within
          simpa [SighashAllWire.prepareInputsAt] using
            ih (position + 1) next later restWithin

/-- Across arbitrary valid source transactions, equal ALL preimage bytes
with a nonempty selected scriptCode identify both the selected input index
and the selected scriptCode. Other transaction fields and original scriptSigs
may differ; equal bytes do not imply equal SHA256d digests in reverse. -/
theorem sourceAllPreimage_identifies_selected_scriptCode
    (left right : SighashAllWire.TxFields)
    (leftSelected rightSelected : Nat) (leftScript rightScript : Bytes)
    (leftValid : SighashAllWire.valid left)
    (rightValid : SighashAllWire.valid right)
    (leftSelectedValid : leftSelected < left.inputs.length)
    (leftScriptValid : leftScript.length < 256 ^ 8)
    (rightScriptValid : rightScript.length < 256 ^ 8)
    (leftNonempty : leftScript ≠ [])
    (same : SighashAllWire.sourceAllPreimage left leftSelected leftScript =
      SighashAllWire.sourceAllPreimage right rightSelected rightScript) :
    leftSelected = rightSelected ∧ leftScript = rightScript := by
  have preparedEqual :
      SighashAllWire.prepareAll left leftSelected leftScript =
        SighashAllWire.prepareAll right rightSelected rightScript :=
    SighashAllWire.encode_injective_on
      (SighashAllWire.prepareAll_valid left leftSelected leftScript
        leftValid leftScriptValid)
      (SighashAllWire.prepareAll_valid right rightSelected rightScript
        rightValid rightScriptValid) same
  have inputLengths := congrArg
    (fun tx : SighashAllWire.TxFields => tx.inputs.length) preparedEqual
  have rightWithin : leftSelected < right.inputs.length := by
    simp only [SighashAllWire.prepareAll,
      SighashAllWire.prepareInputsAt_length] at inputLengths
    omega
  have scriptsEq := congrArg
    (fun tx : SighashAllWire.TxFields =>
      (tx.inputs[leftSelected]?).map (fun input => input.2.2.1))
    preparedEqual
  have leftAt := prepared_selected_script leftSelected 0 leftSelected
    leftScript left.inputs (by omega) leftSelectedValid
  by_cases selectedEq : leftSelected = rightSelected
  · subst rightSelected
    have rightAt := prepared_selected_script leftSelected 0 leftSelected
      rightScript right.inputs (by omega) rightWithin
    constructor
    · rfl
    · simpa [SighashAllWire.prepareAll, leftAt, rightAt] using
        Option.some.inj (by simpa [SighashAllWire.prepareAll,
          leftAt, rightAt] using scriptsEq)
  · have other : rightSelected ≠ 0 + leftSelected := by
      simpa using Ne.symm selectedEq
    have rightAt := prepared_other_script rightSelected 0 leftSelected
      rightScript right.inputs other rightWithin
    have empty : leftScript = [] := by
      have slots : (some leftScript : Option Bytes) = some [] := by
        simpa [SighashAllWire.prepareAll, leftAt, rightAt] using scriptsEq
      exact Option.some.inj slots
    exact (leftNonempty empty).elim

/-- For a real selected input, the source-shaped ALL preimage is injective
in the supplied scriptCode on the valid finite-width wire domain. This does
not assert that SHA256d is injective. -/
theorem sourceAllPreimage_injective_scriptCode
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (left right : Bytes)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    (leftWidth : left.length < 256 ^ 8)
    (rightWidth : right.length < 256 ^ 8)
    (same : SighashAllWire.sourceAllPreimage tx selected left =
      SighashAllWire.sourceAllPreimage tx selected right) :
    left = right := by
  have preparedEq : SighashAllWire.prepareAll tx selected left =
      SighashAllWire.prepareAll tx selected right :=
    SighashAllWire.encode_injective_on
      (SighashAllWire.prepareAll_valid tx selected left txValid leftWidth)
      (SighashAllWire.prepareAll_valid tx selected right txValid rightWidth)
      same
  have scriptsEq := congrArg
    (fun prepared : SighashAllWire.TxFields =>
      (prepared.inputs[selected]?).map (fun input => input.2.2.1))
    preparedEq
  have leftAt := prepared_selected_script selected 0 selected left
    tx.inputs (by omega) selectedValid
  have rightAt := prepared_selected_script selected 0 selected right
    tx.inputs (by omega) selectedValid
  simpa [SighashAllWire.prepareAll, leftAt, rightAt] using
    Option.some.inj (by simpa [SighashAllWire.prepareAll, leftAt,
      rightAt] using scriptsEq)

/-- The literal lock's Core-shaped one-signature deletion result. This
function is used only to witness that *different reached signature sets can*
produce different final scriptCodes; it is not a complete final-round run. -/
def oneDummyDeletedScript (i : Fin 150) : Bytes :=
  CoreFindAndDelete.runMany 880 EncodedLayout.chunks.flatten
    ([FinalSignedLoop.generatedDummyAt i].map
      CorePushSerialize.pushPattern)

private theorem oneDummyDeletedScript_eq_filter (i : Fin 150) :
    oneDummyDeletedScript i =
      ScriptCodeSelection.stripEncodedChunks
        ([FinalSignedLoop.generatedDummyAt i].map
          CorePushSerialize.pushPattern) EncodedLayout.chunks := by
  exact CorePushFindAndDelete.literal_many_pushes
    [FinalSignedLoop.generatedDummyAt i]

/-- Two actual generated dummy signatures remove different opcode chunks
from the literal 880-chunk lock in the source-shaped FindAndDelete model. -/
theorem literal_dummy_zero_one_delete_different :
    oneDummyDeletedScript ⟨0, by decide⟩ ≠
      oneDummyDeletedScript ⟨1, by decide⟩ := by
  rw [oneDummyDeletedScript_eq_filter, oneDummyDeletedScript_eq_filter]
  have mismatch :
      (ScriptCodeSelection.stripEncodedChunks
        ([FinalSignedLoop.generatedDummyAt ⟨0, by decide⟩].map
          CorePushSerialize.pushPattern) EncodedLayout.chunks)[9634]? ≠
      (ScriptCodeSelection.stripEncodedChunks
        ([FinalSignedLoop.generatedDummyAt ⟨1, by decide⟩].map
          CorePushSerialize.pushPattern) EncodedLayout.chunks)[9634]? := by
    decide
  intro same
  exact mismatch (congrArg (fun script : Bytes => script[9634]?) same)

private theorem oneDummyDeletedScript_width (i : Fin 150) :
    (oneDummyDeletedScript i).length < 256 ^ 8 := by
  have bounded := CoreFindAndDelete.runMany_length_le 880
    EncodedLayout.chunks.flatten
    ([FinalSignedLoop.generatedDummyAt i].map CorePushSerialize.pushPattern)
  have lockLength := EncodedLayout.script_length
  change (oneDummyDeletedScript i).length ≤
    EncodedLayout.chunks.flatten.length at bounded
  omega

/-- Holding the transaction fields and selected input fixed, these two
source-shaped final scriptCodes make distinct ALL *preimages*. A SHA256d
collision may still give the same digest, and this is not a Core-accepted
QSB spend or a claim that arbitrary selections are accepted. -/
theorem literal_dummy_deletions_distinct_all_preimages
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length) :
    SighashAllWire.sourceAllPreimage tx selected
      (oneDummyDeletedScript ⟨0, by decide⟩) ≠
    SighashAllWire.sourceAllPreimage tx selected
      (oneDummyDeletedScript ⟨1, by decide⟩) := by
  intro same
  exact literal_dummy_zero_one_delete_different
    (sourceAllPreimage_injective_scriptCode tx selected _ _
      txValid selectedValid
      (oneDummyDeletedScript_width ⟨0, by decide⟩)
      (oneDummyDeletedScript_width ⟨1, by decide⟩) same)

/-- Two nine-position lists with eight shared generated dummies. Their
ten-signature deletion lists append the same fixed final nonce. -/
def commonEight : List (Fin 150) :=
  List.ofFn (fun i : Fin 8 => (⟨i.val + 2, by omega⟩ : Fin 150))

def selectedNineZero : List (Fin 150) :=
  ⟨0, by decide⟩ :: commonEight

def selectedNineOne : List (Fin 150) :=
  ⟨1, by decide⟩ :: commonEight

theorem selected_nine_lengths :
    selectedNineZero.length = 9 ∧ selectedNineOne.length = 9 := by
  decide

theorem selected_nine_nodup :
    selectedNineZero.Nodup ∧ selectedNineOne.Nodup := by
  decide

def tenDeletedScript (ids : List (Fin 150)) : Bytes :=
  CoreFindAndDelete.runMany 880 EncodedLayout.chunks.flatten
    ((ScriptCodeSelection.finalSignatureBytes ids).map
      CorePushSerialize.pushPattern)

private theorem tenDeletedScript_eq_filter (ids : List (Fin 150)) :
    tenDeletedScript ids =
      ScriptCodeSelection.stripEncodedChunks
        ((ScriptCodeSelection.finalSignatureBytes ids).map
          CorePushSerialize.pushPattern) EncodedLayout.chunks :=
  CorePushFindAndDelete.literal_many_pushes
    (ScriptCodeSelection.finalSignatureBytes ids)

/-- The complete source-shaped final signature deletion lists differ at
byte 9554 of the resulting scriptCode. The lists are candidate signature
roles, not proved reachable accepted QSB witnesses. -/
theorem selected_nine_ten_deletions_different :
    tenDeletedScript selectedNineZero ≠
      tenDeletedScript selectedNineOne := by
  rw [tenDeletedScript_eq_filter, tenDeletedScript_eq_filter]
  have mismatch :
      (ScriptCodeSelection.stripEncodedChunks
        ((ScriptCodeSelection.finalSignatureBytes selectedNineZero).map
          CorePushSerialize.pushPattern) EncodedLayout.chunks)[9554]? ≠
      (ScriptCodeSelection.stripEncodedChunks
        ((ScriptCodeSelection.finalSignatureBytes selectedNineOne).map
          CorePushSerialize.pushPattern) EncodedLayout.chunks)[9554]? := by
    decide
  intro same
  exact mismatch (congrArg (fun script : Bytes => script[9554]?) same)

private theorem tenDeletedScript_width (ids : List (Fin 150)) :
    (tenDeletedScript ids).length < 256 ^ 8 := by
  have bounded := CoreFindAndDelete.runMany_length_le 880
    EncodedLayout.chunks.flatten
    ((ScriptCodeSelection.finalSignatureBytes ids).map
      CorePushSerialize.pushPattern)
  have lockLength := EncodedLayout.script_length
  change (tenDeletedScript ids).length ≤
    EncodedLayout.chunks.flatten.length at bounded
  omega

/-- For any valid selected input, the two complete candidate final
signature-role lists give distinct source-shaped ALL preimages. Their
SHA256d digests may collide; no real-lock acceptance is asserted. -/
theorem selected_nine_distinct_all_preimages
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length) :
    SighashAllWire.sourceAllPreimage tx selected
      (tenDeletedScript selectedNineZero) ≠
    SighashAllWire.sourceAllPreimage tx selected
      (tenDeletedScript selectedNineOne) := by
  intro same
  exact selected_nine_ten_deletions_different
    (sourceAllPreimage_injective_scriptCode tx selected _ _
      txValid selectedValid
      (tenDeletedScript_width selectedNineZero)
      (tenDeletedScript_width selectedNineOne) same)

end QSB.ScriptSigSighash
