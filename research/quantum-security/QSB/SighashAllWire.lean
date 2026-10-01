import QSB.WireOutputs

/-!
Source-shaped complete legacy SIGHASH_ALL preimage layout. `encode` takes
inputs that already contain the signature-hash script for each input.
`sourceAllPreimage` prepares those inputs from an original transaction by
substituting the supplied scriptCode for the signed input and blanking all
other input scripts. This module proves that the ordered outputs can be parsed
from every valid encoding even when those input scripts, counts, version, and
locktime vary between transactions.

It does not prove that Core's C++ serializer emits these bytes for an arbitrary
accepted witness, or that its selected scriptCode agrees with the reached
FindAndDelete model. It also does not model ECDSA or hash probabilities.
-/
namespace QSB.SighashAllWire

open QSB.OutputCodec

abbrev InputFields := Bytes × (Nat × (Bytes × Nat))

def inputCodec : PrefixCodec InputFields :=
  productCodec (fixedBytesCodec 32)
    (productCodec (WireIntegers.fixedLECodec 4)
      (productCodec (lengthPrefixedBytesCodec WireIntegers.compactSizeCodec)
        (WireIntegers.fixedLECodec 4)))

/- `version` stores its 32-bit wire pattern as a Nat, so even a semantically
negative C++ int32 version can be represented after conversion. The input
fields likewise carry the raw previous txid and unsigned wire indices. -/
structure TxFields where
  version : Nat
  inputs : List InputFields
  outputs : List Game.Output
  locktime : Nat

def valid (tx : TxFields) : Prop :=
  tx.version < 256 ^ 4 ∧
  tx.inputs.length < 256 ^ 8 ∧
  (∀ inp ∈ tx.inputs, inputCodec.valid inp) ∧
  WireOutputs.validOutputs tx.outputs ∧
  tx.locktime < 256 ^ 4

def encode (tx : TxFields) : Bytes :=
  (WireIntegers.fixedLECodec 4).encode tx.version ++
  WireIntegers.compactSizeCodec.encode tx.inputs.length ++
  encodeItems inputCodec tx.inputs ++
  WireOutputs.encode tx.outputs ++
  (WireIntegers.fixedLECodec 4).encode tx.locktime ++
  (WireIntegers.fixedLECodec 4).encode 1

/-- Parse the preimage only as far as the output list. The locktime and
four-byte hash type are remaining suffix bytes and need not be interpreted
to recover the output projection. -/
def decodeOutputs (preimage : Bytes) : Option (List Game.Output) := do
  let (_, afterVersion) ← (WireIntegers.fixedLECodec 4).decode preimage
  let (nInputs, afterCount) ← WireIntegers.compactSizeCodec.decode afterVersion
  let (_, afterInputs) ← OutputCodec.decodeItems inputCodec nInputs afterCount
  let (outputs, _) ← WireOutputs.decode afterInputs
  return outputs

theorem decodeOutputs_encode (tx : TxFields) (wellFormed : valid tx) :
    decodeOutputs (encode tx) = some tx.outputs := by
  unfold decodeOutputs encode
  simp only [List.append_assoc]
  have hVersion := (WireIntegers.fixedLECodec 4).roundtrip
    tx.version wellFormed.1
    (WireIntegers.compactSizeCodec.encode tx.inputs.length ++
      encodeItems inputCodec tx.inputs ++
      WireOutputs.encode tx.outputs ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime ++
      (WireIntegers.fixedLECodec 4).encode 1)
  simp only [List.append_assoc] at hVersion
  rw [hVersion]
  simp
  have hCount := WireIntegers.compactSizeCodec.roundtrip
    tx.inputs.length wellFormed.2.1
    (encodeItems inputCodec tx.inputs ++ WireOutputs.encode tx.outputs ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime ++
      (WireIntegers.fixedLECodec 4).encode 1)
  simp only [List.append_assoc] at hCount
  rw [hCount]
  simp
  have hInputs := OutputCodec.decodeItems_encodeItems inputCodec tx.inputs
    (WireOutputs.encode tx.outputs ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime ++
      (WireIntegers.fixedLECodec 4).encode 1) wellFormed.2.2.1
  simp only [List.append_assoc] at hInputs
  rw [hInputs]
  simp
  have hOutputs := WireOutputs.decode_encode tx.outputs
    ((WireIntegers.fixedLECodec 4).encode tx.locktime ++
      (WireIntegers.fixedLECodec 4).encode 1) wellFormed.2.2.2.1
  rw [hOutputs]
  rfl

theorem changed_outputs_distinct_preimages
    {released attempted : TxFields}
    (releasedValid : valid released) (attemptedValid : valid attempted)
    (changed : attempted.outputs ≠ released.outputs) :
    encode attempted ≠ encode released := by
  intro same
  have parsed := congrArg decodeOutputs same
  rw [decodeOutputs_encode attempted attemptedValid,
    decodeOutputs_encode released releasedValid] at parsed
  exact changed (Option.some.inj parsed)

/-- Source-shaped BASE/ALL input preparation: put the selected scriptCode in
the signed input and blank every other original scriptSig. In the actual
Core path, the selected scriptCode is produced by opcode-boundary
FindAndDelete before this serializer runs. -/
def withScript (input : InputFields) (script : Bytes) : InputFields :=
  (input.1, (input.2.1, (script, input.2.2.2)))

def prepareInputsAt (selected : Nat) (scriptCode : Bytes) :
    Nat → List InputFields → List InputFields
  | _, [] => []
  | position, input :: rest =>
      withScript input (if position = selected then scriptCode else []) ::
        prepareInputsAt selected scriptCode (position + 1) rest

theorem prepareInputsAt_length (selected : Nat) (scriptCode : Bytes)
    (position : Nat) (inputs : List InputFields) :
    (prepareInputsAt selected scriptCode position inputs).length = inputs.length := by
  induction inputs generalizing position with
  | nil => rfl
  | cons _ rest ih => simp [prepareInputsAt, ih]

theorem withScript_valid (input : InputFields) (script : Bytes)
    (inputValid : inputCodec.valid input)
    (scriptValid : script.length < 256 ^ 8) :
    inputCodec.valid (withScript input script) := by
  rcases input with ⟨txid, vout, oldScript, sequence⟩
  change txid.length = 32 ∧ vout < 256 ^ 4 ∧
    oldScript.length < 256 ^ 8 ∧ sequence < 256 ^ 4 at inputValid
  change txid.length = 32 ∧ vout < 256 ^ 4 ∧
    script.length < 256 ^ 8 ∧ sequence < 256 ^ 4
  exact ⟨inputValid.1, inputValid.2.1, scriptValid, inputValid.2.2.2⟩

theorem prepareInputsAt_valid (selected : Nat) (scriptCode : Bytes)
    (scriptValid : scriptCode.length < 256 ^ 8)
    (position : Nat) (inputs : List InputFields)
    (inputsValid : ∀ input ∈ inputs, inputCodec.valid input) :
    ∀ input ∈ prepareInputsAt selected scriptCode position inputs,
      inputCodec.valid input := by
  induction inputs generalizing position with
  | nil => simp [prepareInputsAt]
  | cons input rest ih =>
      intro candidate present
      simp only [prepareInputsAt, List.mem_cons] at present
      rcases present with rfl | inRest
      · apply withScript_valid input
        · exact inputsValid input (by simp)
        · split_ifs
          · exact scriptValid
          · norm_num
      · exact ih (position + 1) (by
          intro value member
          exact inputsValid value (by simp [member])) candidate inRest

def prepareAll (tx : TxFields) (selected : Nat) (scriptCode : Bytes) : TxFields :=
  { tx with inputs := prepareInputsAt selected scriptCode 0 tx.inputs }

theorem prepareAll_valid (tx : TxFields) (selected : Nat)
    (scriptCode : Bytes) (txValid : valid tx)
    (scriptValid : scriptCode.length < 256 ^ 8) :
    valid (prepareAll tx selected scriptCode) := by
  rcases txValid with ⟨versionValid, countValid, inputsValid,
    outputsValid, locktimeValid⟩
  exact ⟨versionValid,
    by simpa [prepareAll, prepareInputsAt_length] using countValid,
    prepareInputsAt_valid selected scriptCode scriptValid 0 tx.inputs inputsValid,
    outputsValid, locktimeValid⟩

def sourceAllPreimage (tx : TxFields) (selected : Nat)
    (scriptCode : Bytes) : Bytes :=
  encode (prepareAll tx selected scriptCode)

/-- The source-shaped serializer's output projection is recoverable for any
original scriptSig bytes and any selected scriptCode in the wire domain. -/
theorem decodeOutputs_sourceAllPreimage (tx : TxFields) (selected : Nat)
    (scriptCode : Bytes) (txValid : valid tx)
    (scriptValid : scriptCode.length < 256 ^ 8) :
    decodeOutputs (sourceAllPreimage tx selected scriptCode) =
      some tx.outputs := by
  exact decodeOutputs_encode (prepareAll tx selected scriptCode)
    (prepareAll_valid tx selected scriptCode txValid scriptValid)

theorem changed_outputs_sourceAll_distinct_preimages
    {released attempted : TxFields}
    (releasedSelected attemptedSelected : Nat)
    (releasedScript attemptedScript : Bytes)
    (releasedValid : valid released) (attemptedValid : valid attempted)
    (releasedScriptValid : releasedScript.length < 256 ^ 8)
    (attemptedScriptValid : attemptedScript.length < 256 ^ 8)
    (changed : attempted.outputs ≠ released.outputs) :
    sourceAllPreimage attempted attemptedSelected attemptedScript ≠
      sourceAllPreimage released releasedSelected releasedScript := by
  intro same
  have parsed := congrArg decodeOutputs same
  rw [decodeOutputs_sourceAllPreimage attempted attemptedSelected
      attemptedScript attemptedValid attemptedScriptValid,
    decodeOutputs_sourceAllPreimage released releasedSelected
      releasedScript releasedValid releasedScriptValid] at parsed
  exact changed (Option.some.inj parsed)

end QSB.SighashAllWire
