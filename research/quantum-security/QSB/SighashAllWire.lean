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

theorem inputCodec_decodeSound : DecodeSound inputCodec := by
  unfold inputCodec
  apply productCodec_decodeSound
  · exact fixedBytesCodec_decodeSound 32
  · apply productCodec_decodeSound
    · exact WireIntegers.fixedLECodec_decodeSound 4
    · apply productCodec_decodeSound
      · exact lengthPrefixedBytesCodec_decodeSound
          WireIntegers.compactSizeCodec
          WireIntegers.compactSizeCodec_decodeSound
      · exact WireIntegers.fixedLECodec_decodeSound 4

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

/-- Parse every field of the source-shaped legacy ALL preimage, including
the fixed four-byte hash type and any trailing bytes. Keeping the tail in the
result makes the framing theorem independent of a closed-input assumption. -/
def decodeFull (preimage : Bytes) : Option (TxFields × Nat × Bytes) := do
  let (version, afterVersion) ← (WireIntegers.fixedLECodec 4).decode preimage
  let (nInputs, afterCount) ← WireIntegers.compactSizeCodec.decode afterVersion
  let (inputs, afterInputs) ← OutputCodec.decodeItems inputCodec nInputs afterCount
  let (outputs, afterOutputs) ← WireOutputs.decode afterInputs
  let (locktime, afterLocktime) ←
    (WireIntegers.fixedLECodec 4).decode afterOutputs
  let (hashType, tail) ← (WireIntegers.fixedLECodec 4).decode afterLocktime
  return (⟨version, inputs, outputs, locktime⟩, hashType, tail)

/-- The full source-shaped ALL serializer has an unambiguous parse on valid
wire fields. This proves the framed bytes determine version, ordered inputs,
ordered outputs, and locktime; it does not identify Core's C++ serializer. -/
theorem decodeFull_encode (tx : TxFields) (wellFormed : valid tx) :
    decodeFull (encode tx) = some (tx, 1, []) := by
  unfold decodeFull encode
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
  simp
  have hLocktime := (WireIntegers.fixedLECodec 4).roundtrip
    tx.locktime wellFormed.2.2.2.2
    ((WireIntegers.fixedLECodec 4).encode 1)
  rw [hLocktime]
  simp
  have hHashType := (WireIntegers.fixedLECodec 4).roundtrip
    1 (by norm_num : 1 < 256 ^ 4) []
  simp only [List.append_nil] at hHashType
  rw [hHashType]
  rfl

theorem encode_injective_on {left right : TxFields}
    (leftValid : valid left) (rightValid : valid right)
    (same : encode left = encode right) : left = right := by
  have decoded := congrArg decodeFull same
  rw [decodeFull_encode left leftValid,
    decodeFull_encode right rightValid] at decoded
  exact congrArg Prod.fst (Option.some.inj decoded)

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

/-- The bytes that `SIGHASH_ALL` commits about an input independently of its
scriptSig: the ordered previous outpoint and sequence. -/
def inputReference (input : InputFields) : Game.Outpoint × Nat :=
  (⟨input.1, input.2.1⟩, input.2.2.2)

structure CommittedFields where
  version : Nat
  inputRefs : List (Game.Outpoint × Nat)
  outputs : List Game.Output
  locktime : Nat
  deriving DecidableEq

def committedFields (tx : TxFields) : CommittedFields :=
  ⟨tx.version, tx.inputs.map inputReference, tx.outputs, tx.locktime⟩

theorem inputReference_withScript (input : InputFields)
    (script : Bytes) :
    inputReference (withScript input script) = inputReference input := by
  rcases input with ⟨txid, index, oldScript, sequence⟩
  rfl

theorem prepareInputsAt_references (selected : Nat) (scriptCode : Bytes)
    (position : Nat) (inputs : List InputFields) :
    (prepareInputsAt selected scriptCode position inputs).map inputReference =
      inputs.map inputReference := by
  induction inputs generalizing position with
  | nil => rfl
  | cons input rest ih =>
      simp [prepareInputsAt, inputReference_withScript, ih]

theorem committedFields_prepareAll (tx : TxFields) (selected : Nat)
    (scriptCode : Bytes) :
    committedFields (prepareAll tx selected scriptCode) =
      committedFields tx := by
  rcases tx with ⟨version, inputs, outputs, locktime⟩
  simp [committedFields, prepareAll, prepareInputsAt_references]

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

/-- For any two valid source-shaped ALL transactions, even with different
input scripts, signed input positions, and selected scriptCodes, equal
preimages imply equal version, ordered outpoints and sequences, ordered
outputs, and locktime. The statement is about serialized bytes, not digest
collision resistance or compiled Core. -/
theorem equal_sourceAllPreimage_committedFields
    {left right : TxFields} (leftSelected rightSelected : Nat)
    (leftScript rightScript : Bytes)
    (leftValid : valid left) (rightValid : valid right)
    (leftScriptValid : leftScript.length < 256 ^ 8)
    (rightScriptValid : rightScript.length < 256 ^ 8)
    (same : sourceAllPreimage left leftSelected leftScript =
      sourceAllPreimage right rightSelected rightScript) :
    committedFields left = committedFields right := by
  have preparedEqual :
      prepareAll left leftSelected leftScript =
        prepareAll right rightSelected rightScript :=
    encode_injective_on
      (prepareAll_valid left leftSelected leftScript
        leftValid leftScriptValid)
      (prepareAll_valid right rightSelected rightScript
        rightValid rightScriptValid) same
  calc
    committedFields left =
        committedFields (prepareAll left leftSelected leftScript) :=
      (committedFields_prepareAll left leftSelected leftScript).symm
    _ = committedFields (prepareAll right rightSelected rightScript) :=
      congrArg committedFields preparedEqual
    _ = committedFields right :=
      committedFields_prepareAll right rightSelected rightScript

theorem changed_committedFields_sourceAll_distinct_preimages
    {released attempted : TxFields}
    (releasedSelected attemptedSelected : Nat)
    (releasedScript attemptedScript : Bytes)
    (releasedValid : valid released) (attemptedValid : valid attempted)
    (releasedScriptValid : releasedScript.length < 256 ^ 8)
    (attemptedScriptValid : attemptedScript.length < 256 ^ 8)
    (changed : committedFields attempted ≠ committedFields released) :
    sourceAllPreimage attempted attemptedSelected attemptedScript ≠
      sourceAllPreimage released releasedSelected releasedScript := by
  intro same
  exact changed (equal_sourceAllPreimage_committedFields
    attemptedSelected releasedSelected attemptedScript releasedScript
    attemptedValid releasedValid attemptedScriptValid releasedScriptValid same)

/-- A fixed ledger resolves the signed outpoints to the previous outputs
needed for fee authorization. This is an explicit ledger-context parameter;
the preimage itself does not contain previous-output amounts. -/
def projectionOfCommitted (ledger : Game.Outpoint → Game.Output)
    (fields : CommittedFields) : Game.Projection :=
  { version := fields.version
    inputs := fields.inputRefs.map Prod.fst
    sequences := fields.inputRefs.map Prod.snd
    locktime := fields.locktime
    outputs := fields.outputs
    previousOutputs := (fields.inputRefs.map Prod.fst).map ledger }

def projectionWithLedger (ledger : Game.Outpoint → Game.Output)
    (tx : TxFields) : Game.Projection :=
  projectionOfCommitted ledger (committedFields tx)

theorem equal_sourceAllPreimage_projectionWithLedger
    (ledger : Game.Outpoint → Game.Output)
    {left right : TxFields} (leftSelected rightSelected : Nat)
    (leftScript rightScript : Bytes)
    (leftValid : valid left) (rightValid : valid right)
    (leftScriptValid : leftScript.length < 256 ^ 8)
    (rightScriptValid : rightScript.length < 256 ^ 8)
    (same : sourceAllPreimage left leftSelected leftScript =
      sourceAllPreimage right rightSelected rightScript) :
    projectionWithLedger ledger left = projectionWithLedger ledger right :=
  congrArg (projectionOfCommitted ledger)
    (equal_sourceAllPreimage_committedFields leftSelected rightSelected
      leftScript rightScript leftValid rightValid
      leftScriptValid rightScriptValid same)

/-- A transaction with an owner-forbidden semantic projection has a distinct
source-shaped ALL preimage from every approved release in the same fixed
ledger context. This includes changed prevouts, sequences, version, locktime,
outputs, or the fee induced by the resolved previous outputs. -/
theorem unauthorized_sourceAll_distinct_preimage
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    {released attempted : TxFields}
    (releasedSelected attemptedSelected : Nat)
    (releasedScript attemptedScript : Bytes)
    (releasedValid : valid released) (attemptedValid : valid attempted)
    (releasedScriptValid : releasedScript.length < 256 ^ 8)
    (attemptedScriptValid : attemptedScript.length < 256 ^ 8)
    (approved : projectionWithLedger ledger released ∈ authorized)
    (forbidden : projectionWithLedger ledger attempted ∉ authorized) :
    sourceAllPreimage attempted attemptedSelected attemptedScript ≠
      sourceAllPreimage released releasedSelected releasedScript := by
  intro same
  have equalProjection := equal_sourceAllPreimage_projectionWithLedger
    ledger attemptedSelected releasedSelected attemptedScript releasedScript
    attemptedValid releasedValid attemptedScriptValid releasedScriptValid same
  apply forbidden
  rw [equalProjection]
  exact approved

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
