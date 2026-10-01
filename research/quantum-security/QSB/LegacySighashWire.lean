import QSB.SighashAllWire

/-!
Source-shaped Bitcoin Core 27.2 legacy signature-hash serialization for all
32-bit hash types. The low five bits select NONE (2), SINGLE (3), or the
ALL-like branch; bit 7 selects ANYONECANPAY. Other bits remain in the final
four-byte hash-type field. The input `scriptCode` is assumed to have already
undergone the applicable FindAndDelete and opcode-boundary CODESEPARATOR
removal. This file does not prove refinement to C++ or model ECDSA.

`sourcePreimage = none` means the selected input is absent or Core returns
`uint256::ONE` for out-of-range SINGLE. Only the latter is reachable from a
consensus-accepted input; `singleBugDigest` records its raw 32 digest bytes.
-/
namespace QSB.LegacySighashWire

open QSB.OutputCodec
open QSB.SighashAllWire

def baseType (hashType : Nat) : Nat := hashType % 32

def anyoneCanPay (hashType : Nat) : Bool := hashType % 256 ≥ 128

def blankOtherSequence (hashType : Nat) : Bool :=
  baseType hashType == 2 || baseType hashType == 3

def preparedInput (selected position : Nat) (scriptCode : Bytes)
    (hashType : Nat) (input : InputFields) : InputFields :=
  let script := if position = selected then scriptCode else []
  let sequence := if position ≠ selected && blankOtherSequence hashType
    then 0 else input.2.2.2
  (input.1, (input.2.1, (script, sequence)))

def preparedInputsAt (selected : Nat) (scriptCode : Bytes)
    (hashType : Nat) : Nat → List InputFields → List InputFields
  | _, [] => []
  | position, input :: rest =>
      preparedInput selected position scriptCode hashType input ::
        preparedInputsAt selected scriptCode hashType (position + 1) rest

theorem preparedInputsAt_all (selected : Nat) (scriptCode : Bytes)
    (position : Nat) (inputs : List InputFields) :
    preparedInputsAt selected scriptCode 1 position inputs =
      SighashAllWire.prepareInputsAt selected scriptCode position inputs := by
  induction inputs generalizing position with
  | nil => rfl
  | cons input rest ih =>
      simp [preparedInputsAt, SighashAllWire.prepareInputsAt,
        preparedInput, blankOtherSequence, baseType,
        SighashAllWire.withScript, ih]

def signedInputs (tx : TxFields) (selected : Nat) (scriptCode : Bytes)
    (hashType : Nat) : List InputFields :=
  if anyoneCanPay hashType then
    (tx.inputs[selected]?.map (preparedInput selected selected scriptCode hashType)).toList
  else
    preparedInputsAt selected scriptCode hashType 0 tx.inputs

def encodeOutput (output : Game.Output) : Bytes :=
  (outputCodec WireIntegers.nonnegativeAmountCodec
    (lengthPrefixedBytesCodec WireIntegers.compactSizeCodec)).encode output

/-- `CTxOut()` is a negative-one amount and empty script. It is deliberately
not represented as a valid `Game.Output`, whose amounts are nonnegative. -/
def nullOutputBytes : Bytes :=
  WireIntegers.leBytes 8 (256 ^ 8 - 1) ++
    WireIntegers.compactSizeEncode 0

def encodeOutputs (tx : TxFields) (selected : Nat) (hashType : Nat) : Bytes :=
  if baseType hashType == 2 then
    WireIntegers.compactSizeEncode 0
  else if baseType hashType == 3 then
    WireIntegers.compactSizeEncode (selected + 1) ++
      (List.replicate selected nullOutputBytes).flatten ++
      (tx.outputs[selected]?.map encodeOutput).getD []
  else
    WireOutputs.encode tx.outputs

/-- The preimage for a valid signed input except the SINGLE bug. A caller must
restrict `hashType < 2^32` to match Core's signed 32-bit hash-type argument. -/
def sourcePreimage (tx : TxFields) (selected : Nat) (scriptCode : Bytes)
    (hashType : Nat) : Option Bytes :=
  if selected ≥ tx.inputs.length then none
  else if baseType hashType == 3 && selected ≥ tx.outputs.length then none
  else
    let inputs := signedInputs tx selected scriptCode hashType
    some (WireIntegers.leBytes 4 tx.version ++
      WireIntegers.compactSizeEncode inputs.length ++
      OutputCodec.encodeItems inputCodec inputs ++
      encodeOutputs tx selected hashType ++
      WireIntegers.leBytes 4 tx.locktime ++
      WireIntegers.leBytes 4 hashType)

/-- Raw internal `uint256::ONE` bytes, which ECDSA reads as a big-endian
scalar of 2^248. It is not SHA256d of a transaction preimage. -/
def singleBugDigest : Bytes := UInt8.ofNat 1 :: List.replicate 31 (UInt8.ofNat 0)

theorem single_out_of_range (tx : TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat)
    (inputValid : selected < tx.inputs.length)
    (single : baseType hashType = 3)
    (outputMissing : tx.outputs.length ≤ selected) :
    sourcePreimage tx selected scriptCode hashType = none := by
  simp [sourcePreimage, Nat.not_le.mpr inputValid,
    single, outputMissing]

theorem all_preimage (tx : TxFields) (selected : Nat)
    (scriptCode : Bytes) (inputValid : selected < tx.inputs.length) :
    sourcePreimage tx selected scriptCode 1 =
      some (SighashAllWire.sourceAllPreimage tx selected scriptCode) := by
  simp [sourcePreimage, inputValid, baseType, anyoneCanPay,
    signedInputs, preparedInputsAt_all,
    encodeOutputs, SighashAllWire.sourceAllPreimage,
    SighashAllWire.encode, SighashAllWire.prepareAll,
    WireIntegers.fixedLECodec, WireIntegers.compactSizeCodec]

end QSB.LegacySighashWire
