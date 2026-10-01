import QSB.WireOutputs

/-!
Source-shaped complete legacy SIGHASH_ALL preimage layout. The inputs here
already contain the signature-hash script for each input (selected scriptCode
for the signed input, empty scripts for the others). This module proves that
the ordered outputs can be parsed from every valid encoding even when those
input scripts, counts, version, and locktime vary between transactions.

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

end QSB.SighashAllWire
