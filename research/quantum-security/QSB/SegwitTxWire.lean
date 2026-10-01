import QSB.JointSourceChecks

/-!
A source-shaped transaction-byte boundary for a version/marker/flag `00 01`
SegWit envelope containing a bare legacy QSB input. The witness fields are
parsed and returned, while the legacy signature-hash checker receives the
transaction's common version, inputs, outputs, and locktime fields. This
proves round trips for this canonical encoding, not equivalence with Core's
complete transaction parser or acceptance of arbitrary witness scripts.
-/
namespace QSB.SegwitTxWire
open QSB.OutputCodec

abbrev Bytes := List UInt8

def witnessItemCodec : PrefixCodec Bytes :=
  lengthPrefixedBytesCodec WireIntegers.compactSizeCodec

def witnessStackCodec : PrefixCodec (List Bytes) where
  valid := fun items =>
    WireIntegers.compactSizeCodec.valid items.length ∧
      ∀ item ∈ items, witnessItemCodec.valid item
  encode := fun items =>
    WireIntegers.compactSizeCodec.encode items.length ++
      encodeItems witnessItemCodec items
  decode := fun bytes => do
    let (count, rest) ← WireIntegers.compactSizeCodec.decode bytes
    decodeItems witnessItemCodec count rest
  roundtrip := by
    intro items valid tail
    simp only [List.append_assoc]
    change (do
      let (count, rest) ← WireIntegers.compactSizeCodec.decode
        (WireIntegers.compactSizeCodec.encode items.length ++
          (encodeItems witnessItemCodec items ++ tail))
      decodeItems witnessItemCodec count rest) = some (items, tail)
    rw [WireIntegers.compactSizeCodec.roundtrip _ valid.1]
    exact decodeItems_encodeItems witnessItemCodec items tail valid.2

def valid (tx : SighashAllWire.TxFields)
    (witnesses : List (List Bytes)) : Prop :=
  SighashAllWire.valid tx ∧
  witnesses.length = tx.inputs.length ∧
  ∀ witness ∈ witnesses, witnessStackCodec.valid witness

def encode (tx : SighashAllWire.TxFields)
    (witnesses : List (List Bytes)) : Bytes :=
  (WireIntegers.fixedLECodec 4).encode tx.version ++
  [0x00, 0x01] ++
  WireIntegers.compactSizeCodec.encode tx.inputs.length ++
  encodeItems SighashAllWire.inputCodec tx.inputs ++
  WireOutputs.encode tx.outputs ++
  encodeItems witnessStackCodec witnesses ++
  (WireIntegers.fixedLECodec 4).encode tx.locktime

/-- Parse the canonical SegWit envelope, preserving the witness stack list
as data and retaining any remaining bytes for a strict caller to reject. -/
def decode (raw : Bytes) :
    Option (SighashAllWire.TxFields × List (List Bytes) × Bytes) := do
  let (version, afterVersion) ←
    (WireIntegers.fixedLECodec 4).decode raw
  let (markerFlag, afterFlag) ← (fixedBytesCodec 2).decode afterVersion
  if markerFlag != [0x00, 0x01] then none else
    let (count, afterCount) ←
      WireIntegers.compactSizeCodec.decode afterFlag
    let (inputs, afterInputs) ←
      decodeItems SighashAllWire.inputCodec count afterCount
    let (outputs, afterOutputs) ← WireOutputs.decode afterInputs
    let (witnesses, afterWitnesses) ←
      decodeItems witnessStackCodec count afterOutputs
    let (locktime, tail) ←
      (WireIntegers.fixedLECodec 4).decode afterWitnesses
    return (⟨version, inputs, outputs, locktime⟩, witnesses, tail)

/-- The parser recovers both the legacy-sighash fields and every witness
stack from a valid canonical witness serialization, at any input count. -/
theorem decode_encode (tx : SighashAllWire.TxFields)
    (witnesses : List (List Bytes))
    (wellFormed : valid tx witnesses) :
    decode (encode tx witnesses) = some (tx, witnesses, []) := by
  unfold decode encode
  simp only [List.append_assoc]
  have hVersion := (WireIntegers.fixedLECodec 4).roundtrip
    tx.version wellFormed.1.1
    ([0x00, 0x01] ++
      WireIntegers.compactSizeCodec.encode tx.inputs.length ++
      encodeItems SighashAllWire.inputCodec tx.inputs ++
      WireOutputs.encode tx.outputs ++
      encodeItems witnessStackCodec witnesses ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
  simp only [List.append_assoc] at hVersion
  rw [hVersion]
  simp
  have hFlag := (fixedBytesCodec 2).roundtrip
    [0x00, 0x01] (by simp [fixedBytesCodec])
    (WireIntegers.compactSizeCodec.encode tx.inputs.length ++
      encodeItems SighashAllWire.inputCodec tx.inputs ++
      WireOutputs.encode tx.outputs ++
      encodeItems witnessStackCodec witnesses ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
  simp only [List.append_assoc] at hFlag
  have hFlag' : (fixedBytesCodec 2).decode
      ([0x00, 0x01] ++
        WireIntegers.compactSizeCodec.encode tx.inputs.length ++
        encodeItems SighashAllWire.inputCodec tx.inputs ++
        WireOutputs.encode tx.outputs ++
        encodeItems witnessStackCodec witnesses ++
        (WireIntegers.fixedLECodec 4).encode tx.locktime) =
      some ([0x00, 0x01],
        WireIntegers.compactSizeCodec.encode tx.inputs.length ++
        encodeItems SighashAllWire.inputCodec tx.inputs ++
        WireOutputs.encode tx.outputs ++
        encodeItems witnessStackCodec witnesses ++
        (WireIntegers.fixedLECodec 4).encode tx.locktime) := by
    simpa only [fixedBytesCodec, List.append_assoc] using hFlag
  simp only [List.cons_append, List.nil_append,
    List.append_assoc] at hFlag'
  rw [hFlag']
  simp
  have hCount := WireIntegers.compactSizeCodec.roundtrip
    tx.inputs.length wellFormed.1.2.1
    (encodeItems SighashAllWire.inputCodec tx.inputs ++
      WireOutputs.encode tx.outputs ++
      encodeItems witnessStackCodec witnesses ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
  simp only [List.append_assoc] at hCount
  rw [hCount]
  simp
  have hInputs := decodeItems_encodeItems SighashAllWire.inputCodec
    tx.inputs
    (WireOutputs.encode tx.outputs ++
      encodeItems witnessStackCodec witnesses ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
    wellFormed.1.2.2.1
  simp only [List.append_assoc] at hInputs
  rw [hInputs]
  simp
  have hOutputs := WireOutputs.decode_encode tx.outputs
    (encodeItems witnessStackCodec witnesses ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
    wellFormed.1.2.2.2.1
  rw [hOutputs]
  simp
  have hWitnesses := decodeItems_encodeItems witnessStackCodec witnesses
    ((WireIntegers.fixedLECodec 4).encode tx.locktime)
    wellFormed.2.2
  rw [← wellFormed.2.1, hWitnesses]
  simp
  have hLocktime := (WireIntegers.fixedLECodec 4).roundtrip
    tx.locktime wellFormed.1.2.2.2.2 []
  simp only [List.append_nil] at hLocktime
  rw [hLocktime]
  rfl

/-- A source-model legacy sighash computed from canonical SegWit bytes is
unaffected by changing only witness stacks. Its equality to compiled Core's
legacy SignatureHash remains an external refinement obligation. -/
def legacyDigestOfRaw (functions : JointSourceChecks.Functions)
    (raw : Bytes) (selected : Nat) (scriptCode : Bytes)
    (hashType : Nat) : Option Bytes := do
  let (tx, _, tail) ← decode raw
  if tail.isEmpty then
    JointSourceChecks.legacyDigest functions tx selected scriptCode hashType
  else none

theorem legacyDigestOfRaw_encode (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (witnesses : List (List Bytes))
    (wellFormed : valid tx witnesses)
    (selected : Nat) (scriptCode : Bytes) (hashType : Nat) :
    legacyDigestOfRaw functions (encode tx witnesses) selected scriptCode
      hashType = JointSourceChecks.legacyDigest functions tx selected
        scriptCode hashType := by
  simp [legacyDigestOfRaw, decode_encode tx witnesses wellFormed]

theorem legacyDigestOfRaw_witness_change
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields)
    (left right : List (List Bytes))
    (leftValid : valid tx left) (rightValid : valid tx right)
    (selected : Nat) (scriptCode : Bytes) (hashType : Nat) :
    legacyDigestOfRaw functions (encode tx left) selected scriptCode hashType =
      legacyDigestOfRaw functions (encode tx right) selected scriptCode
        hashType := by
  rw [legacyDigestOfRaw_encode functions tx left leftValid,
    legacyDigestOfRaw_encode functions tx right rightValid]

end QSB.SegwitTxWire
