import QSB.SegwitTxWire

/-!
Canonical raw legacy transaction framing, separate from the legacy signature
hash *preimage* in `SighashAllWire`. The latter appends a four-byte hash type
and replaces input scripts before hashing; neither change belongs in a raw
transaction. These theorems cover only bytes emitted by this encoder. They do
not establish equivalence with Core's transaction parser or signature checker.
-/
namespace QSB.LegacyTxWire
open QSB.OutputCodec

abbrev Bytes := List UInt8

def encode (tx : SighashAllWire.TxFields) : Bytes :=
  (WireIntegers.fixedLECodec 4).encode tx.version ++
  WireIntegers.compactSizeCodec.encode tx.inputs.length ++
  encodeItems SighashAllWire.inputCodec tx.inputs ++
  WireOutputs.encode tx.outputs ++
  (WireIntegers.fixedLECodec 4).encode tx.locktime

/-- Parse raw legacy fields while retaining trailing bytes for a strict
caller to reject. The absent SegWit marker is a property of the encoded
domain, not a claim about every byte string this partial parser accepts. -/
def decode (raw : Bytes) : Option (SighashAllWire.TxFields × Bytes) := do
  let (version, afterVersion) ← (WireIntegers.fixedLECodec 4).decode raw
  let (count, afterCount) ← WireIntegers.compactSizeCodec.decode afterVersion
  let (inputs, afterInputs) ←
    decodeItems SighashAllWire.inputCodec count afterCount
  let (outputs, afterOutputs) ← WireOutputs.decode afterInputs
  let (locktime, tail) ←
    (WireIntegers.fixedLECodec 4).decode afterOutputs
  return (⟨version, inputs, outputs, locktime⟩, tail)

theorem decode_encode (tx : SighashAllWire.TxFields)
    (wellFormed : SighashAllWire.valid tx) :
    decode (encode tx) = some (tx, []) := by
  unfold decode encode
  simp only [List.append_assoc]
  have hVersion := (WireIntegers.fixedLECodec 4).roundtrip
    tx.version wellFormed.1
    (WireIntegers.compactSizeCodec.encode tx.inputs.length ++
      encodeItems SighashAllWire.inputCodec tx.inputs ++
      WireOutputs.encode tx.outputs ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
  simp only [List.append_assoc] at hVersion
  rw [hVersion]
  simp
  have hCount := WireIntegers.compactSizeCodec.roundtrip
    tx.inputs.length wellFormed.2.1
    (encodeItems SighashAllWire.inputCodec tx.inputs ++
      WireOutputs.encode tx.outputs ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
  simp only [List.append_assoc] at hCount
  rw [hCount]
  simp
  have hInputs := decodeItems_encodeItems SighashAllWire.inputCodec
    tx.inputs
    (WireOutputs.encode tx.outputs ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
    wellFormed.2.2.1
  rw [hInputs]
  simp
  have hOutputs := WireOutputs.decode_encode tx.outputs
    ((WireIntegers.fixedLECodec 4).encode tx.locktime)
    wellFormed.2.2.2.1
  rw [hOutputs]
  simp
  have hLocktime := (WireIntegers.fixedLECodec 4).roundtrip
    tx.locktime wellFormed.2.2.2.2 []
  simp only [List.append_nil] at hLocktime
  rw [hLocktime]
  rfl

/-- Every successful raw legacy parse is exactly its returned transaction's
canonical serialization followed by its reported tail. This is a statement
about the Lean parser, not a compiled-Core parser refinement. -/
theorem decode_sound (raw : Bytes) (tx : SighashAllWire.TxFields)
    (tail : Bytes) (parsed : decode raw = some (tx, tail)) :
    raw = encode tx ++ tail := by
  cases versionEq : (WireIntegers.fixedLECodec 4).decode raw with
  | none => simp [decode, versionEq] at parsed
  | some versionPair =>
    rcases versionPair with ⟨version, afterVersion⟩
    cases countEq : WireIntegers.compactSizeCodec.decode afterVersion with
    | none => simp [decode, versionEq, countEq] at parsed
    | some countPair =>
      rcases countPair with ⟨count, afterCount⟩
      cases inputsEq : decodeItems SighashAllWire.inputCodec count afterCount with
      | none => simp [decode, versionEq, countEq, inputsEq] at parsed
      | some inputsPair =>
        rcases inputsPair with ⟨inputs, afterInputs⟩
        cases outputsEq : WireOutputs.decode afterInputs with
        | none => simp [decode, versionEq, countEq, inputsEq, outputsEq] at parsed
        | some outputsPair =>
          rcases outputsPair with ⟨outputs, afterOutputs⟩
          cases locktimeEq : (WireIntegers.fixedLECodec 4).decode afterOutputs with
          | none =>
              simp [decode, versionEq, countEq, inputsEq, outputsEq,
                locktimeEq] at parsed
          | some locktimePair =>
            rcases locktimePair with ⟨locktime, afterLocktime⟩
            have result :
                (⟨version, inputs, outputs, locktime⟩, afterLocktime) =
                  (tx, tail) := by
              exact Option.some.inj (by
                simpa [decode, versionEq, countEq, inputsEq,
                  outputsEq, locktimeEq] using parsed)
            have hTx : (⟨version, inputs, outputs, locktime⟩ :
                SighashAllWire.TxFields) = tx := by
              simpa using congrArg Prod.fst result
            have hTail : afterLocktime = tail := by
              simpa using congrArg Prod.snd result
            have hVersion := WireIntegers.fixedLECodec_decodeSound 4
              raw version afterVersion versionEq
            have hCount := WireIntegers.compactSizeCodec_decodeSound
              afterVersion count afterCount countEq
            obtain ⟨hLength, hInputs⟩ := decodeItems_sound
              SighashAllWire.inputCodec SighashAllWire.inputCodec_decodeSound
              count afterCount inputs afterInputs inputsEq
            have hOutputs := WireOutputs.decode_sound
              afterInputs outputs afterOutputs outputsEq
            have hLocktime := WireIntegers.fixedLECodec_decodeSound 4
              afterOutputs locktime afterLocktime locktimeEq
            calc
              raw = (WireIntegers.fixedLECodec 4).encode version ++
                  afterVersion := hVersion
              _ = (WireIntegers.fixedLECodec 4).encode version ++
                  WireIntegers.compactSizeCodec.encode count ++
                  afterCount := by rw [hCount, List.append_assoc]
              _ = (WireIntegers.fixedLECodec 4).encode version ++
                  WireIntegers.compactSizeCodec.encode count ++
                  encodeItems SighashAllWire.inputCodec inputs ++
                  afterInputs := by
                    rw [hInputs]
                    simp only [List.append_assoc]
              _ = (WireIntegers.fixedLECodec 4).encode version ++
                  WireIntegers.compactSizeCodec.encode count ++
                  encodeItems SighashAllWire.inputCodec inputs ++
                  WireOutputs.encode outputs ++ afterOutputs := by
                    rw [hOutputs]
                    simp only [List.append_assoc]
              _ = (WireIntegers.fixedLECodec 4).encode version ++
                  WireIntegers.compactSizeCodec.encode count ++
                  encodeItems SighashAllWire.inputCodec inputs ++
                  WireOutputs.encode outputs ++
                  (WireIntegers.fixedLECodec 4).encode locktime ++
                  afterLocktime := by
                    rw [hLocktime]
                    simp only [List.append_assoc]
              _ = encode tx ++ tail := by
                rw [← hTx, ← hTail]
                simp [encode, ← hLength, List.append_assoc]

/-- The source-shaped legacy sighash of a canonical raw legacy transaction.
Actual Core sighash equivalence remains an external refinement obligation. -/
def legacyDigestOfRaw (functions : JointSourceChecks.Functions)
    (raw : Bytes) (selected : Nat) (scriptCode : Bytes)
    (hashType : Nat) : Option Bytes := do
  let (tx, tail) ← decode raw
  if tail.isEmpty then
    JointSourceChecks.legacyDigest functions tx selected scriptCode hashType
  else none

theorem legacyDigestOfRaw_encode (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields)
    (wellFormed : SighashAllWire.valid tx)
    (selected : Nat) (scriptCode : Bytes) (hashType : Nat) :
    legacyDigestOfRaw functions (encode tx) selected scriptCode hashType =
      JointSourceChecks.legacyDigest functions tx selected scriptCode hashType := by
  simp [legacyDigestOfRaw, decode_encode tx wellFormed]

/-- Equal canonical transaction fields give the same modeled legacy sighash
through the raw legacy and SegWit envelopes. This makes explicit that the
witness envelope does not enter the source-shaped legacy preimage. -/
theorem legacy_segwit_same_digest (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (witnesses : List (List Bytes))
    (wellFormed : SegwitTxWire.valid tx witnesses)
    (selected : Nat) (scriptCode : Bytes) (hashType : Nat) :
    legacyDigestOfRaw functions (encode tx) selected scriptCode hashType =
      SegwitTxWire.legacyDigestOfRaw functions
        (SegwitTxWire.encode tx witnesses) selected scriptCode hashType := by
  rw [legacyDigestOfRaw_encode functions tx wellFormed.1,
    SegwitTxWire.legacyDigestOfRaw_encode functions tx witnesses wellFormed]

end QSB.LegacyTxWire
