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

theorem witnessItemCodec_decodeSound : DecodeSound witnessItemCodec := by
  exact lengthPrefixedBytesCodec_decodeSound
    WireIntegers.compactSizeCodec
    WireIntegers.compactSizeCodec_decodeSound

theorem witnessStackCodec_decodeSound : DecodeSound witnessStackCodec := by
  intro raw items tail parsed
  cases countEq : WireIntegers.compactSizeCodec.decode raw with
  | none => simp [witnessStackCodec, countEq] at parsed
  | some countPair =>
    rcases countPair with ⟨count, rest⟩
    have itemsEq : decodeItems witnessItemCodec count rest =
        some (items, tail) := by
      simpa [witnessStackCodec, countEq] using parsed
    obtain ⟨hLength, hItems⟩ := decodeItems_sound witnessItemCodec
      witnessItemCodec_decodeSound count rest items tail itemsEq
    have hCount := WireIntegers.compactSizeCodec_decodeSound
      raw count rest countEq
    change raw = WireIntegers.compactSizeCodec.encode items.length ++
      encodeItems witnessItemCodec items ++ tail
    calc
      raw = WireIntegers.compactSizeCodec.encode count ++ rest := hCount
      _ = WireIntegers.compactSizeCodec.encode items.length ++
          encodeItems witnessItemCodec items ++ tail := by
        rw [hLength, hItems, List.append_assoc]

/-- Core's SegWit envelope requires at least one nonempty witness stack;
otherwise it rejects the serialization as a superfluous witness record. -/
def hasWitness (witnesses : List (List Bytes)) : Bool :=
  witnesses.any (fun stack => !stack.isEmpty)

def valid (tx : SighashAllWire.TxFields)
    (witnesses : List (List Bytes)) : Prop :=
  SighashAllWire.valid tx ∧
  witnesses.length = tx.inputs.length ∧
  (∀ witness ∈ witnesses, witnessStackCodec.valid witness) ∧
  hasWitness witnesses = true

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
    if hasWitness witnesses then
      let (locktime, tail) ←
        (WireIntegers.fixedLECodec 4).decode afterWitnesses
      return (⟨version, inputs, outputs, locktime⟩, witnesses, tail)
    else none

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
    wellFormed.2.2.1
  rw [← wellFormed.2.1, hWitnesses]
  simp [wellFormed.2.2.2]
  have hLocktime := (WireIntegers.fixedLECodec 4).roundtrip
    tx.locktime wellFormed.1.2.2.2.2 []
  simp only [List.append_nil] at hLocktime
  rw [hLocktime]
  rfl

/-- A successful source-model SegWit parse consumes exactly the canonical
marker/flag envelope, including all witness stacks, followed by the returned
tail. Equality with compiled Core deserialization remains external. -/
theorem decode_sound (raw : Bytes) (tx : SighashAllWire.TxFields)
    (witnesses : List (List Bytes)) (tail : Bytes)
    (parsed : decode raw = some (tx, witnesses, tail)) :
    raw = encode tx witnesses ++ tail := by
  cases versionEq : (WireIntegers.fixedLECodec 4).decode raw with
  | none => simp [decode, versionEq] at parsed
  | some versionPair =>
    rcases versionPair with ⟨version, afterVersion⟩
    cases flagEq : (fixedBytesCodec 2).decode afterVersion with
    | none => simp [decode, versionEq, flagEq] at parsed
    | some flagPair =>
      rcases flagPair with ⟨flag, afterFlag⟩
      by_cases correctFlag : flag = [0x00, 0x01]
      · cases countEq : WireIntegers.compactSizeCodec.decode afterFlag with
        | none =>
            simp [decode, versionEq, flagEq, correctFlag, countEq] at parsed
        | some countPair =>
          rcases countPair with ⟨count, afterCount⟩
          cases inputsEq : decodeItems SighashAllWire.inputCodec count
              afterCount with
          | none =>
              simp [decode, versionEq, flagEq, correctFlag,
                countEq, inputsEq] at parsed
          | some inputsPair =>
            rcases inputsPair with ⟨inputs, afterInputs⟩
            cases outputsEq : WireOutputs.decode afterInputs with
            | none =>
                simp [decode, versionEq, flagEq, correctFlag,
                  countEq, inputsEq, outputsEq] at parsed
            | some outputsPair =>
              rcases outputsPair with ⟨outputs, afterOutputs⟩
              cases witnessesEq : decodeItems witnessStackCodec count
                  afterOutputs with
              | none =>
                  simp [decode, versionEq, flagEq, correctFlag,
                    countEq, inputsEq, outputsEq, witnessesEq] at parsed
              | some witnessesPair =>
                rcases witnessesPair with ⟨parsedWitnesses, afterWitnesses⟩
                cases hasEq : hasWitness parsedWitnesses with
                | false =>
                    simp [decode, versionEq, flagEq, correctFlag, countEq,
                      inputsEq, outputsEq, witnessesEq, hasEq] at parsed
                | true =>
                  cases locktimeEq : (WireIntegers.fixedLECodec 4).decode
                      afterWitnesses with
                  | none =>
                      simp [decode, versionEq, flagEq, correctFlag, countEq,
                        inputsEq, outputsEq, witnessesEq, hasEq,
                        locktimeEq] at parsed
                  | some locktimePair =>
                    rcases locktimePair with ⟨locktime, afterLocktime⟩
                    have result :
                        (⟨version, inputs, outputs, locktime⟩,
                          parsedWitnesses, afterLocktime) =
                          (tx, witnesses, tail) := by
                      exact Option.some.inj (by
                        simpa [decode, versionEq, flagEq, correctFlag,
                          countEq, inputsEq, outputsEq, witnessesEq, hasEq,
                          locktimeEq] using parsed)
                    have hTx : (⟨version, inputs, outputs, locktime⟩ :
                        SighashAllWire.TxFields) = tx := by
                      simpa using congrArg Prod.fst result
                    have hWitnesses : parsedWitnesses = witnesses := by
                      simpa using congrArg (fun p => p.2.1) result
                    have hTail : afterLocktime = tail := by
                      simpa using congrArg (fun p => p.2.2) result
                    have hVersion := WireIntegers.fixedLECodec_decodeSound 4
                      raw version afterVersion versionEq
                    have hFlag := fixedBytesCodec_decodeSound 2
                      afterVersion flag afterFlag flagEq
                    have hCount := WireIntegers.compactSizeCodec_decodeSound
                      afterFlag count afterCount countEq
                    obtain ⟨hInputLength, hInputs⟩ := decodeItems_sound
                      SighashAllWire.inputCodec
                      SighashAllWire.inputCodec_decodeSound
                      count afterCount inputs afterInputs inputsEq
                    have hOutputs := WireOutputs.decode_sound
                      afterInputs outputs afterOutputs outputsEq
                    obtain ⟨_, hWitnessBytes⟩ := decodeItems_sound
                      witnessStackCodec witnessStackCodec_decodeSound
                      count afterOutputs parsedWitnesses afterWitnesses
                      witnessesEq
                    have hLocktime := WireIntegers.fixedLECodec_decodeSound 4
                      afterWitnesses locktime afterLocktime locktimeEq
                    calc
                      raw = (WireIntegers.fixedLECodec 4).encode version ++
                          afterVersion := hVersion
                      _ = (WireIntegers.fixedLECodec 4).encode version ++
                          flag ++ afterFlag := by
                            rw [hFlag]
                            simp [fixedBytesCodec, List.append_assoc]
                      _ = (WireIntegers.fixedLECodec 4).encode version ++
                          flag ++ WireIntegers.compactSizeCodec.encode count ++
                          afterCount := by
                            rw [hCount]
                            simp only [List.append_assoc]
                      _ = (WireIntegers.fixedLECodec 4).encode version ++
                          flag ++ WireIntegers.compactSizeCodec.encode count ++
                          encodeItems SighashAllWire.inputCodec inputs ++
                          afterInputs := by
                            rw [hInputs]
                            simp only [List.append_assoc]
                      _ = (WireIntegers.fixedLECodec 4).encode version ++
                          flag ++ WireIntegers.compactSizeCodec.encode count ++
                          encodeItems SighashAllWire.inputCodec inputs ++
                          WireOutputs.encode outputs ++ afterOutputs := by
                            rw [hOutputs]
                            simp only [List.append_assoc]
                      _ = (WireIntegers.fixedLECodec 4).encode version ++
                          flag ++ WireIntegers.compactSizeCodec.encode count ++
                          encodeItems SighashAllWire.inputCodec inputs ++
                          WireOutputs.encode outputs ++
                          encodeItems witnessStackCodec parsedWitnesses ++
                          afterWitnesses := by
                            rw [hWitnessBytes]
                            simp only [List.append_assoc]
                      _ = (WireIntegers.fixedLECodec 4).encode version ++
                          flag ++ WireIntegers.compactSizeCodec.encode count ++
                          encodeItems SighashAllWire.inputCodec inputs ++
                          WireOutputs.encode outputs ++
                          encodeItems witnessStackCodec parsedWitnesses ++
                          (WireIntegers.fixedLECodec 4).encode locktime ++
                          afterLocktime := by
                            rw [hLocktime]
                            simp only [List.append_assoc]
                      _ = encode tx witnesses ++ tail := by
                            rw [← hTx, ← hWitnesses, ← hTail, correctFlag]
                            simp [encode, ← hInputLength, List.append_assoc]
      · simp [decode, versionEq, flagEq, correctFlag] at parsed

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
