import QSB.LegacyTxWire

/-!
Source-shaped transaction-format dispatch for transactions with at least one
input. Core v27.2 first reads a CompactSize input vector; when that vector is
empty and witness serialization is allowed, the next byte is an optional-data
flag. A consensus-valid spend has a nonempty input vector, so the recognized
raw forms here are the ordinary legacy envelope and marker/flag `00 01`
SegWit envelope. This remains a Lean parser, not a compiled-Core refinement.
-/
namespace QSB.TransactionEnvelopeWire
open QSB.OutputCodec

abbrev Bytes := List UInt8

inductive Envelope where
  | legacy (tx : SighashAllWire.TxFields)
  | segwit (tx : SighashAllWire.TxFields)
      (witnesses : List (List Bytes))

def fields : Envelope → SighashAllWire.TxFields
  | .legacy tx => tx
  | .segwit tx _ => tx

def encode : Envelope → Bytes
  | .legacy tx => LegacyTxWire.encode tx
  | .segwit tx witnesses => SegwitTxWire.encode tx witnesses

/-- Dispatch on Core's initial input-vector count, retaining a tail so that
the strict caller can require complete consumption. The zero-input legacy
case is excluded because it cannot be a consensus-valid spend. -/
def decode (raw : Bytes) : Option (Envelope × Bytes) := do
  let (_, afterVersion) ← (WireIntegers.fixedLECodec 4).decode raw
  let (initialCount, _) ← WireIntegers.compactSizeCodec.decode afterVersion
  if initialCount == 0 then
    let (tx, witnesses, tail) ← SegwitTxWire.decode raw
    if tx.inputs.isEmpty then none else
      return (.segwit tx witnesses, tail)
  else
    let (tx, tail) ← LegacyTxWire.decode raw
    if tx.inputs.isEmpty then none else
      return (.legacy tx, tail)

def decodeStrict (raw : Bytes) : Option Envelope := do
  let (envelope, tail) ← decode raw
  if tail.isEmpty then some envelope else none

/-- A valid canonical legacy transaction with an input takes the nonzero
initial-vector branch and is recovered by the combined parser. -/
theorem decode_legacy_encode (tx : SighashAllWire.TxFields)
    (wellFormed : SighashAllWire.valid tx)
    (nonempty : tx.inputs ≠ []) :
    decode (LegacyTxWire.encode tx) = some (.legacy tx, []) := by
  have hVersion : (WireIntegers.fixedLECodec 4).decode
      (LegacyTxWire.encode tx) =
      some (tx.version,
        WireIntegers.compactSizeCodec.encode tx.inputs.length ++
        encodeItems SighashAllWire.inputCodec tx.inputs ++
        WireOutputs.encode tx.outputs ++
        (WireIntegers.fixedLECodec 4).encode tx.locktime) := by
    have h := (WireIntegers.fixedLECodec 4).roundtrip
      tx.version wellFormed.1
      (WireIntegers.compactSizeCodec.encode tx.inputs.length ++
        encodeItems SighashAllWire.inputCodec tx.inputs ++
        WireOutputs.encode tx.outputs ++
        (WireIntegers.fixedLECodec 4).encode tx.locktime)
    simpa [LegacyTxWire.encode, List.append_assoc] using h
  have hCount := WireIntegers.compactSizeCodec.roundtrip
    tx.inputs.length wellFormed.2.1
    (encodeItems SighashAllWire.inputCodec tx.inputs ++
      WireOutputs.encode tx.outputs ++
      (WireIntegers.fixedLECodec 4).encode tx.locktime)
  have positive : tx.inputs.length ≠ 0 := by
    intro lengthZero
    exact nonempty (List.length_eq_zero_iff.mp lengthZero)
  simp only [List.append_assoc] at hCount
  simp [decode, hVersion, hCount, positive,
    LegacyTxWire.decode_encode tx wellFormed]
  exact nonempty

/-- The marker's empty initial vector selects the SegWit branch, after which
the actual input vector must be nonempty for a consensus-valid spend. -/
theorem decode_segwit_encode (tx : SighashAllWire.TxFields)
    (witnesses : List (List Bytes))
    (wellFormed : SegwitTxWire.valid tx witnesses)
    (nonempty : tx.inputs ≠ []) :
    decode (SegwitTxWire.encode tx witnesses) =
      some (.segwit tx witnesses, []) := by
  have hVersion : (WireIntegers.fixedLECodec 4).decode
      (SegwitTxWire.encode tx witnesses) =
      some (tx.version,
        [0x00, 0x01] ++
        WireIntegers.compactSizeCodec.encode tx.inputs.length ++
        encodeItems SighashAllWire.inputCodec tx.inputs ++
        WireOutputs.encode tx.outputs ++
        encodeItems SegwitTxWire.witnessStackCodec witnesses ++
        (WireIntegers.fixedLECodec 4).encode tx.locktime) := by
    have h := (WireIntegers.fixedLECodec 4).roundtrip
      tx.version wellFormed.1.1
      ([0x00, 0x01] ++
        WireIntegers.compactSizeCodec.encode tx.inputs.length ++
        encodeItems SighashAllWire.inputCodec tx.inputs ++
        WireOutputs.encode tx.outputs ++
        encodeItems SegwitTxWire.witnessStackCodec witnesses ++
        (WireIntegers.fixedLECodec 4).encode tx.locktime)
    simpa [SegwitTxWire.encode, List.append_assoc] using h
  simp [decode, hVersion, WireIntegers.compactSizeCodec,
    WireIntegers.compactSizeDecode, nonempty,
    SegwitTxWire.decode_encode tx witnesses wellFormed]

theorem decodeStrict_legacy_encode (tx : SighashAllWire.TxFields)
    (wellFormed : SighashAllWire.valid tx)
    (nonempty : tx.inputs ≠ []) :
    decodeStrict (LegacyTxWire.encode tx) = some (.legacy tx) := by
  simp [decodeStrict, decode_legacy_encode tx wellFormed nonempty]

theorem decodeStrict_segwit_encode (tx : SighashAllWire.TxFields)
    (witnesses : List (List Bytes))
    (wellFormed : SegwitTxWire.valid tx witnesses)
    (nonempty : tx.inputs ≠ []) :
    decodeStrict (SegwitTxWire.encode tx witnesses) =
      some (.segwit tx witnesses) := by
  simp [decodeStrict, decode_segwit_encode tx witnesses wellFormed nonempty]

/-- Any successful format-dispatch parse still re-encodes to exactly the
consumed bytes, including the witness portion when present. -/
theorem decode_sound (raw : Bytes) (envelope : Envelope) (tail : Bytes)
    (parsed : decode raw = some (envelope, tail)) :
    raw = encode envelope ++ tail := by
  cases versionEq : (WireIntegers.fixedLECodec 4).decode raw with
  | none => simp [decode, versionEq] at parsed
  | some versionPair =>
    rcases versionPair with ⟨version, afterVersion⟩
    cases countEq : WireIntegers.compactSizeCodec.decode afterVersion with
    | none => simp [decode, versionEq, countEq] at parsed
    | some countPair =>
      rcases countPair with ⟨count, afterCount⟩
      by_cases zero : count = 0
      · cases segwitEq : SegwitTxWire.decode raw with
        | none => simp [decode, versionEq, countEq, zero, segwitEq] at parsed
        | some segwitResult =>
          rcases segwitResult with ⟨tx, witnesses, after⟩
          by_cases empty : tx.inputs.isEmpty = true
          · simp [decode, versionEq, countEq, zero, segwitEq] at parsed
            have emptyInputs : tx.inputs = [] := by simpa using empty
            exact (parsed.1 emptyInputs).elim
          · have result : (Envelope.segwit tx witnesses, after) =
                (envelope, tail) := by
              have parts : ¬tx.inputs = [] ∧
                  Envelope.segwit tx witnesses = envelope ∧
                  after = tail := by
                simpa [decode, versionEq, countEq, zero,
                  segwitEq] using parsed
              exact Prod.ext parts.2.1 parts.2.2
            have hEnvelope : Envelope.segwit tx witnesses = envelope := by
              simpa using congrArg Prod.fst result
            have hTail : after = tail := by
              simpa using congrArg Prod.snd result
            rw [← hEnvelope, ← hTail]
            exact SegwitTxWire.decode_sound raw tx witnesses after segwitEq
      · cases legacyEq : LegacyTxWire.decode raw with
        | none => simp [decode, versionEq, countEq, zero, legacyEq] at parsed
        | some legacyResult =>
          rcases legacyResult with ⟨tx, after⟩
          by_cases empty : tx.inputs.isEmpty = true
          · simp [decode, versionEq, countEq, zero, legacyEq] at parsed
            have emptyInputs : tx.inputs = [] := by simpa using empty
            exact (parsed.1 emptyInputs).elim
          · have parts : ¬tx.inputs = [] ∧
                Envelope.legacy tx = envelope ∧ after = tail := by
              simpa [decode, versionEq, countEq, zero,
                legacyEq] using parsed
            rw [← parts.2.1, ← parts.2.2]
            exact LegacyTxWire.decode_sound raw tx after legacyEq

theorem decode_nonempty_inputs (raw : Bytes) (envelope : Envelope)
    (tail : Bytes) (parsed : decode raw = some (envelope, tail)) :
    (fields envelope).inputs ≠ [] := by
  cases versionEq : (WireIntegers.fixedLECodec 4).decode raw with
  | none => simp [decode, versionEq] at parsed
  | some versionPair =>
    rcases versionPair with ⟨version, afterVersion⟩
    cases countEq : WireIntegers.compactSizeCodec.decode afterVersion with
    | none => simp [decode, versionEq, countEq] at parsed
    | some countPair =>
      rcases countPair with ⟨count, afterCount⟩
      by_cases zero : count = 0
      · cases segwitEq : SegwitTxWire.decode raw with
        | none => simp [decode, versionEq, countEq, zero, segwitEq] at parsed
        | some segwitResult =>
          rcases segwitResult with ⟨tx, witnesses, after⟩
          have parts : ¬tx.inputs = [] ∧
              Envelope.segwit tx witnesses = envelope ∧ after = tail := by
            simpa [decode, versionEq, countEq, zero,
              segwitEq] using parsed
          rw [← parts.2.1]
          exact parts.1
      · cases legacyEq : LegacyTxWire.decode raw with
        | none => simp [decode, versionEq, countEq, zero, legacyEq] at parsed
        | some legacyResult =>
          rcases legacyResult with ⟨tx, after⟩
          have parts : ¬tx.inputs = [] ∧
              Envelope.legacy tx = envelope ∧ after = tail := by
            simpa [decode, versionEq, countEq, zero,
              legacyEq] using parsed
          rw [← parts.2.1]
          exact parts.1

theorem decodeStrict_sound (raw : Bytes) (envelope : Envelope)
    (parsed : decodeStrict raw = some envelope) :
    raw = encode envelope := by
  cases decoded : decode raw with
  | none => simp [decodeStrict, decoded] at parsed
  | some result =>
    rcases result with ⟨actual, tail⟩
    cases tail with
    | nil =>
        have same : actual = envelope := by
          simpa [decodeStrict, decoded] using parsed
        rw [← same]
        simpa using decode_sound raw actual [] decoded
    | cons head rest => simp [decodeStrict, decoded] at parsed

theorem decodeStrict_nonempty_inputs (raw : Bytes) (envelope : Envelope)
    (parsed : decodeStrict raw = some envelope) :
    (fields envelope).inputs ≠ [] := by
  cases decoded : decode raw with
  | none => simp [decodeStrict, decoded] at parsed
  | some result =>
    rcases result with ⟨actual, tail⟩
    cases tail with
    | nil =>
        have same : actual = envelope := by
          simpa [decodeStrict, decoded] using parsed
        rw [← same]
        exact decode_nonempty_inputs raw actual [] decoded
    | cons head rest => simp [decodeStrict, decoded] at parsed

/-- The raw-byte source-model checker first dispatches a complete transaction
envelope, then supplies only its common fields to the legacy sighash branch.
Witness data remains outside the legacy preimage. -/
def legacyDigestOfRaw (functions : JointSourceChecks.Functions)
    (raw : Bytes) (selected : Nat) (scriptCode : Bytes)
    (hashType : UInt8) : Option Bytes := do
  let envelope ← decodeStrict raw
  JointSourceChecks.legacyDigest functions (fields envelope)
    selected scriptCode hashType.toNat

/-- Every successful modeled raw-byte digest has one recovered canonical
envelope and is either `H(H(preimage))` or Core's out-of-range SINGLE constant.
The hypotheses here are source-parser success, not compiled Core acceptance. -/
theorem legacyDigestOfRaw_some_cases
    (functions : JointSourceChecks.Functions)
    (raw : Bytes) (selected : Nat) (scriptCode : Bytes)
    (hashType : UInt8) (digest : Bytes)
    (found : legacyDigestOfRaw functions raw selected scriptCode hashType =
      some digest) :
    ∃ envelope,
      raw = encode envelope ∧
      (fields envelope).inputs ≠ [] ∧
      selected < (fields envelope).inputs.length ∧
      ((∃ preimage,
          LegacySighashWire.sourcePreimage (fields envelope) selected
            scriptCode hashType.toNat = some preimage ∧
          digest = functions.H (functions.H preimage)) ∨
        (LegacySighashWire.sourcePreimage (fields envelope) selected
            scriptCode hashType.toNat = none ∧
          LegacySighashWire.baseType hashType.toNat = 3 ∧
          (fields envelope).outputs.length ≤ selected ∧
          digest = LegacySighashWire.singleBugDigest)) := by
  unfold legacyDigestOfRaw at found
  cases parsed : decodeStrict raw with
  | none => simp [parsed] at found
  | some envelope =>
    have digestFound : JointSourceChecks.legacyDigest functions
        (fields envelope) selected scriptCode hashType.toNat = some digest := by
      simpa [parsed] using found
    obtain ⟨inputValid, preimageCase⟩ :=
      JointSourceChecks.legacyDigest_some_cases functions (fields envelope)
        selected scriptCode hashType.toNat digest digestFound
    exact ⟨envelope, decodeStrict_sound raw envelope parsed,
      decodeStrict_nonempty_inputs raw envelope parsed,
      inputValid, preimageCase⟩

end QSB.TransactionEnvelopeWire
