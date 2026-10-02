import QSB.TransactionEnvelopeWire

/-!
The source transaction parser checks canonical wire framing, not all of
Core's `CheckTransaction` conditions. In particular, it admits two inputs
with the same prevout. This is an explicit counterexample to replacing the
external consensus-validity premise with successful source parsing.
-/
namespace QSB.ConsensusValidityBoundary

open QSB.SighashAllWire

def noDuplicatePrevouts (tx : TxFields) : Prop :=
  (tx.inputs.map fun input => (input.1, input.2.1)).Nodup

private def repeatedInput : InputFields :=
  (List.replicate 32 (0x11 : UInt8), (0, ([], 0xFFFFFFFE)))

def duplicateTx : TxFields :=
  { version := 2
    inputs := [repeatedInput, repeatedInput]
    outputs := [{ value := 1000, script := [0x51] }]
    locktime := 0 }

theorem duplicateTx_valid_wire : valid duplicateTx := by
  norm_num [valid, duplicateTx, repeatedInput, inputCodec,
    OutputCodec.productCodec, OutputCodec.fixedBytesCodec,
    WireIntegers.fixedLECodec, OutputCodec.lengthPrefixedBytesCodec,
    WireOutputs.validOutputs, WireIntegers.compactSizeCodec,
    WireIntegers.nonnegativeAmountCodec]

theorem duplicateTx_rejected_duplicate_check :
    ¬ noDuplicatePrevouts duplicateTx := by
  simp [noDuplicatePrevouts, duplicateTx]

theorem duplicateTx_parses :
    TransactionEnvelopeWire.decodeStrict (LegacyTxWire.encode duplicateTx) =
      some (.legacy duplicateTx) := by
  exact TransactionEnvelopeWire.decodeStrict_legacy_encode duplicateTx
    duplicateTx_valid_wire (by decide)

theorem wire_parse_does_not_imply_no_duplicate_prevouts :
    ¬ (∀ tx : TxFields,
      TransactionEnvelopeWire.decodeStrict (LegacyTxWire.encode tx) =
        some (.legacy tx) → noDuplicatePrevouts tx) := by
  intro all
  exact duplicateTx_rejected_duplicate_check
    (all duplicateTx duplicateTx_parses)

end QSB.ConsensusValidityBoundary
