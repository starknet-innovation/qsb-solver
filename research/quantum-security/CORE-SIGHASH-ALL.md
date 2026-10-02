# Legacy `SIGHASH_ALL` semantic commitment boundary (Core 27.2)

The fixed pinning and final nonce signatures in the disposable Config A lock
end in `0x01`. That requests legacy `SIGHASH_ALL` for their reached checks.
This note identifies what this fact supplies, and the remaining gap to an
unauthorized-spend probability bound.

## Source contract

For a base-script signature, [Core's legacy serializer](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1242-L1339)
serializes the transaction version, all input prevouts and sequences, all
outputs in order, and locktime when the hash type is exactly `0x01`.
It substitutes the selected `scriptCode` for the signed input's `scriptSig`
and an empty script for every other input. The hash type is appended before
hashing in [`SignatureHash`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1616-L1632).
Each [output serialization](https://github.com/bitcoin/bitcoin/blob/v27.2/src/primitives/transaction.h#L1308-L1329)
contains its value and scriptPubKey. This is a statement about the bytes
Core hashes, not about whether one fixed ECDSA key can verify only one hash.
Core's [`WriteCompactSize`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/serialize.h#L309-L344)
uses one, three, five, or nine bytes, and its integer writers use little-endian
16-, 32-, and 64-bit words. Core's decoder additionally rejects noncanonical
encodings and oversized vectors; the Lean decoder below is a left inverse for
canonical encoded values and is not claimed equivalent on arbitrary bytes.

The app's pinned `Transaction.sighash` implements the corresponding byte
layout for `SIGHASH_ALL`. `QSB/SighashBinding.lean` proves that, **for fixed
non-output bytes**, injective encoding of ordered outputs makes changed
outputs produce distinct preimages. `QSB/OutputCodec.lean` proves that output
count, value, length-prefixed script, and list encodings compose injectively.
`QSB/WireIntegers.lean` supplies concrete little-endian amount and all four
CompactSize encoder branches with valid-domain round trips;
`QSB/WireOutputs.lean` therefore proves ordered-output byte injectivity when
the amount is nonnegative and below `2^63` and count/script lengths are below
`2^64`. Equality with Core's C++ byte writers and the consensus monetary
domain still needs refinement. `QSB/SighashAllWire.lean` then parses the
ordered outputs from a complete source-shaped ALL preimage with variable
version, prepared input scripts, input count, and locktime. The parser round
trip is proved on its valid wire domain; a generated 139-byte fixture in
`QSB/SighashAllWireFixture.lean` equals the pinned app's baseline preimage.
The newer full parser also recovers version, every prepared input, outputs,
locktime, and the appended ALL word. On valid fields it is a left inverse of
the complete encoder. Source-shaped input preparation preserves each ordered
prevout and sequence while replacing the scripts. Therefore equal prepared
preimages force equality of all these committed fields even if the original
scriptSigs, selected input index, or reached scriptCode differ. A fixed
ledger-resolution function then maps equal ordered outpoints to equal
previous outputs, giving equal `Game.Projection` and fee in that same ledger
context. This ledger function is an explicit model parameter, not a proof of
Bitcoin chain-state resolution.
The model now also blanks original input scripts and substitutes a supplied
`scriptCode` for the signed input before encoding. Its output parser still
round-trips with arbitrary original scriptSigs and selected scriptCode in the
wire domain. A generated fixture checks that this preparation yields the
same pinned 139-byte preimage from different original scriptSig bytes.
`QSB/ScriptSigSighash.lean` proves this erasure for arbitrary source-shaped
transactions at **fixed** selected input and scriptCode. It also proves that
different supplied scriptCodes give different preimages on the valid domain.
Two complete candidate final-signature lists delete different pushes from the
literal generated lock, so fixed transaction fields do not by themselves fix
the final ALL preimage. Those lists are not established as accepted QSB
witnesses; unequal preimages do not rule out a SHA256d collision.
`QSB/FinalSubsetInjective.lean` generalizes this to all lists of the 150
generated final dummy positions in the literal lock: equal source-shaped final
scriptCodes, and therefore equal valid fixed-transaction ALL preimages, occur
exactly for equal selected position sets. Permuting or repeating selected
positions does not change that set. The theorem does not show which sets an
accepted Core execution can reach or assign a quantum-query probability.
`QSB/ReachedSubsetSighash.lean` applies this exact equality classification to
two reached modeled final stacks. Successful full byte-model execution plus
explicit nonempty, DER-sound successful scans supplies nine distinct selected
positions per stack; source-shaped FindAndDelete then removes the ten reached
signature pushes. The theorem does not identify compiled-Core preimages or
establish SHA256d collision resistance.
Its checked-run corollary uses two truthy full `CoreCheckedStep.run` results
and derives each final scan from that interpreter, while retaining the
external key/ECDSA checker and compiled-Core refinement obligations.
The literal validated-wire corollary also checks supplied script bytes before
decoding; it remains a source-model run, not a consensus acceptance theorem.
An additional [full-lock differential](evidence/full-subset-switch-core.json)
checks two such sets against the pinned Core 27.2 adapter. In one synthetic,
unfunded two-input/two-output transaction, with QSB at input 1, replacing
final dummy position 8 with 9 changes the shared final scriptCode and its
in-range ALL digest. The puzzle-relaxed 880-opcode lock accepts each subset
with freshly recovered keys and rejects the second subset when it retains
the first subset's final nonce key. Pinning, HORS comparisons, and both
multisignature checks execute; the three hash-to-signature puzzle
CHECKSIGVERIFY sites are replaced by OP_2DROP. This is finite evidence for
the witness-dependent scriptCode boundary, not acceptance by the real lock
or a same-key rejection theorem. Reproduce it with
`analysis/check_full_subset_switch_core.py` and the pinned app/native paths
recorded in that script and report.
The remaining step is to identify Core's C++ preimage for every accepted
transaction with this source-shaped encoding, including its reached
FindAndDelete `scriptCode`. The Lean theorems combine same-key verification with the
finite-recovery-point theorem: the new hash group element must land in the
key's admissible message-target set. The wire and Core-to-Lean ECDSA/hash
premises remain explicit. Neither theorem collapses this event to a collision
with the released digest.
`QSB/RecoveryCandidates.lean` now bounds the raw 256-bit digest target set by
eight under its stated recovery-point and Core conversion premises: at most
four message residues, each with at most two representatives modulo the
secp256k1 order. This is a count of possible values, not a probability bound
for SHA256d under quantum queries.
`QSB/SighashBinding.lean` composes that finite target set with the prepared
source-shaped ALL preimage: changed outputs force a distinct preimage, while
an explicitly admitted same-key verification and digest reduction place the
attempted digest in the set. Core acceptance and the joint-oracle target-hit
probability remain unproved.
The stronger `source_all_forbidden_projection_wire_digest_target` theorem
uses an owner-authorized set of exact semantic projections. An attempted
projection outside that set has a distinct preimage from any approved release
under the same ledger function, including cases where outputs stay the same
but an input, sequence, version, or locktime changes. The same explicit
verification premises put its digest in the at-most-eight-value set; no
uniformity or quantum query bound follows from that cardinality alone.

For arbitrary accepted QSB witnesses, scriptCode may vary with the selected
final dummy signatures, and other transaction fields may vary too. The
arbitrary-context theorem assumes, but does not prove, that the output
projection can be recovered from *any actual Core* legacy ALL preimage in the
relevant domain. The source-shaped parser proves the corresponding fact for
its own serializer. It does not prove that every Core-accepted witness reaches
the modeled ALL check with the modeled key.

## Pinned native probe

`analysis/check_all_sighash_commitments.py` uses one synthetic two-input,
two-output transaction and an isolated bare `CHECKSIG` lock with one fixed
DER signature ending in `0x01`. It independently constructs the app's ALL
preimage from field serializers, checks its SHA256d against `Transaction.sighash`,
publicly recovers the corresponding key, and asks the pinned Core 27.2 adapter
to verify. The [evidence](evidence/all-sighash-commitments.json) records the
preimage, digest, key, transaction bytes, and Core result for every case.

Ten changes (output amount, output script, output order, output count,
253-byte output script, 253 outputs, signed-input prevout, another input's
sequence, version, and locktime) gave distinct preimages and digests in this
fixture. Core rejected the baseline key in all ten cases and accepted each
freshly recovered key.
Two `scriptSig`-only changes gave the same preimage and digest; Core accepted
the baseline key. These are 13 finite cases, with all 13 fresh-key controls
accepted. They do not establish a universal rejection theorem for the old
key: distinct digests can still be ECDSA-valid for one key through different
recovery points, and a digest collision is also possible. The isolated lock
does not execute either QSB puzzle or its final multisignature.

`analysis/check_wire_vectors.py` compares the pinned app's field serialization
against the Lean-checked CompactSize boundary examples at 252, 253, 65,535,
65,536, and `2^32`, plus the eight-byte value 90,000. The exact finite results
are in [wire-vectors.json](evidence/wire-vectors.json). The two 253-boundary
transaction cases above additionally passed the pinned Core adapter.

## Core's published sighash vectors

`analysis/check_core_sighash_vectors.py` parses the pinned [Core 27.2 sighash
vectors](https://github.com/bitcoin/bitcoin/blob/v27.2/src/test/data/sighash.json)
independently, constructs the complete legacy preimage, and compares its
SHA256d to Core's expected digest. It also reconstructs each transaction with
the pinned app serializer and compares that serializer's sighash. Core's
[test harness](https://github.com/bitcoin/bitcoin/blob/v27.2/src/test/sighash_tests.cpp)
generates 500 random cases and checks the new implementation against the old
one before printing the vectors; its data test compares the published digest
against `SignatureHash` in base sigversion.

The [differential report](evidence/core-sighash-vectors.json) now checks all
500 vectors: 467 ALL-like, 16 NONE, and 17 in-range SINGLE cases, including
229 with ANYONECANPAY. All Core expected digests match independently built
source-shaped preimages and the pinned app serializer. Of the scripts, 210
contain an opcode-boundary `OP_CODESEPARATOR`. In this corpus the
`scriptCode` generator emits only one-byte opcodes, so removing `0xab` is
unambiguously opcode removal. No published vector uses the literal hash type
`0x01`; its separate 13-case native fixture above exercises that exact value.
The corpus also has no out-of-range SINGLE case. The separate native
`core-semantics.json` probe exercises that constant-message exception.

`QSB/LegacySighashWire.lean` models the source-shaped serializer for all
32-bit hash types, including the NONE/SINGLE output branches, zeroed other
sequences, ANYONECANPAY's selected-input reduction, and the out-of-range
SINGLE exception. It proves that type `0x01` reduces to the earlier ALL
preimage and that the out-of-range SINGLE preimage is absent. Five exact
preimage fixtures generated from the independent serializer are checked in
Lean, alongside the exception's raw `uint256::ONE` bytes. This does not prove
that Core's C++ implementation refines the Lean function for arbitrary
transactions, that arbitrary reached `scriptCode` is correct, or that the
exception yields a QSB spend.
The report pins the upstream JSON SHA-256 and the app source hash. Reproduce it
from the repository root after downloading the linked JSON:

```sh
python3 research/quantum-security/analysis/check_core_sighash_vectors.py \
  --vectors /path/to/bitcoin-core-v27.2-sighash.json \
  --app-root /Users/adrienlacombe/ws/qsb-app \
  --output research/quantum-security/evidence/core-sighash-vectors.json
```

These are finite checks of the serializer branches. They do not refine arbitrary
Core transactions or prove that an accepted QSB witness reaches the modeled
final nonce check with the selected `scriptCode`.

Run the probe with the pinned app, native adapter, and image recorded in the
evidence file:

```sh
python3 analysis/check_all_sighash_commitments.py \
  --app-root /Users/adrienlacombe/ws/qsb-app \
  --native-root /tmp/qsb-core-27.2-qrom \
  --image sha256:06da5a3362eda00c5114227ac81abe56dd9b943395553b7c64a310457f4d9e2b \
  --output evidence/all-sighash-commitments.json
```

The `/tmp` native directory is a disposable local build; the evidence records
its executable and library hashes so a replacement build can be compared.
