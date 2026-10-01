# Legacy `SIGHASH_ALL` output commitment boundary (Core 27.2)

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
domain still needs refinement. A second conditional theorem handles varying
other fields and scriptCode if an output parser round-trips all relevant ALL
preimages. Both versions combine same-key verification with the
finite-recovery-point theorem: the new hash group element must land in the
key's admissible message-target set. The wire and Core-to-Lean ECDSA/hash
premises remain explicit. Neither theorem collapses this event to a collision
with the released digest.

For arbitrary accepted QSB witnesses, scriptCode may vary with the selected
final dummy signatures, and other transaction fields may vary too. The
arbitrary-context theorem assumes, but does not prove, that the output
projection can be recovered from *any* legacy ALL preimage in the relevant
domain. It also does not prove that every Core-accepted witness reaches the
modeled ALL check with the modeled key.

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
