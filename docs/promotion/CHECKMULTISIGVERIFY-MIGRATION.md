# Corrected Config A script migration (HOLD)

Upstream [PR 7](https://github.com/avihu28/Quantum-Safe-Bitcoin-Transactions/pull/7),
merged at `b22f81c093488d09b9cd59c171c79b6c40812cf1`, requires the first
round's signature check to succeed with CHECKMULTISIGVERIFY. The final round
retains CHECKMULTISIG. Changed stack geometry also changes subsequent script
bytes. The old script's parameters and results must not be reused for the new
script. Existing on-chain outputs retain their old script.

## Separate script and search contracts

`ranked-v2` is unchanged: no rank partition or coverage accounting changed.
`scriptVersion` identifies the script format independently:

- `qsb-config-a-legacy-v1`: historical requests can omit the field; an explicit
  corrected field is rejected by the historical handler.
- `qsb-config-a-cmsverify-v1`: corrected combined builds require this exact field
  before creating a subprocess and echo it in all returned compute outcomes.
  Missing, unknown and legacy values fail closed.

Build a corrected **candidate**, using the existing combined build instructions,
with `--build-arg SCRIPT_VERSION=qsb-config-a-cmsverify-v1`. The generated
pipeline uses `qsb-combined-candidate-v2`, binds the actual wrapper and binaries,
and remains HOLD. The default remains the historical contract; no historical
image or descriptor is edited. The publishing workflow selects corrected mode
only for explicitly created `candidate-sm86-cmsverify-*` tags. This change does
not create such a tag or publish an image. CI builds both modes and runs their
no-GPU identity/failure checks.

`combined_descriptor.py` emits schema 4 with the corrected `generatorCommit` and
`scriptVersion` only from this v2 pipeline. Schema 3 and old descriptors retain
their original meaning. The app must understand schema 4, reconstruct the actual
script, derive fresh parameters and independently verify results before any
release enrollment. A caller-supplied version and echoed worker identity are
consistency checks, not proof of script validity or provider attestation.
The standalone optimized adapter still rejects the new field; it has not been
silently upgraded or qualified as a complete pipeline.

## Parameter-path audit and retained public fixtures

The pinning loader (`vendor/challenge/candidates/pinning/pinning.cu`,
`load_pinning2`) receives an explicit SHA midstate, suffix bytes, total preimage
length and sequence/locktime offsets. It does not generate script opcodes.
The optimized subset loader (`research/optimized-subset/subset/tests/gpu_epochs/tree.cu`,
`load_digest_params`) receives dummy pushes, prefix remainder, tail and transaction
suffix lengths. Its generic cache preparation uses these actual bytes and their
alignment. Specialized paths with fixed geometry stay disabled by the existing
build flags. No CUDA source or flags are changed by this migration. This source
assessment is not native compatibility evidence.

`tests/fixtures/cmsverify-v1` contains seed-719 public commitments/signatures and
exports for synthetic nonexistent outpoints `11…11` and `22…22`; no wallet,
funded output or recovery data is present. `provenance.json` binds exact exporter
source hashes and every fixture file. Reproduce with a corrected qsb-app checkout:

```sh
python3 scripts/generate_corrected_fixtures.py /path/to/qsb-app /new/fixture-directory
python3 -m unittest discover -s tests -v
```

The 12 vectors derive expected scriptCode hashes and sighashes using the app's
full transaction + FindAndDelete reference, separately from exporter-layout
reconstruction. Local tests check parsed CHECKMULTISIGVERIFY/CHECKMULTISIG
opcodes, both binary layouts, pinning offsets and all 12 reconstructed sighashes
(first/last/scattered subsets, minimum/maximum supported sequence and locktime).
These tests do not execute CUDA or prove that a candidate satisfies real puzzles.
Fixture reproduction runs the local reviewed app reference, not upstream setup
scripts. Seed-derived public fixtures must never be used for real deposits.

## Current bounded evidence

The [16 October A10G gate](2026-10-16-corrected-a10g.md) executed the freshly
built corrected candidate: 128 subset CPU/GPU hashes, 16 exact-binary subset
ranges, two pinning boundary smokes and three alternating performance samples
per subset round passed. No real hit or fresh withdrawal was produced. This
narrows, but does not close, the qualification list below.

## Remaining qualification, before enrollment

1. Build the corrected mode on native Linux/sm86 and preserve exact source,
   compiler, binary, OCI digest and provenance identities.
2. Use these corrected exports with existing trace/differential tooling and the
   separate corrected app CPU reference. Exercise pinning and both subset rounds,
   first/final rank boundaries, SHA block alignments, real hits, exceptional
   recovery and capacity/error paths. Compare full-transaction hashes, not just
   empty range reports. Extend fixtures to supported output layouts as needed.
3. Run matched repeated A10G performance against the baseline for each stage.
   Historical benchmark receipts do not attest this build or this script format.
4. Obtain independent review and a fresh corrected full-predicate offline Core
   withdrawal proof. The prior release's historical waiver is not evidence for
   this changed locking script. External miner inclusion is a separate gate.
5. Publish an attested release and explicitly enroll its exact schema-4 descriptor
   in qsb-app only after approval. No fabricated digest or automatic enrollment.

The original migration preparation performed no GPU work. Subsequent bounded
native evidence is linked above; no app deployment, funded fixture or broadcast
is part of that gate. Until the remaining gates pass the corrected
candidate remains HOLD, and the app must not dispatch new corrected vaults to a
legacy enrolled image.
