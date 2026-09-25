# Exact-build replay and matched benchmark

Status: **HOLD — measured improvement, not yet a promoted default release**.

The unchanged `candidate-20260925-1` image and subset binary were tested against the
published v0.1.0 baseline on one secure RTX 4090 (driver 580.159.04). The harness
was committed and pushed as `ace6c49d4244bf8e9fc0a7b88dae226a4063e2a5` before
allocation, and downloaded source files were checked against their hashes.
Both solver executables were SHA256-checked before any run. The baseline executable
was extracted from its immutable published OCI image; its validation-only release
asset does not change the normal release.

## Results

Each cell uses three alternating baseline/candidate runs of 2,147,483,648 ranks,
starting at rank zero. Times are medians of monotonic wall time, including process
startup. Both executables used identical parameters, GPU, CLI geometry and predicate.

| Output layout / stage | Baseline seconds | Candidate seconds | Throughput gain | Wall-time reduction |
|---|---:|---:|---:|---:|
| SegWit / round 1 | 32.421 | 17.943 | 80.68% | 44.65% |
| Taproot / round 1 | 31.988 | 18.204 | 75.72% | 43.09% |
| SegWit / round 2 | 11.503 | 11.103 | 3.61% | 3.48% |
| Taproot / round 2 | 11.569 | 11.190 | 3.39% | 3.28% |

All 24 benchmark processes completed successfully, with no returned hits. The
separate qsb-app CPU exporter reproduced all four fixture parameter blobs; the
reference commit and actual Python file hashes are recorded in the
[machine-readable receipt](2026-09-25-benchmark.json). Synthetic benchmark inputs
use nonexistent 00/11 outpoints. This checks parameter binding, not exhaustive GPU
coverage. These are small-sample observations on one GPU, with no confidence
interval, hardware-generalization or whole-withdrawal price claim.

Two additional one-candidate historical replays returned the expected subset
indices, recovery IDs and hash choices using the exact candidate executable.
The legacy diagnostic `combo_idx` field is not part of that semantic comparison.
These are known-solution replays, not new discoveries, independent CPU verification
of new hits, fresh searches or withdrawals. No transaction was signed or broadcast.

The receipt validator rejects incomplete/duplicate samples, wrong identities or
ranges, and unexpected benchmark hits that would require independent verification.
18 local tests pass, including receipt completeness and failure-path checks.

## Corrections and cleanup

The first allocation found the expected round-one hit, but the harness rejected
its `Done enum:` completion text because it expected `Done:`. The pod was deleted;
the harness was corrected and pushed before a new allocation. The solver binary
was not changed. The full corrected batch completed on a single GPU and single pod.

The announced rate was $0.74/hour plus storage. Each allocation had its own
29-minute deletion watchdog. Both test pods were deleted, a fresh provider list
confirmed zero remaining pods, and both watchdogs were terminated after cleanup.
Neither historical proof endpoint was started. This bounded test incurred no
production rollout or new long-running search.

## Still needed for promotion

- Broader native differential/adversarial and boundary/exception coverage tied to
  this exact final build. Earlier binary evidence is not automatically transferable.
- Independent final source/integration review, including unchanged historical
  pinning limitations.
- A fresh full-predicate end-to-end withdrawal proof using the final image, then
  explicit normal-release publication and app enrollment. Historical replays and
  this benchmark do not satisfy that proof.

The candidate's unchanged identities and the full samples are in the receipt.
The normal `v*` release path still builds the historical baseline. No application
release descriptor or mainnet activation was issued by this work.
