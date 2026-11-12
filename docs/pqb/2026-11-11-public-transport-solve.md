# Complete public PQB solve through the consumer transport

**All three stages solved and independently verified. Candidate remains HOLD.**
One public synthetic intent completed in **91 minutes 40 seconds**, from
2026-11-11 20:52:57.075 to 22:24:36.799 UTC. Estimated compute was **$20.73**, including
the separate image builder. All temporary AWS resources were independently verified removed.
The [evidence manifest](evidence/public-transport-2026-11-11/manifest.json),
[final audit](evidence/public-transport-2026-11-11/final-audit.json) and
[cleanup receipt](evidence/public-transport-2026-11-11/reconciliation-final.json) bind the result.

## What ran

The development controller imported the pinned consumer's actual `AwsBatch`, `workerInput`,
`checkedOutput`, `pqbReference`, `applyVerifiedHit`, range and GPU-reservation helpers. It used
real AWS Batch submissions, S3 request/result objects and the consumer's independent CPU
verifier. Controller checkpoints were durably saved locally. No provider or CPU verdict was
mocked in this campaign. The manifest and public state came from the consumer's committed
synthetic reference; cloud requests and the controller input contained public data only.

This exercised development orchestration through the real consumer transport. The served
Step Functions coordinator, wallet authorization, witness/signature construction, Bitcoin Core
consensus, miner acceptance and transaction broadcast remain outside this assessment.
The development descriptor was explicitly `public-validation-only`, rather than an enrolled release.

| Consumer stage | Worker stage | Submissions | Completed units | Cancelled terminal | Emitted hits | Full hits |
|---|---|---:|---:|---:|---:|---:|
| pinning | pinning | 34 | 33 | 1 | 3 | 1 |
| round1 | round0 | 60 | 46 | 14 | 9 | 1 |
| round2 | round1 | 49 | 39 | 10 | 4 | 1 |
| Total | | **143** | **118** | **25** | **16** | **3** |

Every completed unit returned its exact range-complete report. All 16 emitted hits were
re-derived by the consumer and by the pinned upstream Python implementation using native
`coincurve==21.0.0`/libsecp256k1. The three selected hits were checked again against the
original public intent at completion. The upstream checker also compared complete problem
bytes and checked eight canonical sighash samples for each problem. See the
[three-hit result](evidence/public-transport-2026-11-11/upstream-accepted-3-native-result.json)
and the per-stage `upstream-native-final-*.json` receipts.

The 25 terminal failures were deliberate coordinator cancellations after a stage was solved;
one was cancelled before starting. There were 39 controller cancellation intents: 14 concerned
work that still completed or had already completed when the provider cancellation helper ran.
Such units received credit only after their complete output passed verification. Cancelled or
incomplete work received no range credit. No uncertain submission or unexpected worker failure
occurred, and no paid request was replayed. No round was exhausted, so native re-pinning was
not exercised.

## Exact source and artifact identities

| Object | Identity |
|---|---|
| GPU image source | `4bfd8f1f7011331979f33b60bb8c6e379227ca16` |
| Active solve controller | `04d6039a85f9fde145ea5540c874a4c27b5e9417` |
| Executed controller bundle SHA-256 | `87ad3e3a9303c77f48ed1cc6c567cab633a8b6bb90fcb1cec097f4d8c7ede3c1` |
| Consumer | qsb-app `276f2ae09d50ca44d46b035e45b6d0365802edcf` |
| Consumer tree, also at original `81c060d` | `37e3b41d7142001d2cdf676f1101489e9d6e50f4` |
| Imported upstream/checker | `eccdd09772edf14ab37fc63992b0626ad7ff2221` |
| Private OCI index digest | `sha256:4212bcf06999da2b8084247c17d3fc0e2786e46cf356cb17e7ea971809e190c5` |
| Linux amd64 manifest | `sha256:8f942ed252394c25bad8f378ac547b90e2773e73fe1fd44a36eb6af8387a9de0` |
| OCI config digest (build export) | `sha256:65818adc4c174f004b3dc13e17d3a234049dafdfeeda267b491ed4c3ced7d957` |
| Ranked binary SHA-256 | `0e811c59de2d36f66142a6f65393c55a64e0e37c7eb40df4251f86b713ef3d82` |
| Image archive SHA-256 | `114ec543d414d2eb69875208f506ce395232082911916f6ca6a04ed133f8e229` |
| Public input file SHA-256 | `38f2cd198ac14cbf24483dd48fec3b27028e076475efdabdcb17e8dbc1347d4c` |
| Contract | `pqb-ranked-v2`, canonical hash `5217daa6415b83dcce2d85159130df4994ab0e9bb67910c7bdf00e5804f4ee71` |

The binary was compiled with nvcc 12.8.93, `-O3 -std=c++17 -arch=sm_86`. No experimental
CUDA options or reduced gates were enabled. All completed jobs' startup logs show NVIDIA A10G,
driver 580.178.04, zero Linux capabilities and `NoNewPrivs=1`. The 51 Batch instances used the
pinned ECS GPU AMI `ami-034c2d44a0a1d5e82`; at most 16 workers ran concurrently.
The consumer's actual hardened command required `/opt/qsb/aws_entrypoint.py`, so this image
adds `/opt/qsb` as an alias of `/opt/qsb-pqb`. Offline CI and native execution checked that path.

The native image was built from clean, pushed source after the original
[CI run](https://github.com/starknet-innovation/qsb-solver/actions/runs/43094872603)
passed compilation, offline checks and scanning but failed to create artifacts. The separate
native build retained its exact archive, Docker inspection, compiler/binding receipts and raw
registry manifest. Its Grype 0.119.0 scan, using the 2026-11-11 database, passed the repository
policy: zero fixable Critical matches and 20 unfixed Critical package matches. This is a
point-in-time package assessment. Apt updates and transitive package resolution remain mutable
build inputs; the retained archive and actual image identity bind this run. Later CI builds
have their own identities and do not inherit this native attestation.

The private registry was removed after collection. The 2,210,919,793-byte image archive and
original compiled controller bundles remain in the local campaign directory, outside Git.
The evidence manifest records their hashes. No public PQB release, GitHub release attestation,
release descriptor enrollment or application deployment was performed.

## Corrections and collection limits

- An initial interpretation incorrectly treated upstream's conditional hybrid-key exclusion as
  its default. The temporary consumer change `2eb4504` was fully reverted by `276f2ae`; its tree
  equals the original `81c060d` tree. The temporary controller observed only the empty preflight.
  Known requests and reservations were handed over without replay or a deadline change, and
  completed outputs were checked again. No solution was discarded. Upstream pins
  `HYBRID_KEYS_MINEABLE=True`; the accepted round1 hit uses encoding 2, consistent with that
  policy. Actual miner acceptance remains untested.
- Earlier supplemental Python receipts used upstream's pure-Python WASM curve shim under
  CPython 3.15.1. They remain identified separately. Final checks repeated all 118 completed
  units and 16 hits with native coincurve 21.0.0 under CPython 3.13.4/arm64. The native library,
  interpreter and source hashes are retained in the runtime receipts. Neither backend launches
  a Bitcoin Core consensus process.
- Batch scaled idle instances down during handoffs and between some units. Quota rejections
  during termination delayed replacement capacity. Managed scaling activities and all allocated
  instance lifetimes are retained; the solve wall time includes these delays.
- Cleanup initially tried an empty compute-environment association update. Read-back showed
  that the association remained. Commit `deacd2c` deletes the disabled, drained queue directly,
  as supported by [DeleteJobQueue](https://docs.aws.amazon.com/batch/latest/APIReference/API_DeleteJobQueue.html),
  then deletes the environment. Six cleanup tests passed and the corrected path completed.
  Original no-op receipts and fresh reconciliation are separate.
- The stock transport exposes original S3 envelopes and CloudWatch startup/result logs.
  Per-batch kernel logs and interrupted temporary work files are not forwarded. One cancelled
  job had an assigned log name but no created stream; its absent `startedAt` and stream absence
  were independently recorded. All 118 completed jobs have their terminal log summary.

The final local suite ran 163 tests: 162 passed and one Linux-only test was skipped on macOS.
The cleanup correction's six tests also passed. Clean source `deacd2c` passed
[CI run 43112042552](https://github.com/starknet-innovation/qsb-solver/actions/runs/43112042552).
The evidence package's 1,201 archived originals passed byte-hash checks; restoring the package
and re-running its final audit with the retained image reproduced every stable result field.

## Cost and cleanup

The fixed deadline was **2026-11-12 02:51:32 UTC**, with independent Scheduler/Lambda and
guest guards. It was never extended. Before paid work the campaign reserved $200 for the
solve and $2 for the separate bounded builder. All 143 submissions retained their original
900-second reservation, totalling **128,700 GPU-seconds** against the 540,000-second ceiling.
Reservations were closed only after independent cleanup; cancelled units were never refunded
inside the solve's accounting.

At the recorded Ireland Linux on-demand price of $1.123 per `g5.xlarge` hour, estimated compute
was **$20.4339 for 51 Batch instances**, plus **$0.2929 for the 939-second builder**:
**$20.7268 total**. The estimate uses provider launch-to-shutdown-transition lifetimes, including
startup, cancellation, idle/collection time and replacement instances. Provider billing was not
read. EBS, IPv4, S3, ECR, network and other service charges are excluded.

Fresh read-back confirmed all 51 recorded Batch volumes and the builder's recorded volume
gone, and all recorded instances terminated or absent. Queue, compute environment, managed
Auto Scaling group, both launch templates, interfaces, security group, IAM roles/profile,
private registry, staging bucket, deadline function/schedule and log groups were removed.
The managed ECS cluster is INACTIVE with zero tasks, services or registered instances.
The Batch definition remains INACTIVE as provider history. Pre-existing service roles and
unrelated infrastructure were preserved. Both operational reservations are released.

## Assessment and next gate

This closes the missing **complete public-data solve through real Batch/S3 transport** for
one synthetic intent. It supplies an observed public-solve latency and compute estimate,
including cancelled work. It does not estimate a production distribution or a matched baseline
speedup. Native counters and exact checking of emitted hits do not prove complete coverage of
every range. The prior small independent-reference cases retain their original source/runtime
identities; the missing planted zero-sighash case and broader hardware coverage remain open.

The candidate stays **HOLD** for evidence/contract and release-handoff review. Existing qsb-app
release descriptors and defaults remain unchanged. The ordinary release workflow still builds
the historical worker. PQB publication, enrollment and deployment require their own concrete
artifact and authorization; new builds require an explicit applicability review.
