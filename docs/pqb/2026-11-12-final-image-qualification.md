# Final PQB image and publication review — HOLD

The final image includes the reviewed whole-log completion-parser fix. Build provenance,
installed parser regression, exact runtime identity and retained source notices are verified.
All three exact-image largest units and the independent consumer replay passed. Cleanup
is independently verified. Publication, release creation, descriptor enrollment and deployment
remain separate actions.

## Exact artifact

| Identity | Value |
| --- | --- |
| Image source / wire kernelCommit | `ecb31d384fbdec9c67cd802548460b774a722baf` |
| OCI index | `sha256:0fd3775769c9fb6d6611c5f30be4d901ae65fc0694ceb27853b826d4f3bb060c` |
| linux/amd64 manifest | `sha256:77b8c2db4ffb55923001b37c96599e0a3ae9a687ce06d5f386a9379b565550fe` |
| Config | `sha256:ab005b0d7a042bac05002ef6532a1f3886dca3f5bf23c57e514e61c92ec473b3` |
| Binary SHA-256 | `0e811c59de2d36f66142a6f65393c55a64e0e37c7eb40df4251f86b713ef3d82` |
| Installed parser SHA-256 | `9363f3ff3c0469db520e88a7e2575ca94d4012b2f01ccc5e98acff55901b712f` |
| Protocol / partition | `pqb-v1` / `pqb-ranked-v2` |
| Canonical contract SHA-256 | `5217daa6415b83dcce2d85159130df4994ab0e9bb67910c7bdf00e5804f4ee71` |
| Imported upstream | `fireblocks-labs/pqb` at `eccdd09772edf14ab37fc63992b0626ad7ff2221` |
| Build | nvcc 12.8.93, `-O3 -std=c++17 -arch=sm_86 -I /src/vendor/pqb/grinder` |

The [hosted build](https://github.com/starknet-innovation/qsb-solver/actions/runs/43179921372)
built the actual PQB Dockerfile's `aws` target. GitHub signed the original OCI archive,
asset checksums and prospective OCI subject. The verifier checks exact repository,
qualification workflow, source ref/commit, run identity and GitHub-hosted runner; every
OCI blob and signed asset is rehashed. Original signed bundles, verification output,
Docker configuration, actual package inventory, compiler receipt, source locks and notices
are retained. Mutable APT/Python resolution means this identifies exact bytes, not a
bit-for-bit reproducible rebuild. The archive remains unpublished; a signed prospective
GHCR subject does not establish registry availability.

The scan passed its stated policy: zero Critical matches with an available fix. It still
records 20 unfixed Critical package matches (and 89 High); the full findings remain assets.
The installed parser accepted a simulated single completion in a log over 2 MiB and rejected
an early duplicate in that full log. Those simulated checks are distinct from GPU evidence.
The actual no-GPU binary failure was separately checked and received no work credit.

## Native qualification

All three largest production units (attempt 0), each preceded by all 13 independent small
correctness cases, passed on one A10G (`g5.2xlarge`, Ireland 1b, driver 580.126.09).
The host verified actual loaded rootfs diff IDs and every runtime config field against the
attested archive before compute. The installed bound handler ran without a worker-code copy,
network access or experimental production flags. All production requests used the 24-bit
gate and unchanged 840-second worker timeout.

| Worker stage | Native worker seconds | With independent unit checking | Emitted candidates |
| --- | ---: | ---: | ---: |
| pinning | 492.831 | 492.867 | 0 |
| round0 | 506.204 | 506.229 | 0 |
| round1 | 490.848 | 490.889 | 1 |

Each full unit passed exact batch/range accounting, unique candidate checks, the statistical
gate-count bound and independent CPU re-derivation. These are single-unit timing boundaries,
not interleaved performance samples or full-pipeline throughput. The worker timing includes
its process/startup/output path; the next column also includes the external unit reference.
The device was warmed by the preceding small cases; this is not a cold-device measurement.
Separate app CPU checks are recorded below. Staging/import and the small cases are outside
these unit timers. The fixed 60-minute deadline and 3,100-second container bound were not
extended. The original 355,949-byte gzip receipt hashes to
`70526ef7da4920820e888bbaae5baa72b543e6b827ad1ea111f48584deb189ce`.
Its original bytes were downloaded and verified before decoding or termination.

See the [native summary](evidence/final-image-2026-11-12/native/summary.json) and original
archive in the [checksummed package](evidence/final-image-2026-11-12/manifest.json).

## Applicability and handoff

The complete local-Git source comparison includes additions and deletions. Only
`worker/pqb/build.py` and `worker/pqb/pqb_handler.py` changed among the actual build/runtime
source inputs since the earlier full-solve image. The adapted CUDA, headers, partition and
requested flags are unchanged, and the actual new binary is byte-identical. The build adds
an upstream-baseline hash check; the handler now rejects completion duplicates anywhere in
the log. Actual new runtime dependencies and the new handler retain their own evidence.

The earlier [complete public solve](2026-11-11-public-transport-solve.md) remains evidence for
its exact older image. The hardened replay of all 118 saved envelopes and 16 candidates has
now been regenerated successfully with inventory/hash/link checks, closing the stale-replay
item in the historical review. It does not relabel those GPU outputs as results of this image.

The pinned qsb-app `276f2ae09d50ca44d46b035e45b6d0365802edcf` (tree
`37e3b41d7142001d2cdf676f1101489e9d6e50f4`) accepted the final schema-3 descriptor in memory
and all three fresh native envelopes through its actual context/range/accounting checks.
Its packet parser and problem derivation reproduce all three committed public inputs.
The emitted round1 candidate passed `HitChecker` plus its canonical transaction recheck;
it is a valid gate/shape candidate, not a full solved stage. Wrong kernel, search version,
range and descriptor/contract identities were rejected. The descriptor remains unenrolled.
The initial local harness negative test incorrectly expected rejection of an unused protocol
extension in the response; the corrected test changes its actual searchVersion discriminator.
Both CPU receipts are preserved; no app behavior changed and no GPU work was repeated.

This image was natively exercised through its installed handler in isolated Docker. The
real complete Batch/S3 transport solve remains the earlier image's separate evidence;
this run is not another final-image Batch/served solve. The AWS entrypoint source is unchanged
and its offline hardened-transport checks passed in CI.

The [final descriptor](evidence/final-image-2026-11-12/release/descriptor-proposal.json) remains
a HOLD proposal with an unpublished image reference. Before
publication, review this package and the notices/redistribution scope. Preserve this exact
archive; do not rebuild it under a release tag. An authorized publisher must copy every
manifest with preserved digests, compare the registry's raw index bytes and amd64 manifest,
and verify GitHub provenance against the actual registry digest. Publish the exact contract,
schema-3 descriptor, binding/build receipt, checksum list, dependency/scan/notices and source
attribution with this assessment. Do not use the ordinary historical `aws-v*` release workflow
or the combined QSB candidate workflow: neither builds/publishes this PQB artifact.

Then, only with adoption authorization, enroll the descriptor verbatim as a new qsb-app release
file, regenerate the registry and run protocol/reference/range tests and app/coordinator/SDK
checks. Mirror the exact index into the serving account/region's ECR repository, bind a new
Batch job-definition revision and app manifest, and reconcile/drain pinned work before choosing
one served release. The current served consumer enforces gate accounting bounds but lacks the
development six-sigma sanity check; fix it with focused rejection tests or explicitly accept
that limitation before serving PQB.

Preserve the previous QSB descriptor/image/job definition for rollback. There is no previous
qualified PQB release: an old QSB worker cannot resume PQB work or spend PQB vaults. Stop new
PQB work and reconcile its paid jobs before restoring a QSB configuration. Never overwrite
old descriptors or reinterpret a pinned request.

This qualification does not measure another full solve, served Step Functions orchestration,
native exhaustion/re-pinning, a planted zero-sighash path, wallet authorization, Bitcoin Core
solved-spend consensus, miner acceptance or broadcast. It establishes neither broad completeness
against a dishonest worker nor matched speedup, population latency/cost, or lower on-chain fees.

## Cost and cleanup

The fresh campaign reserved $10, now released. Eleven setup/session identities were retained:
eight known capacity rejections (no instances), one prepared-only session (never armed/launched),
one allocated host whose import failed before native work, and the successful final session.
The failed Ubuntu 22.04 Skopeo/Docker API import was fixed with the host Docker client and an
actual local Docker 29 rootfs/config import check before the successful native allocation.
The first result-collection command failed before upload because SSM used sh; an explicit
bash wrapper collected the same completed archive. Neither failure triggered GPU work replay.

Compute estimated through the initial termination requests totals **$0.86**.
A conservative estimate through the independently collected terminated readbacks is
**$1.20**, including both allocated hosts. This is not provider billing;
storage, IPv4, network and other service charges are excluded. Exact cutoffs/rates and all
failed/incomplete work are retained in [cost accounting](evidence/final-image-2026-11-12/cloud/cost-accounting.json).

Fresh [independent reconciliation](evidence/final-image-2026-11-12/cloud/reconciliation-final.json)
confirms every owned instance terminated or absent, both recorded root volumes gone, and all
owned temporary IAM roles/profiles, groups, functions, schedules, native network interface and
both staging buckets removed. No unknown submission remains. Original failures and earlier
cleanup receipts remain intact, with fresh reconciliation separate. A nonbillable US G-vCPU
quota request remains CASE_OPENED; it allocated no hardware and does not authorize a new run.
No previous completed experiment, budget, deadline or automation was resumed.

## Reproduce verification

Keep both source checkouts clean and install the consumer's locked dependencies. Download
artifact `pqb-qualified-sm86` from run `43179921372` into an external directory. The original
archive is about 2.2 GB and is retained outside Git; its exact hash/size and the provider's
artifact metadata are in the evidence manifest. Do not substitute another run's image.

```sh
python3 scripts/verify_pqb_build.py BUILD_ARTIFACT_DIR NEW_VERIFICATION_DIR \
  --source-commit ecb31d384fbdec9c67cd802548460b774a722baf \
  --source-ref refs/heads/codex/pqb-qualify-20261112 --run-id 43179921372
python3 scripts/check_pqb_final.py CLEAN_APP_CHECKOUT \
  276f2ae09d50ca44d46b035e45b6d0365802edcf \
  EVIDENCE_DIR/native/public-result.json.gz 70526ef7da4920820e888bbaae5baa72b543e6b827ad1ea111f48584deb189ce \
  EVIDENCE_DIR/release/descriptor-proposal.json NEW_CONSUMER_RECEIPT_DIR \
  --build-artifacts BUILD_ARTIFACT_DIR
```

The native archive SHA-256 comes from this assessment's manifest and its independently
collected host receipt. The consumer checker validates the archive/member inventories,
loaded rootfs/config against the signed build, every stage's binding and original request,
all 13 small-case verdicts before each unit, the largest production ranges, completion/timing
and independent consumer derivation of every emitted hit. It never enrolls a release.
Reproducing these CPU/provenance checks does not launch hardware or repeat GPU work.
