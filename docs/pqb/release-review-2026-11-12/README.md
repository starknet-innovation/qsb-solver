# PQB release/adoption review — HOLD

Reviewed 12 November 2026 against PR #18 source
`b0ea0147eb6680b9e16e1a69129307ebe2f0339b` and qsb-app PR #150 source
`276f2ae09d50ca44d46b035e45b6d0365802edcf` (tree
`37e3b41d7142001d2cdf676f1101489e9d6e50f4`). The disposition is **retain for review,
do not publish or adopt the measured image as a release**. Preparation adds no enrolled
descriptor, served release, cloud resource or transaction.

## Descriptor and artifact identity

[`descriptor-proposal.json`](descriptor-proposal.json) is a **HOLD review envelope**,
not a release asset named `solver.json`. Its inner `solver` satisfies the pinned consumer's
strict schema 3 and its independently generated contract hash. Its GHCR reference is
**prospective and unpublished**: it reuses the actual recorded private-validation index
digest only to express the measured artifact's proposed identity. Registry availability
and GitHub build provenance have not been verified. Never copy this inner object into the
app registry or use it to authorize a pull, publication or deployment.

| Identity | Bound value / source |
| --- | --- |
| Measured image source / wire `kernelCommit` | `4bfd8f1f7011331979f33b60bb8c6e379227ca16` |
| Adapted upstream / generator | `fireblocks-labs/pqb` at `eccdd09772edf14ab37fc63992b0626ad7ff2221` |
| Protocol / partition | `pqb-v1` / `pqb-ranked-v2` |
| Canonical contract SHA-256 | `5217daa6415b83dcce2d85159130df4994ab0e9bb67910c7bdf00e5804f4ee71` |
| Binary SHA-256 | `0e811c59de2d36f66142a6f65393c55a64e0e37c7eb40df4251f86b713ef3d82` |
| OCI index | `sha256:4212bcf06999da2b8084247c17d3fc0e2786e46cf356cb17e7ea971809e190c5` |
| linux/amd64 manifest | `sha256:8f942ed252394c25bad8f378ac547b90e2773e73fe1fd44a36eb6af8387a9de0` |
| Compiler / flags | nvcc 12.8.93; `-O3 -std=c++17 -arch=sm_86 -I /src/vendor/pqb/grinder` |
| Runtime / host | Pinned CUDA 12.8.1 base plus build-time Ubuntu updates and boto3 1.42.0; A10G / g5.xlarge, driver 580.178.04 |

The [original package](../evidence/public-transport-2026-11-11/README.md) retains the full
source lock, compiler output, installed-file binding, image inspection, runtime packages,
native image scan and manifest. The generator checks all 79 manifest file hashes, raw OCI
index bytes, source-lock and vendor hashes, Python source identities, runtime command and
every valid/invalid partition vector against **the image source commit**. It does not turn
recorded build claims into a signed provenance attestation. The 2,210,919,793-byte local image
archive was freshly rehashed to its retained SHA-256
`114ec543d414d2eb69875208f506ce395232082911916f6ca6a04ed133f8e229`.
The [complete source comparison](source-comparison.json) inventories additions, deletions
and modifications between the measured and reviewed commits using local Git trees without
GitHub file-list limits. It is an identity inventory, not a claim of a fresh whole-code audit.

MIT licensing, upstream third-party notices, retained source and adapted-source attribution
remain required assets. The Dockerfile copies them into the image. No CPU verifier, wallet,
key material or release registry moves into the worker. Pinned base images plus mutable
APT/Python dependency resolution do **not** imply a bit-for-bit reproducible rebuild.

## Applicability decision

| Evidence / source difference | Finding and disposition |
| --- | --- |
| Completed public transport solve | Applicable to the exact `4bfd8f1` image: 143 submissions, 118 completed units, 25 terminal cancellations, 16 emitted hits and three full hits. qsb-app and pinned upstream native coincurve/libsecp checked all completed outputs/hits. Retain. |
| Whole-log completion parser | Reviewed source scans the whole log for duplicate completion records; the measured image scanned only its last MiB. The old native solve does not attest to this fix. **Refresh the image before release.** |
| Build-time upstream-baseline hash check | Reviewed `build.py` additionally verifies the original upstream grinder before compiling. Same CUDA source, partition and requested flags; a fresh build still needs its actual binary hash. |
| Arithmetic / partition | Locked CUDA source, headers and partition bytes are unchanged between measured and reviewed image inputs. Older arithmetic evidence remains supporting evidence under those exact identities, not a new runtime attestation. The proposal records both changed runtime-input hashes. |
| Current control/collection fixes | Deadline cleanup now permits deletion of a disabled terminal `INVALID` queue; setup-failure collection preserves the real exit code; reference export selects only the current chain after re-pinning. Local simulated regressions pass. No new native/cloud campaign validates these changes. |
| Native largest units and 13 correctness cases | Supporting evidence with their original binaries, handlers, source and runtime identities; do not relabel them as tests of a new image. |
| Performance | One complete solve: 5,499.724 seconds. Earlier matched A10G component results remain component results. No matched whole-pipeline speedup, population cost/latency distribution or lower transaction fee is established. |
| Vulnerability policy | Actual native image scan: zero fixable Critical, 20 unfixed Critical package matches; policy passed. Refresh the scan for any new artifact. |

The separate [consumer compatibility receipt](descriptor-compatibility.json) replays all
118 retained native envelopes through the actual consumer response/context/range checks;
all 16 candidates are within their assigned ranges. It verifies schema/contract compatibility,
rejects wrong protocol/generator/contract, private-image references, duplicate IDs and the
outer HOLD envelope, and confirms this release ID is **not enrolled**. These are fresh CPU
compatibility checks, not new native execution or new cryptographic verification of the hits.

That receipt and `local-checks.json` record harness `4bffafbf…`. After review the harness was
tightened: the replay archive must be a hashed manifest entry, every archive member must match
`archiveMembers` by path, size and SHA-256 with none missing, extra or repeated, and evidence
entries reached through a symbolic link are refused. The retained receipt has **not** been
regenerated with the tightened harness; the new checks were run only by the unit tests against
this package (118 envelopes, inventory matched). Regenerate it before relying on it for adoption.

The worker counts gate hits as a sanity check on performed work. All 118 saved results pass
the development controller's `6 * sqrt(trials / 2^24) + 6` bound. The pinned **served** consumer
checks trial totals and gate-count accounting bounds, but does not apply that statistical
bound. Close that consumer difference with focused rejection tests, or record an explicit
adoption decision accepting the limitation, before serving PQB. Neither counts nor exact
checking of emitted hits proves complete coverage against a dishonest worker.

Other limits remain: one GPU model and one complete workload; no native exhaustion/re-pinning
run, dedicated planted zero-sighash branch, served Step Functions solve, wallet authorization,
solved-spend Bitcoin Core check, miner acceptance or broadcast. Preserve the accepted hybrid
round hit under the pinned generator's policy. Do not substitute an unreviewed STRICTENC policy.

## qsb-app handoff

1. **Qualify the final artifact.** Start from a clean committed/pushed source including the
   reviewed parser fix. Build `worker/pqb/Dockerfile`, target `aws`, architecture `86`, with
   `SOLVER_COMMIT` equal to that source. Retain installed Python/binary hashes, exact build
   receipt, config, package inventory, notices and source. Run offline image/failure checks
   and review which public native cases must be repeated for that exact artifact. Unchanged
   binary bytes alone do not qualify changed Python, packages or runtime. Do not restart the
   closed solve or reuse its budget/deadline; any necessary native assessment needs a fresh
   committed collection plan, reservation and independent cleanup.
2. **Prepare the actual publication path.** Existing `release.yml` builds historical QSB;
   `candidate.yml` builds the combined QSB worker. Neither publishes PQB. A dedicated reviewed
   path must build the actual PQB target, scan before release, record the pushed immutable
   index and platform digests and attest the exact source/workflow on a GitHub-hosted runner.
   Verify `gh attestation verify` with the actual repository, signer workflow, source tag/ref,
   source commit and `--deny-self-hosted-runners`. Publication remains a separate action;
   this package neither creates a tag nor claims a public digest exists.
3. **Regenerate the release assets.** Extract identities from the final provenance-verified
   image; recheck the matching contract vectors. Publish the final schema-3 `solver.json`,
   exact `pqb-ranked-v2.json`, checksums, installed binding/build receipt, dependency inventory,
   scan, notices/source attribution and correctness/applicability report. Source and kernel
   commits must be the final image's values; this historical proposal cannot be relabeled.
4. **Enroll only with explicit authorization.** In qsb-app, verify the final GHCR provenance
   and compare the release asset byte for byte; add it verbatim as a new file in
   `src/lib/releases`, regenerate the registry, and run protocol/reference/range tests,
   typecheck, frontend build and coordinator/SDK checks. Leave archived descriptors intact.
   Run this handoff's compatibility replay against the final descriptor and pinned app.
5. **Review serving separately.** Copy the exact attested index digest into the queue account
   and region's `qsb-solver` ECR repository using a digest-preserving registry copy. The removed
   `qsb-pqb-solve-*` validation repository is not an acceptable production mirror. Verify
   destination digest, hardened entrypoint, sm86/A10G runtime, timeout, budgets and CPU checks.
   Bind a new Batch job-definition revision and app build manifest to the same descriptor.
   Drain/reconcile old pinned jobs before selecting the single `SOLVER_RELEASE_ID`.

Serving PQB changes which protocol can start withdrawals: a deployment serves one protocol,
and Config A withdrawals cannot use a PQB worker. A deposit remains independent of release
selection. Mainnet enablement, exact transaction authorization, signing and broadcasting
are not part of this handoff.

**Rollback:** preserve the enrolled QSB descriptor
`src/lib/releases/qsb-solver-combined-aws-sm86-v0-3-0.json` and its previous image/job-definition
and app manifest. Confirm the actual served revision at deployment review; it was not queried
here. That Config A release cannot resume PQB jobs or spend PQB vaults. There is no prior
qualified PQB release: stop new PQB jobs, reconcile/drain their paid work, and retain their
pinned evidence before restoring a QSB configuration. Never silently reinterpret a pinned job.

## Reproduce the preparation

Run from this repository with the historical commits available (`git fetch` if needed):

```sh
python3 -m unittest tests.test_pqb_descriptor -v
python3 scripts/pqb_descriptor.py \
  --evidence docs/pqb/evidence/public-transport-2026-11-11 \
  --review-commit b0ea0147eb6680b9e16e1a69129307ebe2f0339b \
  --output /new/external/path/descriptor-proposal.json
python3 scripts/check_pqb_release.py /clean/qsb-app \
  276f2ae09d50ca44d46b035e45b6d0365802edcf \
  docs/pqb/evidence/public-transport-2026-11-11 \
  /new/external/path/descriptor-proposal.json /new/external/compatibility-directory
```

The consumer needs its locked Node dependencies. The checker creates a new external output
directory and calls the app's actual TypeScript; it never writes its registry. The scripts
only prepare/check the retained private-validation proposal, not descriptors for arbitrary
future images. Fresh publication needs the final artifact path and provenance checks above.

Fresh [local verification](local-checks.json) also covers the reviewed controller's simulated
identity/reservation/one-shot paths and current-chain export after synthetic abandoned epochs.
The export regression reproduces the original three public reference packets/problems exactly.
The Python suite includes evidence-tamper, wrong-source, compiler flags and runtime-command
rejections, disabled invalid queues, transitional queues and setup timeout receipt checks.

## Cost and cleanup

Preparation used local CPU checks only: no paid submissions, new reservations or resources.
The completed campaign's $20.7268367 is estimated list-price compute including the builder
and cancelled work, **not provider billing**; other services are excluded. All 52 recorded
volumes and temporary resources were independently reconciled in the
[original closeout](../evidence/public-transport-2026-11-11/reconciliation-final.json), and its
$200 solve / $2 builder reservations are released. Original receipts remain unchanged.

The next evidence gap is a qualified final image incorporating the reviewed parser, with
fresh artifact identities and a reviewed provenance/publication path. Enrollment and serving
are still separate decisions.
