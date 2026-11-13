# QSB solver

Public-data GPU workers for [qsb-app](https://github.com/starknet-innovation/qsb-app). The application retains its independent CPU verifier, coordinator, wallet and release registry. No verifier or wallet material is included here. An image identity is not evidence of solver correctness or complete range coverage.

For verified publication and qsb-app enrollment status, evidence limits and the
documentation map, start with [docs/README.md](docs/README.md).

## Historical worker

The upstream candidate tree at `2791ed0588f5014ccd688d48ba5502df2879f2f1` is committed under `vendor/challenge/candidates`. `vendor/challenge/provenance.json` identifies every imported file. `worker/prepare_kernels.py` applies the existing production-predicate/ranked-search adaptation; it does not silently repair historical arithmetic or output truncation.

```
python3 -m unittest discover -s tests -v
docker build --platform linux/amd64 -f worker/Dockerfile --target aws --build-arg CUDA_ARCH=86 -t qsb-solver:local .
```

The worker accepts the historical `ranked-v2` public parameter requests and produces untrusted hit candidates and range reports. `contracts/ranked-v2.json` is the versioned cross-repository range-vector contract. Both repositories test the same vectors; changes to the partition require a new searchVersion.

## Research subset

`research/optimized-subset` and `worker/optimized` preserve the separate modified subset implementation and compute adapter. The standalone target remains **HOLD** and subset-only. The separately validated combined release includes this source lineage; see [release status](docs/README.md). Neither target is interchangeable with the historical worker. Its runtime deliberately excludes the former embedded CPU reference and accepts only describe/compute. This changes runtime identities; historical validation and old runtime hashes must not be reused as attestation of these builds.

```
docker build --platform linux/amd64 -f worker/optimized/Dockerfile --target runtime -t qsb-optimized:local .
python3 worker/optimized/test_image.py qsb-optimized:local
```

Source/unit/build checks do not establish native correctness or end-to-end execution. The exact combined release has separate native evidence; new builds need their own assessment. No mainnet enablement or provider allocation is performed by this repository's CI.

## PQB worker

[worker/pqb](worker/pqb/README.md) is a separate worker for PQB vaults (fireblocks-labs/pqb), with its own `pqb-ranked-v2` contract and an adapted copy of PQB's grinder that sweeps stated ranges exhaustively. Its [three largest native units](docs/pqb/2026-11-11-full-unit-validation.md) and [13 native correctness cases, consumer checks and image scan](docs/pqb/2026-11-11-correctness-consumer-validation.md) passed their stated criteria.

A [complete public synthetic solve through the real consumer Batch/S3 transport](docs/pqb/2026-11-11-public-transport-solve.md) then verified all three stages in 91 minutes 40 seconds, at $20.73 estimated compute including its builder. That development-orchestrated assessment excludes the served coordinator, wallet and consensus/miner paths. Cleanup is independently verified. The [TLS-fixed PQB release](https://github.com/starknet-innovation/qsb-solver/releases/tag/pqb-aws-sm86-v0.1.0) is published; its descriptor is handed off through [qsb-app PR #150](https://github.com/starknet-innovation/qsb-app/pull/150). The [final image assessment](docs/pqb/2026-11-12-final-image-qualification.md) qualifies the parser-fixed image with signed build provenance, three fresh largest native units, 13 correctness cases before each unit and an independent qsb-app replay. The [Critical findings review](docs/pqb/2026-11-12-critical-review.md) found a reachable TLS trust-store blocker. The merged source fix is built into the [TLS replacement](docs/pqb/2026-11-12-tls-replacement.md), whose exact compute stack matches the retained native evidence. Fresh installed TLS/S3 checks and hosted archive checks passed; the published digest and original build provenance verify from the registry. A [fresh isolated consumer-workflow assessment](docs/pqb/2026-11-13-serving-validation.md) now passes the A10G preflight, complete synthetic Step Functions/Batch solve, independent CPU audit and thirteen offline Core checks, with verified cleanup. The descriptor is enrolled through merged PR #150; production still selects Config A, and its account-specific PQB runtime remains to be qualified. See the [assessment](docs/pqb/ASSESSMENT.md). Historical and combined QSB releases remain unchanged.

## Release

PQB has a separate [final-image qualification plan](docs/pqb/FINAL-IMAGE.md). Its explicit
`codex/pqb-qualify-*` push workflow exports and signs an exact OCI artifact for native
qualification; it does not push a registry image, publish a release or enroll a descriptor.

An `aws-v*` Git tag builds the historical worker for Linux amd64/sm_86 (AWS A10G), pushes `ghcr.io/starknet-innovation/qsb-solver` and attests its immutable digest. The release includes a schema-v3 descriptor and exact range vectors. `searchContract` is the SHA-256 of UTF-8 canonical JSON (recursive sorted keys, compact separators, array order preserved) for `contracts/ranked-v2.json`. The descriptor generator checks every valid and invalid vector against the worker before hashing. Consumers must require the same hash as their independently tested contract. Earlier schema-v2 releases remain immutable; they do not gain this binding retroactively, and a new tagged release plus explicit consumer enrollment is required. Consumers must select the digest, verify the GitHub provenance with `gh attestation verify oci://IMAGE@sha256:DIGEST --repo starknet-innovation/qsb-solver`, and enroll a new descriptor in qsb-app; existing archived descriptors remain unchanged. Tags label releases; they are not image identities.

NVIDIA does not rebuild CUDA image tags, so runtime stages apply current Ubuntu updates to the pinned base at build time, from Ubuntu's archives only (NVIDIA's apt source is excluded, keeping the pinned CUDA packages). OS package versions therefore depend on the build date. That update step retries up to three times, refreshing the package index each time, because Ubuntu's mirrors can briefly list a superseded file that is already gone. Publishing workflows scan with a pinned Grype (`scripts/image_scan.py`). They fail on critical findings that have a fix, rating each by the worse of the distribution and NVD severities. `candidate-sm86-*` scans before push. `aws-v*` scans the pushed digest before attestation, descriptor and release, so a failed scan leaves an unattested tag that consumers cannot enroll. The release carries the summary as `image-scan.json`. It is a point-in-time package scan. It is not correctness evidence, and nothing here rescans published images.

Tagging triggers publication of compiled binaries. The user confirmed redistribution approval on 2026-09-25. That records the supplied approval, not an independent legal opinion. All upstream license and source notices remain in the tree and image. See [LICENSES.md](LICENSES.md).

Development validation scripts under `worker/validation` consume an explicitly supplied `QSB_CPU_REFERENCE_ROOT` pointing to qsb-app's independent `worker/cpu` checkout. They do not bundle or publish that reference inside the solver. Historical ranked-v1 tooling is retained only under `research/archived-validation` and must not be run as a current release gate.

## Optimized promotion work

[Combined candidate integration](worker/promotion/README.md) joins historical
pinning and the optimized subset under one `ranked-v2` worker identity. The tested sm86 combined image was published and its descriptor enrolled in qsb-app;
see [verified status](docs/README.md). New candidate prereleases remain HOLD until native correctness, matched A10G performance for
pinning and both subset rounds, and final evidence review pass. `aws-v*`
tags still build the historical baseline.

The user removed the fresh wallet-backed regtest search from this release's gates
on 25 September. Preserve prior evidence; do not start a fresh search for PR #2.
The first separately authorized mainnet pilot will be the end-to-end test of this
release. Publication and app enrollment each require explicit user approval.

### Attested AWS release

AWS Batch is the only transport. Historical releases use the `aws` target of `worker/Dockerfile`; combined releases use `worker/promotion/Dockerfile`. The PQB release uses `worker/pqb/Dockerfile` and copies its qualified archive through the dedicated publication workflow. These paths use CUDA architecture 86 (A10G); an ordinary `aws-v*` tag does not build PQB. The Runpod transport was retired on 1 October 2026: `v*` and non-sm86 `candidate-*` tags no longer publish, and the earlier Runpod releases (`v0.1.0`, `candidate-20260925-1`, `candidate-20260925-2`) remain immutable records. The development AWS artifact workflow uses that same Docker target; its tarball alone is not an enrolled release.

After CI succeeds, verify the generated descriptor's GHCR digest and source commit with `gh attestation verify`. To mirror it into a private registry, use a digest-preserving registry copy (for example `crane copy GHCR_IMAGE@sha256:DIGEST ECR_REPOSITORY:RELEASE_TAG`) and verify the destination manifest digest equals the attested digest before registering a Batch job definition. Keep the public descriptor's canonical GHCR identity; operator registry/account configuration belongs outside this repository. Never substitute a digest from a `docker load`/`push` round trip or treat the mirror's name as provenance. Consumer enrollment and deployment remain separate steps requiring that exact digest and fresh runtime verification.
