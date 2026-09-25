# QSB solver

Public-data GPU workers for [qsb-app](https://github.com/starknet-innovation/qsb-app). The application retains its independent CPU verifier, coordinator, wallet and release registry. No verifier or wallet material is included here. An image identity is not evidence of solver correctness or complete range coverage.

## Historical worker

The upstream candidate tree at `2791ed0588f5014ccd688d48ba5502df2879f2f1` is committed under `vendor/challenge/candidates`. `vendor/challenge/provenance.json` identifies every imported file. `worker/prepare_kernels.py` applies the existing production-predicate/ranked-search adaptation; it does not silently repair historical arithmetic or output truncation.

```
python3 -m unittest discover -s tests -v
docker build --platform linux/amd64 -f worker/Dockerfile -t qsb-solver:local .
```

The worker accepts the historical `ranked-v2` public parameter requests and produces untrusted hit candidates and range reports. `contracts/ranked-v2.json` is the versioned cross-repository range-vector contract. Both repositories test the same vectors; changes to the partition require a new searchVersion.

## Research subset

`research/optimized-subset` and `worker/optimized` preserve the separate modified subset implementation and compute adapter. It remains **HOLD**, subset-only, and is not interchangeable with the historical worker. Its runtime deliberately excludes the former embedded CPU reference and accepts only describe/compute. This changes runtime identities; historical validation and old runtime hashes must not be reused as attestation of these builds.

```
docker build --platform linux/amd64 -f worker/optimized/Dockerfile --target runtime -t qsb-optimized:local .
python3 worker/optimized/test_image.py qsb-optimized:local
docker build --platform linux/amd64 -f worker/optimized/Dockerfile --target queue -t qsb-optimized-queue:local .
```

GPU differential tests and a fresh end-to-end proof are still separate from source/unit/build checks. No mainnet enablement or provider allocation is performed by this repository's CI.

## Release

A `v*` Git tag builds the historical worker for Linux amd64/sm_89, pushes `ghcr.io/starknet-innovation/qsb-solver` and attests its immutable digest. The release includes the descriptor template and exact range vectors. Consumers must select the digest, verify the GitHub provenance with `gh attestation verify oci://IMAGE@sha256:DIGEST --repo starknet-innovation/qsb-solver`, and enroll a new descriptor in qsb-app; existing archived descriptors remain unchanged. Tags label releases; they are not image identities.

Tagging triggers publication of compiled binaries. The user confirmed redistribution approval on 2026-09-25. That records the supplied approval, not an independent legal opinion. All upstream license and source notices remain in the tree and image. See [LICENSES.md](LICENSES.md).

Development validation scripts under `worker/validation` consume an explicitly supplied `QSB_CPU_REFERENCE_ROOT` pointing to qsb-app's independent `worker/cpu` checkout. They do not bundle or publish that reference inside the solver. Historical ranked-v1 tooling is retained only under `research/archived-validation` and must not be run as a current release gate.
