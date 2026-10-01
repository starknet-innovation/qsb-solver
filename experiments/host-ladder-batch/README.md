# Isolated host point-ladder normalization experiment

This experiment compares the frozen `gt_build_ladders` public elliptic-curve helper with an independently written recurrence retaining separately owned points before one batch normalization. It extracts only geometry, affine export and ladder construction, retaining upstream GPL-3.0 licensing and fatal OpenSSL return checks. It does not build, execute or integrate a solver, search, recovery, transaction, or wallet input path. The CLI accepts an output path and fixed internal public fixtures only.

`prepare.py` rejects any mismatch in frozen source hashes and writes a manifest and upstream LICENSE. The default mixed15 geometry is the only supported/tested geometry: 19,200 allocated records, 12,002 populated points, and 7,198 zero/padding records per fixture. The old upstream comment about 8,176 points does not describe this geometry. Five fixtures are public scalar values 1, 2, n-1, 2^255 and 2^256-1. Each compares every baseline/candidate record byte-for-byte, checks every padding slot, and checks 90 selected ladder points with separate direct scalar multiplication and serialization. Those 90 ladder samples are distinct from production full-table spot checks and do not establish a full solver validation result.

Scalar zero and group order make the base infinity; normalization success does not make infinity finite. Four separate process tests require the original affine-export rejection for both implementations. Allocation, copy, point arithmetic, normalization, export and BIGNUM results are checked. Like the frozen baseline, the standalone process exits immediately on failure, so the OS reclaims partial allocations. This is not a reusable library API or a production error-handling proposal.

## Portability and evidence

[OpenSSL's migration guide](https://docs.openssl.org/3.0/man7/migration_guide/) deprecates `EC_POINTs_make_affine` and provides no replacement. This is an experiment-only dependency, not an adoption recommendation. The source fails compilation when deprecated API declarations are disabled and link/load fails if the symbol is absent; never silently substitute another algorithm. The pinned Python-enabled runtime digest `86eba696ee50bfd5e7b90eca1d3ed6dfa3f60582779a653eff5e9229b55cbfbf` was checked locally: OpenSSL 3.0.2 exports the API and an isolated one-infinity-point call returned success. That runtime lacks development headers. A build requires the separate Dockerfile or a local OpenSSL development installation.

Local macOS ARM64/OpenSSL 3.6.3 execution passed the fixed dataset and all four rejection modes. Baseline-first single-pair timings are diagnostics only: CPU architecture, OpenSSL version, ordering and instrumentation differ from A10G hosts. They establish no A10G performance, solver throughput, or production adoption claim. A Linux binary must be run and its dependencies checked against the exact intended runtime before remote use.

## Reproduce

From repository root:

```
python3 experiments/host-ladder-batch/prepare.py /tmp/host-ladder-build
c++ -O3 -std=c++17 /tmp/host-ladder-build/ladder.cpp -lcrypto -o /tmp/host-ladder-build/host-ladder-gate
python3 experiments/host-ladder-batch/check.py /tmp/host-ladder-build/host-ladder-gate /tmp/host-ladder-checks
```

Supply your installed OpenSSL include/library directories when needed. All output directories/files must be fresh. `check.py` bounds normal execution at 120 seconds and each negative test at 10 seconds. The Dockerfile uses the pinned CUDA development base only as a known Linux build environment; this experiment uses no GPU. It exports `/results/host-ladder-gate`, generated sources, manifest, binary SHA256, compiler, dynamic dependency and OpenSSL build receipts. Package versions are recorded, not claimed reproducible from unpinned apt metadata. No cloud resources are created by this directory.
