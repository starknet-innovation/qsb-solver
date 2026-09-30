# Exact table inversion batching experiment

Research only. This independently implemented experiment replaces just
`kernel_build_gtable` in the current optimized subset source. It does not apply
PR #7's rejected SHA vector patch, import upstream GLV12 arithmetic, change table
geometry, or modify a production/release lock. Existing `GPUMath.h` field and
point operations remain byte-for-byte unchanged.

Each 32-lane warp computes a product tree of the original homogeneous Z values,
performs one existing five-limb `_ModInv` at the root, and distributes inverses
back down the tree. Copy records and padding lanes use identity leaves. Zero
(including the p representative) is excluded from the product; affected records
use the original per-record inversion. Every recovered nonzero inverse must be
canonical and multiply by the original Z to exactly one, otherwise that record
falls back to the original inversion. X/Z and Y/Z normalization and 64-byte
little-endian X||Y records are unchanged. All lanes reach every warp barrier.
The kernel explicitly rejects launch block dimensions other than (256,1,1).

## Preparation and native build

From the repository root:

```
python3 experiments/exact-table-batch/prepare.py /tmp/exact-table-build
nvcc -O3 -arch=sm_86 /tmp/exact-table-build/table-gate.cu -lcrypto -o /tmp/exact-table-build/table-gate
```

The preparer refuses baseline source/header drift and existing output directories.
It emits deterministic generated sources, an isolated candidate patch, unchanged
headers, and a SHA256 manifest. The native CI Dockerfile produces these plus the
binary, compiler output, linked libraries, binary hash and SASS under `/results`.
No GPU is required for compilation and no solver executes during preparation.

The default build tests the production mixed15 geometry. The same generated
source also accepts `-DZLAB_T14=1` for the optional mixed14 geometry; local CPU
geometry tests cover both, but native results must identify which was compiled.

## Native gate (bounded operator-controlled host only)

```
timeout 600 /path/to/table-gate /results/table.json
```

The executable accepts an exclusive output JSON path and optional
`--correctness-only`. This mode retains all four full-table differential checks
and independent OpenSSL samples, skips the timing loop, and writes
`"timingExecuted": false` with an empty `samples` array. Use this mode under
sanitisers to avoid spending time on instrumentation-distorted timing. It contains no solver
search, wallet, recovery or transaction code. It builds public elliptic-curve
lookup tables for scalars 1, 17 and a deterministic dense 248-bit integer, and:

* Compares every byte of three complete baseline/candidate tables.
* Independently checks 252 records per mixed15 table using OpenSSL scalar
  multiplication (chunk corners plus deterministic samples).
* Compares a fourth complete table with injected equal/opposite affine inputs,
  exercising zero-denominator fallback, while checking unaffected records too.
* Clears output to different baseline/candidate sentinels before every launch;
  an omitted candidate store cannot inherit a prior baseline value.
* Launches one extra all-padding block during exceptional differential checks.
* After these checks, records seven interleaved baseline/candidate timing pairs,
  comparing complete output and OpenSSL samples for each pair.

`kernel_ms` is CUDA-event time around the construction kernel only.
`construction_ms` is the harness wall time for ladder creation, memory allocation,
upload, table building, download, OpenSSL spot checks and cleanup. It additionally
includes sentinel memset and event-management instrumentation, so it is **not**
an identical measurement of production initialization or end-to-end solver rate.
Report both measurements and variability; kernel savings alone do not establish
an improvement in real job throughput. The completed earlier range campaign
observed a short table-initialization phase, so rejecting negligible benefit is
an expected valid outcome.

Native `compute-sanitizer` memcheck and synchronization/race checking are required
before adopting the synchronization-heavy implementation, for example:

```
timeout 600 compute-sanitizer --tool memcheck --error-exitcode 90 /path/to/table-gate /results/memcheck.json --correctness-only
timeout 600 compute-sanitizer --tool racecheck --error-exitcode 91 /path/to/table-gate /results/racecheck.json --correctness-only
timeout 600 compute-sanitizer --tool synccheck --error-exitcode 92 /path/to/table-gate /results/synccheck.json --correctness-only
```

A result JSON proves nothing about the sanitizer verdict without successful
process exit and the full sanitizer report. A timeout is incomplete, not pass.
Run each invocation under a separate
operator-enforced outer timeout, retain tool error exit codes and complete logs,
and do not mistake an incomplete/partial JSON for a passed gate. Native GPU
correctness/performance remains unverified until those executions complete.
Local CPU tests verify the algebraic product-tree specification, zero/p boundary
handling, source binding, patch isolation and complete geometry mapping; they do
not prove native execution of arbitrary synthetic denominator values.

## Licensing

No upstream implementation was imported. The extracted baseline arithmetic is
existing repository GPL-3.0 VanitySearch-derived code; its original copyright
and license header is preserved in the emitted `GPUMath.h`. Generated artifacts
must retain repository licensing and corresponding sources.

## Bounded combined host runner

`host.sh` runs memcheck, racecheck and synccheck in correctness-only mode before
the normal timing invocation. The combined sequence has a single 600-second
internal budget and a 720-second outer budget; these are not four separate
600-second allowances. The standalone commands above illustrate individual
checks, not the combined runner's time allocation. If this combined budget is
insufficient, the experiment is incomplete and requires diagnosis before any
subsequent allocation. No missing sanitizer result counts as a pass.

After result-directory creation, the EXIT handler records the original exit
status and packages available evidence even after staging, image-pull or GPU
identity failures. Container removal has a separate bounded timeout. Packaging
failure emits a collection-error marker with the original gate status, and a
successful gate with failed packaging returns failure. EC2 and volume cleanup
remain the independent controller's responsibility.
