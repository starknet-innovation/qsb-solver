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
and do not mistake an incomplete/partial JSON for a passed gate. The recorded native result below covers only its stated geometry and inputs.
Other configurations remain unverified.
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

## Collected evidence acceptance

After the committed collector verifies the envelope size/hash and writes its
files, run `verify_results.py RESULTS OUTPUT --binary-sha256 EXPECTED_SHA
--image EXPECTED_DIGEST --command-exit OBSERVED_SSM_EXIT`. Supply the independently
observed terminal command exit, not a value inferred from report text. The output
file must not already exist. Expected binary/image identities come from the
prelaunch plan. This validator does not establish cloud cleanup or source provenance.

Acceptance requires all four complete mixed15 reports, clean tool-specific
sanitizer summaries, identical ordered table hashes, one A10G, and all seven
alternating timing pairs. Duplicate JSON keys, nonfinite values, incomplete
receipts, mismatched runtime/binary identities and ambiguous sanitizer summaries
fail closed. Zero measured kernel duration is inconclusive for ratios and is
also rejected. The summary retains every paired time ratio plus median/range;
it explicitly grants neither solver speedup nor range credit. All input files
are hashed in the receipt, while raw GPU UUIDs remain private operational data.

## Native result, 30 September 2026

On one NVIDIA A10G, all four complete mixed15 table comparisons passed, with
1,048,576 records per table, 30 exceptional inputs and 252 independent OpenSSL
samples per normal table. Memcheck, racecheck and synccheck completed with clean
reports before timing. [Raw samples](evidence/normal.json), sanitizer reports and
[the bound summary](evidence/summary.json) retain the public evidence.

Across seven alternating pairs on that GPU, kernel time decreased by a median
7.49% (individual decreases 6.76–8.22%), saving about 0.229 ms per table.
Instrumented construction time decreased by only 0.10% at the median; individual
pairs ranged from 0.67% slower to 0.75% faster. These are observed paired ranges,
not confidence intervals. This single-host run establishes a kernel-level benefit,
but no convincing construction-level benefit or solver throughput improvement.

Recommendation: keep the change experimental. Do not integrate or promote it on
throughput grounds from these measurements. The construction measurement includes
CPU preparation, OpenSSL checks, copies and harness instrumentation; it is not
a production initialization benchmark. Coverage excludes mixed14, arbitrary
inputs and end-to-end search. Production source and release identities are unchanged.

The host, recorded root volume and all scoped temporary resources were independently
verified removed at 20:17:40 UTC. This new USD100 campaign retains a USD5 conservative
charge for the allocation; that amount is not an observed invoice charge.
