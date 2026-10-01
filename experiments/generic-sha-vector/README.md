# Isolated generic SHA schedule vector loading

This patch changes only generic cached-tail schedule loads, preserving eight SHA rounds and their order. Production sources, source locks and release identities are unchanged. `prepare.py` verifies the baseline source hash, applies the isolated patch in a temporary directory, then extracts both actual functions into a native CUDA differential harness.

Host extracted-function gate: 170,000 comparisons, clang address/undefined sanitizers, passed. Native gate compares both CUDA functions against a separate CPU round loop, including every intermediate block, zero/all-one/random schedules and 1,024 random states. Expected 174,080 comparisons. Compile with CUDA12.8 and `-O3 -arch=sm_86 -std=c++17`, run normally and under compute-sanitizer memcheck. Retain compiler flags, binary hash and outputs.

This is not full-solver certification or a performance result. Follow with full-transaction differentials, all tail alignments, and interleaved same-GPU complete-solver timing before adoption. Two uint4 expressions do not guarantee faster machine code; inspect emitted SASS and register usage. No release publication or activation is implied.

## 30 September native attempt

A single g5.xlarge launch in eu-west-1c returned explicit `InsufficientInstanceCapacity`. No instance was allocated and no native gate ran. Independent post-check confirmed zero instances for the request token and removal of its security group, cleanup schedule/function, roles and instance profile. Native correctness and performance remain pending; host results above are unchanged. The experiment controller/gate commit was `5292e651b58957918abaded5235a343105a75f4f`. Retry requires a fresh execution state and another capacity/price/watchdog preflight.

London 2a and 2b also returned explicit capacity rejection; all temporary resources were independently removed. Local execution-image preflight found that the historical audit image contains prebuilt tests but no nvcc. The host gate now pins the CUDA development image directly. Local x86 emulation crashes nvcc with exit139, so the dedicated Linux CI compilation gate records compiler output, binary hash and SASS without GPU allocation or registry publication. It does not execute the kernel or establish speedup.

Native Linux CI run 36692760138 at bea21976f0411b1eba19289c02a53fa2f2a54788 compiled the extracted gate successfully with CUDA12.8.93, sm86, 45 registers and no stack/spills. Binary SHA256: 621ad5bf76de6dca99f0bb19a08e2315de62878d0d03110c2e4bbbc9bec6fcf6. SASS contains two LDG instructions of width128. These are combined differential-kernel statistics, not standalone candidate occupancy or performance. Logs/hashes are under evidence/. The CI now also builds an isolated full baseline/candidate solver pair from verified source inventory for subsequent matched tests; those outputs are not enrolled releases.

Full solver compilation passed in native Linux CI run [36693028154](https://github.com/starknet-innovation/qsb-solver/actions/runs/36693028154), source commit 06b0c3222a5d59f75b1a3bf66d5af82cd0ec8fdd. Downloaded artifacts were independently SHA256-verified. Baseline is 8664f41f3deeeb91b3d189db3df469570c83e90610e4b54a955e2a625486606c; candidate is 0fe47c3bd6b5b3671f02af242095922acd418ea5ab7c2f13647b0b386782ea7b. Both kernel_digest builds use 128 registers, a 272-byte stack frame, 28 bytes each spill stores/loads and 24,576 bytes shared memory. The baseline has eight LD.E instructions where the candidate has two LD.E.128; static kernel instructions decrease from 36,739 to 36,732. These are static compiler observations, not dynamic throughput or correctness evidence. GPU differential, memcheck and matched performance remain pending capacity. Build/package details and disassembly hashes are in evidence/solver-pair-build.json and evidence/kernel-comparison.json. GPU execution must use a fresh scope and the corrected development image; never reuse prior rejected launch records.

## Prepared matched timing runner

`run_pair.py BUNDLE OUTPUT FIXTURE_SHA256` accepts the two exact binaries above as `BUNDLE/baseline` and `BUNDLE/candidate`, plus hash-bound `BUNDLE/fixtures.json`. The fixture inventory must contain both rounds for SegWit and Taproot. Use only reviewed synthetic public fixtures. Run the native differential and memcheck gates successfully before timing; this runner does not replace those gates.

The runner requires one A10G and records 24 interleaved startup-inclusive samples, three baseline/candidate pairs per context, each covering 2^29 ranks from zero. Each process has a 120-second limit within a 600-second total deadline. Complete output, exact attempted count, no hit files, and both frozen binary identities are required for a gain summary. Unexpected hits stop timing for CPU review. Failures retain diagnostics and never produce a partial gain claim. Output is exclusive on creation and progress is fsynced. Projected full-range time is an estimate, not a measured full-range result.

Five local tests cover source preparation and timing acceptance/rejection; CI runs them before compiling the native gate. No matched GPU timings have been collected. The subsequent London 2a attempt also returned explicit capacity rejection; independent cleanup confirmed no allocation or remaining temporary resources.

## Full-binary sampled range prerequisite

`run_ranges.py BUNDLE BUNDLE/regression.json` runs 32 exact-binary checks: both binaries on four ranges for each of the four synthetic benchmark contexts. The ranges are `(start,count)` = `(0,1)`, `(63,257)`, `(65535,65537)`, `(0,2^26)`. The committed public fixture file is pinned to SHA256 `e7975d3061ccd7246c0d4548eeab201710a93959b63a2fcbd3a602e9790b99b9`. This is sampled range/output regression only, not full CPU differential, all-alignments coverage or a fresh withdrawal.

The timing runner now refuses to start unless `BUNDLE/regression.json` reports completion, contains every expected successful sample and matches both binary hashes and the fixture hash. It records the regression receipt hash. These checks bind local evidence; they are not remote attestation. Seven local tests pass, including incomplete inventory, wrong rank/count, failed process, unexpected hit and shortened completion rejection. Neither the sampled native regression nor timing has run on a GPU yet.

Keep correctness and timing in separately bounded scopes if the remaining host deadline cannot accommodate both. The 25-minute cleanup deadline must never be extended to finish timing.

## Diagnostic CPU differential preparation

The pair build also emits `candidate-trace`, `candidate-trace.diff` and `trace-receipt.json`. Instrumentation accepts only the frozen vector source hash and adds a single recovered-key hash print before predicate selection. The receipt binds the diagnostic source, patch, flags and binary to the separately preserved unmodified candidate. This allows subsequent public full-transaction CPU checks; diagnostic execution is not execution attestation for the unmodified candidate. Neither predicates nor the measured candidate artifact are changed. Eleven local tests pass, including rejection of baseline, modified or already-instrumented source. Diagnostic GPU execution and CPU verification remain pending.

`run_trace.py BUNDLE OUTPUT TRACE_RECEIPT_SHA256` collects both diagnostic and exact-candidate execution for the 20 committed `worker/promotion/validation/trace-fixtures.json` cases (SHA256 `e9e4f2abfdb27195f9e67d18b86990fc9419008084a9a142f24e127a89be1104`). Place that file in the bundle alongside the candidate, trace binary, patch and receipt. Every trace must contain both recovery branches for exactly the requested lexicographic combinations; missing, duplicate, malformed and out-of-range records reject. The 600-second internal deadline and per-process limits remain in force. A completed collection is explicitly `native-completed-awaiting-cpu-verification`, never a CPU verdict or durable credit. Thirteen local tests pass; real GPU traces and their separate CPU/full-transaction verification remain pending.

Independent verification: `verify_trace.py NATIVE_RESULT CPU_REFERENCE_ROOT experiments/generic-sha-vector/fixtures OUTPUT`. The external public CPU implementation is the three named modules under `worker/cpu` in qsb-app commit `b737fc6e6c1f4114fcd655b2f57f99224f79f280`; `cpu-reference-lock.json` checks each byte before import. The public synthetic state/parameter sidecars are included under `fixtures/` and separately hash-checked. The verifier reconstructs full transaction sighashes and compares recovered-key puzzle hashes, while requiring exact native case inventory and complete unmodified-binary range output. A one-candidate CPU-generated positive control and corrupted-hash rejection passed locally; this is verifier testing, not native evidence. Native Linux CI run 36696374308 built the trace successfully, and downloaded artifact hashes were checked. The unmodified candidate remains byte-identical; see `evidence/trace-build.json`.

The verifier accepts optional `--workers 1..4` (default 1) for independent CPU
case verification. This reuses the parallel-verification design in upstream
`harness/verify.py` at `ff27a2b66990a3eb554a1d4453e896c0397337ba`, with a locally
written scheduler. Unlike upstream's fork/all-CPU implementation, this offline
tool spawns a bounded number of workers after copying hash-verified reference
modules into a private temporary directory. No candidate process runs during
verification. Ordered results and all checks are preserved; any worker failure
prevents a passing receipt. Workers may finish already queued work before an
error returns. Apply an outer process deadline when operating the verifier.
This option does not change solver execution, reference arithmetic, fixtures,
receipt contents, search coverage or image qualification. Scheduling tests are
separate from native-trace equivalence and performance measurements.

### Offline verification scheduling result, 1 October 2026

On the local macOS ARM64 host, three interleaved serial/four-worker pairs checked
the same saved native trace: 20 cases, 3,116 candidates and 6,232 hashes. All six
passing receipts were byte-identical. Serial median command time was 127.363 s;
four-worker median was 34.720 s. Candidate/baseline paired ratios were
0.2624, 0.2727 and 0.2688 (median paired latency reduction 73.12%). These three
observations are not confidence intervals or evidence of A10G/Linux performance.
Timing includes process startup, reference loading, checks, receipt writing and
exit; no GPU search ran. CPU time, energy and dollar cost were not measured.

Both modes rejected a one-nibble corruption in an existing trace hash without
writing a passing receipt. The unchanged verification functions were also
compared structurally against the original source. The full local suite ran
196 tests successfully, with one skipped. An earlier timing attempt failed
before verification because relocating the baseline broke relative fixture
lookup; that failed attempt is retained and excluded in full. All reported
pairs used an intact frozen baseline source snapshot.

See `evidence/parallel-cpu-verification.json` for all six samples, source bindings
and rejection summaries. The candidate is qualified only as optional local
offline-verifier scheduling; serial remains the default. The verifier is not
packaged in the worker image, so this result does not justify publishing a new
worker image or claiming cheaper transactions or complete-pipeline improvement.

## Native results, 30 September

### First-valid verification scheduling experiment

`ordered_verdicts.py` is a separate experimental adapter for independent pure
verification checks. Unlike the all-cases diagnostic verifier, it selects the
first accepted verdict in input order, preserves all-DER-only rejection, and
propagates errors only before acceptance. It caps outstanding checks at the
chosen worker count (one to four), cancels queued checks on exit, and joins
running workers. Callers must still enforce an outer process deadline; running
checks can delay shutdown after early acceptance.

Seven control-flow tests cover these cases, bounded prefetch and resource
limits. A separate local comparison with the unchanged qsb-app public handler,
using stub exports and verdicts, matches four cases at one, two and four workers.
Those stubs do not establish cryptographic correctness or production integration.
The adapter is not wired into qsb-app or a worker image. It needs isolated public
reference initialization and matched representative workload measurements before
adoption; extra work after early acceptance can outweigh parallelism.

A real-reference follow-up used the unchanged frozen qsb-app handler on one or
32 existing diagnostic records (all rejected), with three interleaved pairs on
the same local macOS host. Serial/four-worker median process times were
0.199/0.300 s for one record and 1.524/1.165 s for 32. Median paired elapsed
ratios were 1.502 and 0.760; CPU-time ratios were 1.433 and 2.830. The adapter
called the original handler separately per record, including repeated parameter
export, while serial exported once. This isolates a concrete setup-cost problem;
it does not justify a default parallel path. The parent timer includes startup,
hash checks, exports, verification, worker shutdown, durable receipt and exit.
All 12 samples and source/input bindings are retained in
`evidence/first-verdict-public-reference.json`. No successful-hit workload,
full solver pipeline, cloud-dollar saving or image promotion was measured.

### Saved trace replay on Linux

`evidence/native-trace-replay.json.gz` is a deterministic gzip copy of the
existing public synthetic diagnostic trace from 30 September. Its uncompressed
824,188 bytes have SHA256
`8c376571eb56e48d125bdec7de6b0df91d4972f28b4228f4cd1486961fb43e04`.
It contains saved outputs, not a new GPU execution or performance measurement.
The `Saved public trace verification` workflow fetches the three pinned public
CPU reference modules, checks their locked hashes, and verifies the saved trace
with four worker processes in the immutable validation runtime. The container
has no network, a read-only root, a two-CPU quota and a ten-minute timeout.
The resulting receipt must match SHA256
`650927daa8935bbd39cc83f3cb394f47fe196b919738d03652f5e356f822d17c`.
This checks native Linux portability only, not throughput or pipeline cost.
Local amd64 emulation passed the scheduling unit tests but reached its separate
300-second full-trace deadline without a receipt; that attempt was cleaned up
and is inconclusive. Native Linux CI run `36849938167` subsequently passed all
20 cases (3,116 candidates and 6,232 hashes), and the downloaded artifact receipt
matched the expected hash byte-for-byte. See
`evidence/parallel-cpu-verification-linux.json` for the committed source, runtime,
artifact and failed-attempt identities. The first CI attempt failed at receipt
writing due to output-directory permissions; mapping the container user to the
runner owner and preflighting writes fixed that infrastructure issue. Neither CI
run is a matched performance experiment.

The extracted compression gate subsequently passed 174,080 independent native comparisons and compute-sanitizer reported zero errors. This is the extracted harness, not full-solver certification.

The exact frozen baseline/candidate binaries have now passed all 32 sampled range checks on one A10G. Complete output and identities are preserved in `evidence/native-ranges.json`; the receipt SHA256 is `43273178c0d7c2c48882ea11a56581ac4365597f1faf5284cd34ddf3afd59775`. The sampled inventory covers four ranges for each of four stage/layout contexts, for both binaries; it grants no whole-range credit. The host, root disk and temporary infrastructure were independently confirmed removed.

The Python-capable CUDA validation runtime was published by CI run 36745858082 from commit `068a90dee65fb4567df1086261ee6350942558e7`. Its immutable digest and controller identity are in `evidence/native-ranges-summary.json`; signed build provenance and anonymous registry access were verified before allocation. `stage_full.py` generates a small public-artifact handoff using immutable source URLs, the frozen CI archive digest and individual binary hashes. The chunk collector binds complete results before decoding.

Diagnostic native traces now passed independent CPU/full-transaction verification: 20 cases, 3,116 candidates and 6,232 recovery hashes. The CPU receipt is preserved in `evidence/native-trace-cpu.json`; its native input hash binds the retained raw trace. The diagnostic derivative remains distinct from the exact candidate. The trace host, disk and temporary resources were independently confirmed removed.

Matched same-GPU timing is complete; see the adoption decision below. The `timing` mode of `stage_full.py` and `host-full.sh` stages the exact same binaries and immutable runtime with the completed compression, range and CPU-trace receipts. `run_pair.py` checks their frozen hashes before any GPU process, and records those hashes in the timing result. Its existing 24 interleaved samples and 600-second deadline remain unchanged. There is no demonstrated speedup, fresh withdrawal, release enrollment or mainnet-readiness claim. The PR remains a draft.


## Matched timing result and adoption decision

The final bounded A10G experiment completed all 24 interleaved samples with the frozen baseline/candidate and the three hash-bound correctness receipts. Full output is in `evidence/native-timing.json`; its SHA256 is `c96670925fbb9d60294b57689cf8033b864094348c7dfe0acf993073e5adfe58`. Execution controller: `b96752330d6d376a5bb0ba97cb6b2abe37d4e9eb`; solver source remains `aa898b66326706d24e56688eef907ea97bd66f41`.

| Context | Candidate median throughput change |
| --- | ---: |
| Taproot round 1 | -0.108% |
| Taproot round 2 | -0.286% |
| SegWit round 1 | -0.051% |
| SegWit round 2 | -0.364% |

**Do not promote this optimization on these results.** Correctness checks passed, but there is no measured throughput benefit. Three startup-inclusive pairs per context are insufficient to establish that these small negative differences are statistically significant regressions. The first baseline sample includes a visible startup outlier; the table uses the predeclared median calculation, with no samples dropped. Maximum-sample full-range projections remain below the worker limit, but those are estimates, not measured full-range executions. The PR stays draft; no release or production enrollment is authorized by this experiment.
