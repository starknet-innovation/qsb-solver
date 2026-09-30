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
