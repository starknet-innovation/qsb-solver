# Isolated generic SHA schedule vector loading

This patch changes only generic cached-tail schedule loads, preserving eight SHA rounds and their order. Production sources, source locks and release identities are unchanged. `prepare.py` verifies the baseline source hash, applies the isolated patch in a temporary directory, then extracts both actual functions into a native CUDA differential harness.

Host extracted-function gate: 170,000 comparisons, clang address/undefined sanitizers, passed. Native gate compares both CUDA functions against a separate CPU round loop, including every intermediate block, zero/all-one/random schedules and 1,024 random states. Expected 174,080 comparisons. Compile with CUDA12.8 and `-O3 -arch=sm_86 -std=c++17`, run normally and under compute-sanitizer memcheck. Retain compiler flags, binary hash and outputs.

This is not full-solver certification or a performance result. Follow with full-transaction differentials, all tail alignments, and interleaved same-GPU complete-solver timing before adoption. Two uint4 expressions do not guarantee faster machine code; inspect emitted SASS and register usage. No release publication or activation is implied.

## 30 September native attempt

A single g5.xlarge launch in eu-west-1c returned explicit `InsufficientInstanceCapacity`. No instance was allocated and no native gate ran. Independent post-check confirmed zero instances for the request token and removal of its security group, cleanup schedule/function, roles and instance profile. Native correctness and performance remain pending; host results above are unchanged. The experiment controller/gate commit was `5292e651b58957918abaded5235a343105a75f4f`. Retry requires a fresh execution state and another capacity/price/watchdog preflight.

London 2a and 2b also returned explicit capacity rejection; all temporary resources were independently removed. Local execution-image preflight found that the historical audit image contains prebuilt tests but no nvcc. The host gate now pins the CUDA development image directly. Local x86 emulation crashes nvcc with exit139, so the dedicated Linux CI compilation gate records compiler output, binary hash and SASS without GPU allocation or registry publication. It does not execute the kernel or establish speedup.

Native Linux CI run 36692760138 at bea21976f0411b1eba19289c02a53fa2f2a54788 compiled the extracted gate successfully with CUDA12.8.93, sm86, 45 registers and no stack/spills. Binary SHA256: 621ad5bf76de6dca99f0bb19a08e2315de62878d0d03110c2e4bbbc9bec6fcf6. SASS contains two LDG instructions of width128. These are combined differential-kernel statistics, not standalone candidate occupancy or performance. Logs/hashes are under evidence/. The CI now also builds an isolated full baseline/candidate solver pair from verified source inventory for subsequent matched tests; those outputs are not enrolled releases.
