# Isolated generic SHA schedule vector loading

This patch changes only generic cached-tail schedule loads, preserving eight SHA rounds and their order. Production sources, source locks and release identities are unchanged. `prepare.py` verifies the baseline source hash, applies the isolated patch in a temporary directory, then extracts both actual functions into a native CUDA differential harness.

Host extracted-function gate: 170,000 comparisons, clang address/undefined sanitizers, passed. Native gate compares both CUDA functions against a separate CPU round loop, including every intermediate block, zero/all-one/random schedules and 1,024 random states. Expected 174,080 comparisons. Compile with CUDA12.8 and `-O3 -arch=sm_86 -std=c++17`, run normally and under compute-sanitizer memcheck. Retain compiler flags, binary hash and outputs.

This is not full-solver certification or a performance result. Follow with full-transaction differentials, all tail alignments, and interleaved same-GPU complete-solver timing before adoption. Two uint4 expressions do not guarantee faster machine code; inspect emitted SASS and register usage. No release publication or activation is implied.
