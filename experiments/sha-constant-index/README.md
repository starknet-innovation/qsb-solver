# Scalar constant SHA schedule induction — unexecuted

This isolated experiment starts from the repaired generic baseline tree SHA256
`71e4b01469b2d2327c32bc62d4b20d1a6276c20c994cf6c3e8a082e9abac7cdb`.
It does not include PR7's rejected vector-load patch. It replaces the nested
block/round indexing in `qsb_compress_constant_rolled` with a scalar offset that
advances across exactly 256 schedule words. Each 64-word boundary still has its
own eight-word feed-forward addition. The constant array is flattened to avoid
pointer arithmetic crossing C++ subarray boundaries. No predicates, arithmetic
cuts, range mapping, or production source locks are changed.

This is an independently written indexing change informed by the frozen Yukon
review's induction idea; no upstream GLV or arithmetic source is imported.

Build on native Linux amd64, from repository root:

```
docker build -f experiments/sha-constant-index/Dockerfile -t sha-constant-index .
```

The image's `/results` contains `compression-gate`, baseline/candidate extracted
CUDA, PTX, cubin and SASS, plus a hash-bound build receipt. Building does not run
the gate. Root CI may copy `/results` from a created container and upload it.

Before allocating a GPU, compare the standalone `compression` entry's SASS
instructions and control-flow (disregarding addresses, compiler metadata and
symbol names). The wrappers are otherwise identical. If instruction sequences
are identical, reject the candidate without native spend. Different SASS is
only an eligibility signal, never performance evidence. Full solver compilation
and path applicability still need review before a performance claim.

The CUDA differential harness compares both extracted functions against a
separate CPU round-loop oracle. It uses 1,024 arbitrary/boundary initial states
and ten 256-word schedules (zero, all ones, increasing words and seeded random).
Every comparison includes all four blocks and their feed-forward additions:
10,240 output comparisons. Native execution and compute-sanitizer are pending.
This is not whole-solver correctness evidence or a cryptographic proof.

The source transformation emits an experimental full tree for review, not an
executable full-solver build path. If later adopting it, update all conditional
header consumers of the original two-dimensional symbol as well; the optional
paired path uses two-dimensional indexing. Do not enroll the transformed tree
without this integration and exact source inventory verification.


## Screening result, 30 September

Shelved for the current ranked worker; no GPU spend. Native compile CI36766252057 (source7a53f82bf1fbba6bbf43b8018ea7a0554f95d8ea) succeeded and all downloaded artifact hashes matched build.json. Both extracted kernels list184instructions with padding; excluding NOPs, baseline169 versus candidate170. Candidate adds two IADD3 and removes one IMAD.MOV; highest referenced general register rises fromR35 toR37. These are static observations, not throughput or occupancy measurements.

More decisively, the locked solver prevents epoch_mode when ranked_work is true (tree.cu2607,2633). fast_inc starts at0 and is configured for this fixed-four-block function only inside epoch_mode (2699–2753). Therefore the bounded rank_start/rank_count worker path never reaches this changed function. Existing ranked performance fixtures cannot measure it. This candidate is not disproven for another workload, but lacks relevance or a concrete codegen benefit for the authorized optimization target. Native correctness and performance remain unexecuted.
