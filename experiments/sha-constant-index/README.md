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
