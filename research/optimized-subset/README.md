# Optimized subset source — isolated research

This directory preserves the 32 source files from the later OpenSSL-error-checked candidate snapshot, derived from the repaired 1650caf subset candidate. Changes include generic tail SHA schedule caching, bounded exact exceptional-point recovery, checked CUDA host operations and output publication, and checked OpenSSL calls. Original upstream sources and earlier research remain outside this export.

Since 10 November 2026 `subset/GPUHash.h` also carries upstream's SHA-256 rotate-add round macros (`QSB_SHA_LEA`, on by default in the file), taken verbatim from upstream `582a99408761f904f7f92a5d64d9ca0dcc76924a`; no other upstream change after `1650caf` is included. The measured isolated experiment is in [experiments/sha-rotate-add](../../experiments/sha-rotate-add/README.md). That change produces a new subset binary: the published combined releases do not contain it, and their evidence does not cover it.

This is not the original leaderboard submission. Its lineage is used by the separately validated combined release; see [publication and enrollment status](../../docs/README.md). Live deployment is a separate fact. The historical `worker/Dockerfile` builds a different pinned baseline. No binary is shipped here; building these files does not establish the identity or correctness of an earlier measured binary.

For review: the generic ranked path is the enum kernel compiled with `ZLAB_TRIM=0` and `QSB_PAIR_SHARED=0`, together with the exact recovery helpers in `subset/tests/gpu_epochs/tree.cu`. The default short-epoch pair build is a different geometry and refuses ranked work. Specialized paths and arbitrary compiler flag combinations are not certified. More than 64 retained hit records fails the range rather than supporting unbounded output. A deterministic failure must not be credited as completed coverage or blindly retried.

Historical component evidence remains in the qsb-app documentation and does not certify this new repository build. The [public optimized worker build](../../worker/optimized/README.md) now compiles these files with pinned CUDA/base-image identities and recorded flags. Fresh output identities require applicable native validation, evidence review and separate enrollment. The September release explicitly waived a fresh wallet-backed proof; component evidence must still not be presented as end-to-end execution.

See LICENSE for the upstream Apache-2.0 terms. The files include local modifications; no upstream endorsement is implied.
