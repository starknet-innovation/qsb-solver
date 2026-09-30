# Exact optimization candidate assessment

Research status as of 30 September 2026. This is an interim assessment, not an
adoption decision or evidence that all optimization opportunities are exhausted.
Production source and release identities remain unchanged.

| Candidate | Evidence | Current disposition |
| --- | --- | --- |
| Table inversion batching | Four complete mixed15 differential checks, independent OpenSSL samples, clean sanitizers, seven alternating timing pairs on one A10G | Kernel time decreased 7.49% at the median, about 0.229 ms/table; construction benefit inconclusive. Keep experimental. |
| CPU combination refill overlap | All 24 matched timing samples and 32 range samples explicitly report GPU enumeration without CPU fill | Not applicable to the observed ranked path. Do not benchmark the fallback path as a substitute. |
| Other pipeline/cache scheduling | No timeline or stage-level profiling in existing receipts; old upstream pipelines have completion, overflow and publication issues | Unprofiled, not disproven. Do not enable by changing a flag. |
| GLV table/decode refinements | Upstream configurations include omission shortcuts; the exact product helper is absent from current worker targets | Requires a different arithmetic/table architecture; no directly applicable isolated refinement or native performance claim. |
| Scalar SHA constant indexing | Native compiler screen; affected function unreachable for ranked workload | Shelved without GPU execution. |

## Evidence and measurement limits

[Table experiment](exact-table-batch/README.md) retains raw timings and sanitizer
reports. Its construction timer includes validation and instrumentation and does
not measure production initialization or solver throughput. One device and seven
pairs do not establish a general hardware result.

The existing [matched timing receipt](generic-sha-vector/evidence/native-timing.json)
contains 24 startup-inclusive samples comparing the earlier SHA vector candidate
against baseline. Every sample logs `Using GPU-enum fast path (no CPU fill, base-linear)`.
The same is true of all 32 [range samples](generic-sha-vector/evidence/native-ranges.json),
which are correctness evidence rather than a matched performance comparison.
These receipts provide no transfer/compute timeline or host/GPU idle-time breakdown.
They cannot establish a general scheduling bottleneck or rule out all overlap gains.

[run_pair.py](generic-sha-vector/run_pair.py) times subprocess launch through
completion. Input fixture preparation precedes that timer, and result parsing
follows it. Host provisioning, image pull and result collection are outside it.

The ranked path in the current
[subset source](../research/optimized-subset/subset/tests/gpu_epochs/tree.cu)
enumerates combinations on the GPU. The CPU-fill fallback is a different path.
Any future scheduling candidate must preserve complete results, error handling,
buffer lifetime and durable publication; submitted work is not durable completion.

The [SHA scalar-index screen](sha-constant-index/README.md) is independent of the
rejected vector-load experiment. Compiler differences are not performance evidence.

No new end-to-end correctness, fresh withdrawal, range credit or speedup claim
follows from this candidate assessment.

## Follow-up host math hypothesis

Production initialization includes the same 252 OpenSSL spot checks as the table
harness. Removing them from a timing denominator would not demonstrate a production
benefit. A second paid run of the unchanged kernel solely for that narrower timing
is not justified by the current evidence.

A distinct experiment is being prepared for host ladder construction: compare
per-point affine export with batched normalization of retained public points.
It must preserve complete records, zero padding, checked failures and independent
point validation. No implementation is integrated into a worker, and no speedup
is established. The proposed OpenSSL batching API is deprecated in OpenSSL 3.0
and has no replacement according to its
[official migration guide](https://docs.openssl.org/3.0/man7/migration_guide/);
API availability and this portability limitation must be recorded before testing.
