# Host ladder batching: measured component improvement

The isolated host-ladder candidate reduced warm instrumented public-table construction time by **53.98%** on one A10G host. Keep this as a validated research candidate in draft PR [#8](https://github.com/starknet-innovation/qsb-solver/pull/8); it is not integrated or approved for production. Whole-solver throughput and cold-start performance remain unmeasured.

## Measurement

Seven alternating baseline/candidate pairs used the same GPU and identical original GPU kernel. The baseline constructs affine ladder records individually; the candidate retains owned point snapshots and batches normalization before the unchanged affine exporter.

| Measurement | Result |
|---|---:|
| Median paired candidate/baseline construction ratio | 0.460180 |
| Paired construction reductions | 53.875–55.242% |
| Median paired saving | 176.866 ms |
| Baseline / candidate construction medians | 327.515 / 150.806 ms |
| Baseline / candidate ladder-phase medians | 212.989 / 36.467 ms |
| Unchanged-kernel median paired ratio | 1.001009 |

The first baseline sample was slower. Excluding that pair leaves ratio 0.460245; baseline-first and candidate-first subsets have medians 0.459910 and 0.460309. These are observed samples, not confidence intervals or evidence of repeatability across hosts.

Timing covers public scalar 1, after context warmup. It includes table validation, device allocation, sentinel initialization, CUDA events and cleanup. It excludes CUDA context initialization and caller output-buffer allocation. The result is **warm instrumented construction**, not production startup or solver throughput. GPU kernel timings are diagnostic: its code is identical in both arms.

## Correctness and provenance

Before timing, three public fixtures passed complete equality of 19,200 ladder records and 1,048,576 table records, with 252 direct OpenSSL samples per table per arm. Complete table equality repeats after every retained pair. All three table hashes match the earlier GPU table experiment. Memcheck, racecheck and synccheck passed with clean summaries. Distinct output sentinels detect unwritten records.

Separate native Linux CPU CI passed five fixtures, including padding equality and 90 direct OpenSSL samples per fixture, plus explicit zero and group-order rejection in both implementations. The direct reference uses the same OpenSSL library; it is independent of the recurrence, not an independent cryptographic library. Neither finite fixture coverage nor sanitizers constitute a proof for every scalar.

The candidate uses OpenSSL's public, deprecated `EC_POINTs_make_affine` API, verified in the pinned OpenSSL 3.0.2 runtime. Builds that disable deprecated APIs require separate handling. Existing source notices are retained; no upstream GLV implementation was imported.

- Execution source: [882e336849386577f6fdd966dcfecf27384eff67](https://github.com/starknet-innovation/qsb-solver/commit/882e336849386577f6fdd966dcfecf27384eff67).
- Native GPU compilation: [run 36774856236](https://github.com/starknet-innovation/qsb-solver/actions/runs/36774856236).
- Native CPU evidence: [run 36774072335](https://github.com/starknet-innovation/qsb-solver/actions/runs/36774072335).
- Artifact ID: 11125011733; binary SHA256: `3eba54f48c42f97db941a14c18cd5bf5b454bf36c27f7e0c2c8619bfa016cfab`.
- Immutable runtime and original-kernel identities, all raw public reports, sanitizer logs and evidence hashes: [evidence/summary.json](evidence/summary.json).

Independent review reproduced the ratios, checked evidence hashes, phase accounting and table hashes, and confirmed the measurement limitations. Instance, root volume and all temporary resources were independently confirmed removed at 2026-09-30 21:02:49 UTC. Private operational receipts remain outside Git.

## Other hypotheses and campaign disposition

| Candidate | Evidence and recommendation |
|---|---|
| GPU table inversion batching | Native correctness and sanitizers passed; kernel time fell 7.49% (~0.229 ms/table), but instrumented construction fell only 0.10% with overlapping variation. Keep experimental; no practical construction/throughput benefit established. See [earlier evidence](../exact-table-batch/evidence/summary.json). |
| Host ladder normalization batching | Defensible component benefit above. Retain for further integration review; do not claim whole-solver speedup. |
| CPU refill overlap | All 24 prior timing and 32 range samples used the GPU-enumeration path with no CPU fill. Refilling overlaps a different path; no new paid test justified. Other scheduling ideas are unprofiled. |
| Exact GLV table/decode refinements | Inspected omission modes lose candidates and were rejected. Other exact helpers are not used by the current worker and would require a different architecture; no measured improvement or import. |
| SHA scalar constant indexing | Changed function is unreachable in the measured ranked path; compiler output alone establishes no benefit. Shelved without native execution. The previously rejected PR #7 vector experiment was not repeated. |

The stopping condition of identifying a defensible improvement is met at component scope. Broader throughput optimization remains separate work; the untested hypotheses above are not disproven. No merges, release publication, worker enrollment, production deployment or broadcasts occurred.

The new USD100 campaign used two allocated instances and retains **USD10 conservative admission charges**, leaving USD90 unreserved. This is not an actual AWS invoice. Two explicit capacity rejections were reconciled and cleaned before releasing their reservations. All allocations are cleaned, with no unknown submissions or outstanding reservations. The earlier USD20 campaign remains separate. Capacity and older validation automations remain paused.
