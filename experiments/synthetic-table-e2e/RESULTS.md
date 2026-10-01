# Fixed public arithmetic: fresh-process throughput

The host-ladder candidate reduces measured end-to-end latency for this synthetic public-scalar-1 table workload on one AWS A10G. It does not measure full solver throughput, pinning, either search round, transaction recovery, or a withdrawal. No promotion to those workflows follows from this result.

Seven alternating baseline/candidate pairs were retained for each fixed workload, with a fresh process and CUDA context for every sample. The physical GPU/driver was already warmed. Both arms used the same original GPU kernel. All six prerequisite sanitizer runs passed (memcheck, racecheck and synccheck for each arm). Every table passed 252 independent OpenSSL samples and the frozen full-table SHA256 check.

| Tables per process | Baseline median time | Candidate median time | Median paired time reduction | Baseline tables/s | Candidate tables/s |
|---|---:|---:|---:|---:|---:|
| 1 | 647.87 ms | 473.21 ms | 26.67% | 1.544 | 2.113 |
| 4 | 1,752.71 ms | 1,047.12 ms | 40.14% | 2.282 | 3.820 |
| 16 | 6,157.63 ms | 3,344.54 ms | 45.66% | 2.598 | 4.784 |

Times include process/loader startup, CUDA initialization, allocation, transfers, arithmetic, independent checks, full-table hashing, durable child JSON report/exit and parent log/receipt validation. Runner journal persistence, cloud setup and result download are excluded. Paired candidate/baseline ratios ranged 0.7241–0.7360, 0.5962–0.6006 and 0.5405–0.5463 respectively. These are observed ranges across seven pairs, not confidence intervals.

## Per-stage results

Median stage totals in milliseconds for the 16-table process:

| Stage | Baseline | Candidate |
|---|---:|---:|
| CUDA context initialization | 144.93 | 140.80 |
| Host output allocation | 32.27 | 32.23 |
| Host ladder arithmetic | 3,403.15 | 590.59 |
| Device allocation | 6.35 | 6.85 |
| Upload and sentinel initialization | 5.38 | 5.42 |
| GPU kernel wall interval | 49.39 | 49.29 |
| Download | 106.66 | 106.77 |
| Independent OpenSSL validation | 1,634.83 | 1,635.85 |
| Per-table cleanup | 4.38 | 4.52 |
| Full-table SHA256 | 668.20 | 667.83 |
| Host output cleanup | 5.92 | 5.69 |
| External residual: loader/report/exit plus uninstrumented work | 96.56 | 97.12 |
| Parent log and receipt validation | 0.48 | 0.48 |

Stage medians need not sum to the median total. CUDA-event kernel measurements (49.19/49.09 ms) are nested within the kernel wall interval and are not added again. The external residual cannot be attributed solely to startup or report I/O. Full 1/4/16-table breakdowns are in `evidence/stage-analysis.json`.

The host arithmetic saving survives startup and validation overhead in this fixed workload. Its increasing amortization across table counts explains the larger measured throughput gain at 16 tables. Actual solver throughput remains unmeasured, and scalar diversity, sustained service behavior, multiple GPUs and cold-machine startup were not tested.

## Reproducibility

`evidence/identity.json` binds source, native compile run, artifact ZIP, binary and immutable runtime. `native-result.json` contains the full ordered sample and sanitizer reports; `validated-result.json` contains independently recomputed summaries and hashes for the collected files. Original transport, terminal and infrastructure receipts remain in the private campaign directory.

Instance termination, root-volume deletion and removal of all temporary schedules, functions, roles, profiles and security groups were independently verified at 2026-10-01 05:12:51 UTC. This run retains a USD5 conservative admission charge; the USD100 campaign now has USD15 charged conservatively and USD85 unreserved. These are budget reservations, not the provider invoice. No replacement or additional run is scheduled.
