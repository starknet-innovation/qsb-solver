# Yukon upstream audit and candidate assessment, 9 November 2026

Status: **assessment only**. No source was imported, built or executed. Every
candidate below is on HOLD. Production source, binaries, image digests and
descriptors are unchanged. This is not an adoption decision, and it is not
evidence that any upstream change is correct, complete or faster on an A10G.

## Identity

| Item | Value |
| --- | --- |
| Repository | <https://github.com/Layr-Labs/quantum-safe-bitcoin-challenge> |
| Audit date | 9 November 2026 |
| Upstream head | `582a99408761f904f7f92a5d64d9ca0dcc76924a` (5 October 2026; the challenge is closed) |
| Pinning comparison base | `2791ed0588f5014ccd688d48ba5502df2879f2f1` (18 September), the commit in `vendor/challenge/provenance.json` |
| Subset comparison base | `1650caf` (19 September), the lineage named in `research/optimized-subset/README.md` |
| Method | Full clone and `git diff` of complete trees. No GitHub comparison API was used, so no file-list cap or tree truncation applies. The head tree has 132 files. |
| Machine-readable inventory | [2026-11-09-yukon-upstream-inventory.json](2026-11-09-yukon-upstream-inventory.json): tree hashes, file adds/changes/deletes and every new build switch name per track |

Checks that ran:

- Every `candidates/pinning` file at `2791ed0` is byte-identical to its copy under
  `vendor/challenge/`.
- Outside the two candidate directories, only `benchmark.json` changed since `2791ed0`
  (the minimum score improvement was restored to 100 bips). The harness, problems and
  spec are unchanged.

Checks that did not run:

- No line-by-line review of the upstream device or host code.
- No byte comparison of `research/optimized-subset` against `1650caf`. That tree is a
  local adaptation and is expected to differ; its lock is `worker/optimized/source-lock.json`.
- No build, CPU test, compiler observation or GPU execution of any upstream file.

## What changed upstream

| Track | Commits since base | Diff | Build switches (base → head) |
| --- | --- | --- | --- |
| Pinning | 27 | 40 files, +26,288 / −1,044 | 36 → 385 |
| Subset | 16 | 37 files, +30,857 / −1,741 | 36 → 448 |

Leaderboard scores on the benchmark RTX 4090 (organizer results, read from
<https://www.yukon.org/qsb> on the audit date; "verified candidates/s" is estimated
from verified hits, see `spec/SCORING.md`):

| Track | At our base | At head | Change | Head vs Yukon baseline |
| --- | --- | --- | --- | --- |
| Pinning | 724.6M (18 Sept, 11:42 CEST) | 1,036.5M | +43% | 7.09× |
| Subset | 569.9M (19 Sept, 23:38 CEST) | 753.6M | +32% | 12.16× |

The base scores are matched to commits by timestamp, not by a recorded submission ID.

Yukon's own cost estimate ($59 per transaction) uses a simulated fleet of 100 RTX 3090s.
Its stated same-GPU gains there are 4.01× for pinning and 5.16× for subset, against
7.09× and 12.16× on the 4090. It applies the subset gain to both rounds "until
confirmed" and leaves $25 unallocated. That is an organizer estimate for different
hardware and a different workload boundary. It is not a measurement of this repository's
pipeline, and it is not an on-chain fee.

## Why the score does not transfer directly

These are properties of the upstream head, read from its source comments, build files
and submission note.

1. **Precompiled sm_89 kernel image.** Both tracks embed a base64 cubin
   (`qsb_carrier_sm89.h`, built by `build_carrier.sh` with `-arch=sm_89`). `QsbCarrier.h`
   turns it off when the device is not sm_89 and falls back to the JIT image. The A10G
   is sm_86, so the measured head binary is not the binary an A10G would run. Tuning
   notes refer to register counts, blocks per SM and SM partitions of the 4090.
2. **CPU co-grinding is on by default** (`QSB_CPU_GRIND 1`, `QSB_COGRIND 1`;
   `cpu_cogrind*.h`, `CpuGrindSubset.h`, with AVX2, AVX-512 IFMA and SHA-NI paths).
   Hits found on host cores count toward the score. That is not GPU throughput and
   depends on the benchmark host's CPU. 114 of the 762 new switches are host-CPU by name.
3. **Declared lossy shortcuts, backed by a host gate.** Upstream comments state these
   lose hits rather than produce wrong ones:
   - `QSB_HIGH15_NOFB 1` (both tracks): drops the GLV split's exact-rounding fallback;
     "a wrong one only loses its hit".
   - `QSB_LOSS_FINK32`, `QSB_LOSS_SQRLEAN`, `QSB_LOSS_ROOTLAZY` (subset, on in the head
     package): "Loss only", with a stated wrong class of about 2^-23 per site.
   - `QSB_C31 1` (pinning): a 2^-31 fold that "needs HOST_GATE".

   The benchmark scores verified hits, so a small miss rate is nearly free there.
   Under `ranked-v2` a missed candidate inside a range reported complete is a
   correctness failure. Exact checking of emitted hits does not cover it.
4. **Benchmark-shape specialisation.** Upstream `ZLAB_TRIM` now defaults to 1 and
   compiles only Yukon's ranked short-epoch shape; other shapes exit with an error.
   Our build uses `ZLAB_TRIM=0`, `QSB_PAIR_SHARED=0` and the GPU-enumeration path.
   "Ranked" upstream means the Yukon benchmark problem, not our `ranked-v2` contract.
   Pinning is built for a fixed `QSB_ZEROS_N=24`, and `QSB_ISO_XR` relies on a
   property of the problem that has not been checked against our requests.
5. **Run-time adaptive switches.** `QSB_GATE_FMA_RT` and `QSB_QMIX_RT` change code
   form after 120 s based on observed rate decay. They are tuned to a 20-minute
   benchmark run, not to a bounded range job, and make timing depend on thermal state.
6. **Draw markers and noise.** `REDRAW.txt` and `QSB_DRAW_TAG`-style defines exist to
   resubmit an unchanged package. The spec gives the score noise as about 0.7%
   (pinning) and 1.0% (subset); most late records gain 1–2%.

## Candidate assessment

Evidence labels: **O** organizer result (4090, benchmark shape), **A** author report
(submission note or source comment), **N** our native A10G measurement. None of the
upstream candidates has CPU-test, compiler or native evidence from this repository.

| # | Candidate | Stage | State here | Evidence | Disposition | Reason |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Pinning tree at `2791ed0` | pinning | Imported; host-repaired, device code unchanged | O; N (26 Sept: parity with `aws-v0.1.0`) | Already present | Shipped in v0.2.0 and v0.3.0 |
| 2 | Subset lineage at `1650caf`, generic path | round 1, round 2 | Locally adapted | N (26 Sept: round 1 +31–32%, round 2 +1.6–1.7%) | Already present | Shipped in v0.2.0 and v0.3.0 |
| 3 | sm_89 carrier images | both | Absent | O, A | Incompatible | Wrong architecture for A10G; an sm_86 rebuild is a new binary with no evidence |
| 4 | CPU co-grinders and host producers | both | Absent | O, A | Incompatible | Host-CPU work, not GPU cost; changes what the worker claims to have searched |
| 5 | Lossy shortcuts (`HIGH15_NOFB`, `LOSS_*`, `C31`) | both | Absent | A | Rejected for complete-range use | Author-declared hit loss; conflicts with `ranked-v2` completeness. Retain only with the switch off or an exactness proof |
| 6 | Run-time adaptive switches (`*_RT`) | subset | Absent | A | Incompatible as shipped | Tuned to a 20-minute run; fixed form could be reviewed separately |
| 7 | Draw markers | both | Absent | — | Rejected | No runtime effect |
| 8 | Subset SHA rotate-add rounds (`QSB_SHA_LEA`, `sha_gate_fma.cuh`) | round 1, round 2 | Absent | O, A ("exact") | Retain for review | Reviewed: the `GPUHash.h` round macros reach the generic path and are an exact identity. The gate, outer and callee parts are pair-path only. Measured on 10 November in `experiments/sha-rotate-add`: native correctness passed on an A10G, round 1 about +3%, round 2 unchanged |
| 9 | Subset inversion-tree and table layout (`TREE_ROW128`, `TREE_LANEMASK`, `DIVSTEP_4LANE`, `YOFF_S`, `inverse_limbs.cuh`) | round 1, round 2 | Absent | O, A | Retain for review, conditional | Reviewed: the tree switches reach the generic path but are exact only with the exact tree multiply, which upstream head replaces by default. `YOFF_S` needs the GLV table and moves to row 11 |
| 10 | Subset point-add and pair-sum rewrites (`ZZ3_LATE`, `YP_MAC`, `YP_DC`, `FOLD_REG`, `FMUL_LEAN`, `EC_PSI_ZZ`, `y_pair_sc.cuh`, `point_add_f8_zz3.cuh`) | round 1, round 2 | Absent | O, A | Awaiting evidence | Field arithmetic with dropped normalisations. Each needs an exactness argument before any paid run; several sit next to the `LOSS_*` family |
| 11 | Subset GLV scalar split (`GLVScalar.cuh`, `Q_MIX`) | round 1, round 2 | Absent | O, A | Awaiting evidence | A different table and decode architecture, and the home of `HIGH15_NOFB`. An earlier assessment found no isolated refinement that applies to the current worker |
| 12 | Pinning device changes since `2791ed0` (ASICBoost-style shared tail schedule, fused roots, `sha_pinsha.cuh`, `WarpInverse.cuh`, `*_mac.cuh`) | pinning | Absent | O, A | Awaiting evidence, low priority | Pinning is about 105–115 s of a projected 730–745 s of GPU time per layout. Entangled with the carrier, `C31` and `ISO_XR` |
| 13 | Subset host verification gate (`QSB_HOST_VERIFY`, `qsb_host_verify.h`) | both | Absent | A | Retain for review | An exact OpenSSL publication gate is compatible in principle. It does not replace qsb-app's CPU verifier, and it is what makes upstream's lossy switches safe for a hit-rate score only |

Of the 762 new switch names (counted per track, so a name in both tracks counts
twice), 610 are unclassified by the name heuristic in the
inventory. Unclassified means unreviewed, not safe.

### Prior local results that bear on these candidates

Read from the heads of `origin/research/generic-sha-vector` (`7d22686`),
`origin/research/exact-table-batch` (`f0e3398`) and
`origin/research/parallel-public-verification` (`b98680a`). They are not on `main`.

- **Generic SHA vector load:** native correctness passed; matched timing was recorded
  "without a promotion benefit". A new SHA candidate (row 8) is a different change, but
  must say why it would behave differently on the A10G.
- **Table inversion batching:** kernel time −7.49% at the median on one A10G over seven
  pairs; construction benefit inconclusive. Kept experimental. Relevant to row 9.
- **CPU combination refill overlap:** not applicable, because the ranked path enumerates
  on the GPU. This also bounds the value of upstream host-producer work (row 4).
- **GLV table and decode refinements:** judged to need a different architecture
  (row 11).
- **Scalar SHA constant indexing:** shelved without GPU execution; the function was
  unreachable for the ranked workload.

Rows 8 and 9 have a [source review](2026-11-09-yukon-rows-8-9-review.md).

## Where the cost is

From the [26 September A10G results](../promotion/2026-09-26-a10g-performance.md),
projected full-range times for the published image are about 400 s for subset round 1,
230 s for round 2 and 105–115 s for pinning. Those are linear projections from bounded
samples, not measured full ranges, and not a whole-withdrawal cost. On that basis
subset is about 85% of projected GPU time, so rows 8–10 are the candidates worth
reviewing first.

## Licensing notes

Upstream is Apache-2.0. `candidates/pinning/COPYING` is GPL-3.0 and was already
present at the base. Both tracks now add `COPYING-secp256k1` (MIT, Pieter Wuille),
which indicates code derived from libsecp256k1. Any import must carry that notice and
be recorded in `LICENSES.md`. Redistribution approval recorded on 25 September covers
what was reviewed then, not new imports. This needs legal review before reliance.

## Cost, cleanup and next evidence gap

- **Cost:** none. No cloud resource was requested or launched, so there is nothing to
  clean up or reconcile.
- **Next gap:** the source review of rows 8 and 9 is done; see its next steps. The
  first is an sm_86 CI build of the row 8 SHA change with a disassembly comparison,
  which needs no GPU.
- **After that:** the existing native component checks, then
  one matched A10G run against v0.3.0 with interleaved samples. The paid run needs a
  complete test and collection plan first and explicit authorization.
- **Not planned:** any change to `searchVersion`. Adopting the short-epoch geometry
  would require one and is out of scope for this assessment.
