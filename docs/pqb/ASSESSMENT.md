# PQB candidate assessment

Reviewed 12 November 2026. **Publication blocked:** the [Critical findings review](2026-11-12-critical-review.md) reproduced compromised-certificate acceptance in the qualified image's outbound S3 TLS client. A locally tested source fix needs a new qualified artifact.

 Disposition: **retain for review, HOLD**. No PQB release is published,
enrolled or deployed. The component measurement, largest native units and 13 correctness cases
passed their stated criteria. A [complete public synthetic transport solve](2026-11-11-public-transport-solve.md)
then verified all three stages in 91 minutes 40 seconds at $20.73 estimated compute, including
its builder. Exact artifact identities, limits and independently verified cleanup are retained
in that report; the earlier receipts keep their original identities.
The [final image assessment and qsb-app handoff](2026-11-12-final-image-qualification.md)
qualify the parser-fixed image under its actual signed source/digest: all three largest native
units, 13 small cases before each unit and the independent consumer replay passed. The
checksummed HOLD descriptor and publication provenance are prepared; registry publication,
enrollment and deployment remain separate. Earlier receipts retain their original identities.

## What this is

[PQB](https://github.com/fireblocks-labs/pqb) (Fireblocks, MIT) is a different quantum-resistant
lock from QSB. A spend solves three GPU puzzles: one pinning stage over `nSequence`/`nLockTime`
and two FindAndDelete rounds over a shared 109-entry table. Its authors report about 12.1 RTX
4090-hours per spend. The existing `ranked-v2` worker cannot solve these puzzles and is not
changed by this work.

This candidate is a second, separate worker: PQB's own CUDA grinder, adapted so that a request
names a range and the worker either covers all of it or fails.

| | |
|---|---|
| Upstream | `https://github.com/fireblocks-labs/pqb` at `eccdd09772edf14ab37fc63992b0626ad7ff2221` (committed 2026-11-10; the repository holds this one commit, so there is no comparison base) |
| Imported | `grinder/{grind.cu,common.cuh,ptx_field.cuh,README.md}`, `LICENSE`, `THIRD_PARTY_NOTICES.md`, byte for byte, in [vendor/pqb](../../vendor/pqb) with `provenance.json` |
| Not imported | the Python CLI, the TypeScript library, the explorer, the whitepaper |
| Adapted | [research/pqb-ranked/grind.cu](../../research/pqb-ranked/grind.cu), bound by `source-lock.json` |
| Contract | [`pqb-ranked-v2`](../../contracts/pqb-ranked-v2.json), `worker/pqb/pqb_ranges.py` |
| Worker | [worker/pqb](../../worker/pqb/README.md): handler, binding, Dockerfile (`aws` target, sm_86 default) |

This is not Yukon benchmark research. The process in `AGENTS.md` was applied to it by analogy.

## Why it could lower cost

Two separate effects; comparative whole-spend savings remain modelled. Component rates and
one public three-stage solve have separate measured evidence.

1. **The scheme.** PQB's reported grind is far smaller than QSB's. That is a property of the
   lock, it needs PQB vaults in qsb-app, and it is the authors' figure.
2. **Exhaustive round sweeps.** Upstream draws round subsets at random, so a round with no
   solution never announces itself and is abandoned at a cut-off. Upstream's own docs say an
   exhaustive sweep would remove that overhead and that their kernel cannot do it. This
   adaptation instead provides a bounded fixed-order pass and an explicit completion report.
   Native accounting and checking emitted hits still do not prove complete coverage.

   `research/pqb-ranked/tools/cost_model.py` puts pqb's own model and published 4090 rates
   through both policies:

   | rates | random draws with cut-off | exhaustive sweep | |
   |---|---|---|---|
   | pqb card sweep, one RTX 4090 | 12.11 h | 8.31 h | ×0.686 |
   | pqb 16-card fleet mean | 12.88 h | 8.84 h | ×0.686 |

   The first column reproduces upstream's 12.1. **This is a model** of expected hours. Its one
   assumption about this code, that the ranked walk runs at upstream's trials per second, was
   measured on an A10G on 11 November: ranked ran at 1.00 to 1.01 times upstream's steady rate
   on all three stages ([record](2026-11-11-a10g-measurement.md)).

## Evidence

| Evidence | Kind | What it shows |
|---|---|---|
| Upstream trial rates, the 12.1 h figure, a mainnet spend in block 972,743 | author report | Not reproduced or verified here. Rates are for RTX 4090/5090/H100 on vast.ai with CUDA 12.6.3 and `-arch=native`. |
| `tests/test_pqb_ranked_emulation.py` | CPU emulation of the kernel source (`-DQG_EMU`) | For 3 pinning, 3 round-0 and 3 round-1 ranges (first, last and interior of each space, including multi-batch runs with two batches in flight), the complete hit set equals an independent pure-Python enumeration at a 12-bit gate; round ranges are the contiguous pqb subset ranks the grinder reports; out-of-space ranges are refused. |
| same file, DER-shape tests | CPU emulation | `der_shape` agrees with its definition on 2,000 random and 648 constructed digests; with the filter on, the gate-hit count is exact on a small range and every reported hit re-derives with the shape. |
| same file, exceptional-case tests | CPU emulation | With every thread forced through the exact host path, hit sets equal the reference on all three stages and gate counts match. With a menu point planted equal to one z-block's sighash point (a doubling, and its negative giving infinity), the grinder reports exactly that thread as exceptional and the hit set still equals the reference. |
| `research/pqb-ranked/tools/pqb_crosscheck.py`, run locally on 2026-11-11 | CPU emulation against pqb itself | All 302 hits from 8 ranked ranges reproduced by pqb's `gpu.HitChecker` (125 also through `grind.evaluate`), each nonce inside the range `pqb_ranges` states. The committed problems are exactly what pqb derives from the committed packets. Not run by CI. |
| `tests/test_pqb_handler.py` | CPU emulation | Request and problem validation; a small unit completes on each stage; a unit the grinder does not account for, a refused range, a timeout and a binding mismatch are not credited. |
| `tests/test_pqb_contract.py` | arithmetic | Units tile each round's subsets exactly once and the pinning units cover the usable nonces. |
| [Native A10G run, 11 November](2026-11-11-a10g-measurement.md) | native GPU execution and matched timing | On one `g5.xlarge`: all 11 correctness cases returned exactly the reference's hit sets, including multi-batch ranges, the DER-shape filter and a planted exceptional point. Ranked steady rate 1.004 to 1.014 times upstream's random search, three alternating samples per stage. A10G rates 2.49 / 2.73 / 2.01 G trials/s. |
| nvcc 12.8.93 in `nvidia/cuda:12.8.1-devel-ubuntu22.04` for linux/arm64, run locally on 2026-11-11 | compiler observation | The adapted `grind.cu` compiles for `sm_86` and `sm_89` with the lock's flags; its only warnings are two unused-symbol warnings. The host code is arm64 and the image was pulled by tag, so these are not the release binaries and their hashes are not recorded. |

**Which artifact each receipt covers.** The original matched component run used binary
`3f816a00…` from `266f4a0`. Later host-side bounds, option/slot validation and compile-guard fixes
produced a different binary. The [full-unit campaign](2026-11-11-full-unit-validation.md) ran
binary `0e811c59…` from `0a25ec4`: all three largest units passed, each after 11 native
independent-reference cases. Round1 emitted one production-gate/DER-shaped candidate that
re-derived correctly on CPU. This supplies filter-emission evidence beyond the original
component run's empty filtered case; it is not a full solve.

Later review at `ca9ca95` added duplicate-output/event rejection, failure-artifact retention and
two positive pinning filter cases. Its CI binary is byte-identical (`0e811c59…`), with unchanged
CUDA source and flags. A separate [correctness-only native session](2026-11-11-correctness-consumer-validation.md)
at `a24c0dd` subsequently passed all 13 cases, including both positive pinning cases with their
recorded one-bit test gate. The full-unit receipts retain their actual `0a25ec4` handler/harness
identity. See the applicability review rather than treating old receipts as a new binding attestation.

The full-unit harness's optional local evidence directory retains problem, native log and
hits without changing the request schema or the default temporary-directory path. See the
[plan](FULL-UNIT.md) and [retained results](2026-11-11-full-unit-validation.md).

The actual PQB CI image now has a retained Grype scan: zero fixable critical matches and
20 unfixed critical package matches. Its policy passed; this is not a vulnerability-free image.
The pinned qsb-app PR #150 consumer passed 15 focused CPU tests, 350 cross-repository range
comparisons, strict worker parsing of its three problem fixtures, and independent re-derivation
of the retained native round1 candidate. See the [supplemental report](2026-11-11-correctness-consumer-validation.md).

The [public transport campaign](2026-11-11-public-transport-solve.md) subsequently completed
one three-stage solve through the consumer's actual Batch/S3 and CPU modules. All 118 completed
units and 16 emitted hits also passed the pinned upstream checker with native libsecp256k1;
three hits solve the full predicates. Its temporary private image, source and runtime have
their own receipts. Served Step Functions orchestration, wallet/consensus/miner execution,
another GPU model and broad completeness certification remain open. No native re-pinning was
needed in this case. No public PQB release was enrolled.

The emulation build runs the same source on a CPU. It is evidence about the algorithm as
written. It is not evidence about nvcc's code generation, device execution or the PTX field
arithmetic in `ptx_field.cuh`, which the emulation build does not use.

## Deviations from upstream

- **Ranked mode** (`--pin-seq …`, `--prefix-start …`): no random draws. Pinning walks stated
  `nSequence` values and every `nLockTime` in order. Rounds take their (t−1)-prefixes from a
  host-built list in lexicographic order, each with all its completions, in place of prefixes
  drawn on the device.
- **Fail closed** in ranked mode: a hit-buffer overflow, or a z-block count different from the
  range's size, is a non-zero exit instead of a warning.
- **`--der-filter 1`**: gate hits are counted; only those with the DER shape are reported: a
  few instructions that run after a digest passes the gate.
  Upstream reports every 24-bit gate hit (about 70,000 per pinning unit), which the consumer
  would have to store and re-derive.
- **Exceptional-case detection** in `ec_comb` (two zero tests per thread, a marker `ec_menu`
  skips) and an exact host path, `exact_block`. The second change inside a kernel; it adds
  checks and does not alter the arithmetic. No cost was measurable on an A10G.
- Unknown options are refused. Under emulation `QG_NZ_MAX` is honoured, for tests.
- Compiled with the repository's pinned CUDA 12.8.1 image and a fixed `-arch=sm_86`, not
  upstream's 12.6.3 and `-arch=native`.

- `QG_FUSE=0` is refused at compile time: the unfused hashing kernel would hash the stale point
  slots of a thread the exceptional path skipped.
- Range options must be unsigned decimals, and need the option that turns ranked mode on.
- Round problems whose table slots are closer than the kernel supports are refused. The kernel
  handles three deletion boundaries per 64-byte block, which needs 22 bytes between boundaries;
  upstream's host check allows 12. PQB's own table has exactly 22.

Without a ranked flag the search is still upstream's random draws, but the binary is not
upstream's: exceptional threads are detected and recomputed there too, and unknown or malformed
options are refused.

## Correctness and coverage limits

- **Exceptional curve cases are detected and recomputed, not assumed away.** The device
  formulas are incomplete: they cannot add equal or opposite points or represent infinity.
  Every such case puts a zero factor into one of the thread's two batched inversions, so the
  kernel tests both products, reports a thread that has one, emits nothing for it, and the host
  recomputes its z-blocks with complete affine formulas. Upstream would silently spoil every
  point of that thread. It ran natively on an A10G for a planted case. What remains unproven:
  one branch (a sighash ≡ 0 mod n, where the sighash point itself is infinity) cannot be planted
  through a hash, so it is covered by the complete addition it shares with the tested branches,
  not by its own test. More than 1,024 exceptional threads in a batch fails the range.
- **Candidates are necessary-condition hits.** Strict DER, the `SIGHASH_SINGLE` filter, key
  recovery for a verify-form stage, and the policy on hybrid-encoded keys (consensus-valid,
  refused where STRICTENC is enforced) all belong to the consumer.
- **The worker cannot validate a problem's meaning.** It checks shape and gate. Whether the
  preimage is the caller's transaction is the caller's check.
- **Fixed shapes.** Only pqb's `PQB` configuration: 12×2×3 pinning, a 109-slot/8-pick round 0, a
  101-slot/9-pick round 1. Rounds with an extra fixed deletion (`deletions_before`) are
  unsupported upstream and here.
- **Capacity.** 2²⁰ hits per batch and 32 candidates per unit, both fail-closed.
- **Unit sizes are fitted to one host's rates.** `pqb-ranked-v2` has pinning units of 14
  `nSequence` values, round-0 units of 3 × 2²⁷ prefixes and round-1 units of 2³⁰ prefixes. At the
  measured A10G rates the largest unit of each stage takes 486 s, 502 s and 486 s (round units
  average about 380 s and are uneven across the space). That is sized for a 900-second job limit
  with room for start-up and a slower host; pqb saw hosts of one model differ by up to 30 %,
  which would bring the largest unit to about 650 s. The native largest units subsequently
  completed in **490.9 / 504.7 / 487.3 s** through the bound handler. This is not a host-wide
  guarantee or an application job certification. `pqb-ranked-v1` (16 values, 2³⁰ prefixes for both rounds) was provisional, never
  published or enrolled, and had round-0 units of up to 21 minutes. The worker stops a unit at
  840 s and reports it `interrupted`, so a slow unit ends with a result instead of being killed
  by a 900-second job limit. Changing a unit size is a new `searchVersion`.
- **Hardware.** Upstream reports the workload is bound by 32-bit integer throughput and that
  consumer cards beat datacenter cards per dollar (their H100 runs pinning at 0.56× their 4090).
  The A10G ran at 0.42 of pqb's 4090 rates; see the AWS cost section.

## AWS cost per spend

Expected hours come from pqb's model with exhaustive sweeps (a model, not a measurement). Speeds
are measured where the table says so. Prices are on-demand from the AWS Pricing API or
third-party snapshots read on 2026-11-11; spot prices move and capacity is not guaranteed. None
of this is a bill.

| Instance (GPU) | Speed vs RTX 4090 | Price used | Per spend, exhaustive sweep | Per spend, random draws |
|---|---|---|---|---|
| g5.xlarge (A10G), component-measured configuration | 0.42, **measured here** on one host | $1.123/h on-demand, eu-west-1 | about $22 | about $32 |
| g5.xlarge (A10G) | same | $1.277/h on-demand, eu-west-2 | about $25 | about $37 |
| g5.xlarge (A10G) | same | $0.454/h spot snapshot, eu-west-2 | about $9 | about $13 |
| g6e.xlarge (L40S) | 0.85, measured by pqb on one vast.ai host | $1.861/h on-demand, us-east-1 | about $18 | about $26 |
| g6e.xlarge (L40S) | same | $0.87–1.36/h spot snapshot, us-east-1 | $8–13 | $12–19 |
| g6.xlarge (L4) | **unmeasured**; assumed 0.15–0.26 | $1.022/h on-demand, eu-west-2 | $33–57 | $48–82 |
| vast.ai RTX 4090, pqb's reference | 1 | $0.37 per 4090-hour (pqb) | about $3 | about $4.5 |

- The A10G figure is 19.6 A10G-hours per spend with the measured ranked rates, 28.8 with
  upstream's random draws. Before the measurement this row assumed 0.20–0.33 of a 4090 and
  $32–53; the card is faster than assumed.
- `g6e` is not offered in eu-west-1 or eu-west-2 in this account; `g6` is offered in eu-west-2.
- On the day, EC2 refused seven `g5.xlarge` launches across five zones for capacity before one
  succeeded. On-demand A10G availability is a practical constraint, not just a price.
- Not included: per-job start-up, units replayed after an interruption, units still running when
  another finds the solution, storage and data transfer.

These are historical projections from the component rates and upstream's cost model, including
its estimated benefit from exhaustive sweeps. They are not measured comparative whole-spend
costs. The later public transport solve cost $20.43 estimated Batch compute plus $0.29 for its
builder, including allocated startup/cancellation/collection time. One synthetic result does
not establish a production cost distribution or another GPU's cost.

## What qsb-app would need

Consumer adoption requires PQB vault/problem construction, an independent CPU verifier for
candidates and transaction meaning, a coordinator that pins, runs round0 then round1 and
re-pins when a whole round is empty, plus matching contract vectors tested in both repositories.
These are proposed in [qsb-app PR #150](https://github.com/starknet-innovation/qsb-app/pull/150).
The supplemental CPU assessment pins its tested commit and matching vectors. The later public
solve used consumer `276f2ae`, whose tree equals that original `81c060d` tree, and exercised
actual Batch/S3/CPU modules with development orchestration. Its report records the remaining
served-application and release gaps. The worker keeps no verifier, wallet or key material.

## Cost and cleanup

Historical component session, on 11 November 2026 ([record](2026-11-11-a10g-measurement.md)):

- **Provider submissions:** eight `g5.xlarge` launch requests, one per session. EC2 refused seven
  for capacity, so they allocated nothing. The eighth, in eu-west-1b, ran for about 6.7 minutes.
- **Cost:** about **$0.13** estimated (6.7 minutes at $1.123/h, plus negligible storage, S3 and
  API calls). This is an estimate from the list price and the instance's launch and termination
  times. It is not provider billing, which was not read. The user's cap was $5.
- **Cleanup:** verified for every session by an independent check: no instance, volume, security
  group, schedule, function, role, instance profile or staging bucket remains, and nothing is
  running in eu-west-1 or eu-west-2. It was irregular for the session that launched: the
  orchestrating job was stopped after the instance had terminated and before the controller's
  cleanup; the committed controller then removed part of the temporary resources and failed on a
  network timeout, and the remaining three roles and security group were deleted by name.

The separately authorized [full-unit campaign](2026-11-11-full-unit-validation.md) then launched
four instances sequentially: an earlier pinning build and the three units of the pinned final
binary. Estimated compute was **$0.90**, including that earlier run and startup/collection,
not provider billing; storage, IPv4 and other charges are outside that compute estimate.
One setup failed before any GPU submission. All instances, recorded volumes and temporary
resources were independently verified removed. No reservation or submission remains open.
The old $5 cap did not authorize this campaign or any future run.

The later correctness-only campaign used one further fresh instance under the current chat's
hardware authorization. Estimated compute was **$0.0649** (208 seconds at $1.123/h), excluding
storage/IPv4/other charges and distinct from billing. The native archive was collected and
hash-verified; instance, recorded volume and all temporary resources were independently verified
removed. Its $2 reservation was released. See the supplemental report and receipts.

The complete public transport campaign used 51 Batch instance lifetimes, at most 16 workers
concurrently, plus one separate bounded builder. Estimated compute was $20.73 including all
allocated startup, cancelled and collection time; provider billing was not read and other
service charges are excluded. All 52 recorded volumes were independently verified gone,
instances terminated/absent and temporary resources removed. The $200 solve and $2 builder
reservations are released. Its original controller reservations remain 128,700 GPU-seconds;
cancelled jobs were never refunded inside the solve. See the full report and evidence package.

## Next evidence gaps, in order

1. Qualify a final image incorporating the reviewed whole-log completion parser. The
   [completed release/adoption review](release-review-2026-11-12/README.md) binds the measured
   image separately from newer source and prepares a HOLD descriptor and consumer handoff.
   The public solve and its cleanup are complete; do not restart them.
2. Prepare the dedicated PQB provenance/publication path and final release assets for separate
   publication and enrollment decisions. Served coordinator,
   wallet/consensus/miner validation and release enrollment remain separate from this public
   transport assessment. The actual zero-sighash branch still lacks its own planted test.
3. Broader hardware/host and workload sampling before relying on a latency/cost distribution.
   One solve and fresh EC2 instance IDs do not certify another GPU model or establish a matched
   whole-pipeline speedup. Preserve completed campaigns rather than restarting them.
