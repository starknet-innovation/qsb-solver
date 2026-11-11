# PQB candidate assessment

Assessed 11 November 2026. Disposition: **retain for review, HOLD**. Nothing here is published,
enrolled or deployed, and no cloud resource was used.

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
| Contract | [`pqb-ranked-v1`](../../contracts/pqb-ranked-v1.json), `worker/pqb/pqb_ranges.py` |
| Worker | [worker/pqb](../../worker/pqb/README.md): handler, binding, Dockerfile (`aws` target, sm_86 default) |

This is not Yukon benchmark research. The process in `AGENTS.md` was applied to it by analogy.

## Why it could lower cost

Two separate effects, neither measured here.

1. **The scheme.** PQB's reported grind is far smaller than QSB's. That is a property of the
   lock, it needs PQB vaults in qsb-app, and it is the authors' figure.
2. **Exhaustive round sweeps.** Upstream draws round subsets at random, so a round with no
   solution never announces itself and is abandoned at a cut-off. Upstream's own docs say an
   exhaustive sweep would remove that overhead and that their kernel cannot do it. This
   adaptation does: a fixed-order pass proves an empty round after exactly one pass.

   `research/pqb-ranked/tools/cost_model.py` puts pqb's own model and published 4090 rates
   through both policies:

   | rates | random draws with cut-off | exhaustive sweep | |
   |---|---|---|---|
   | pqb card sweep, one RTX 4090 | 12.11 h | 8.31 h | ×0.686 |
   | pqb 16-card fleet mean | 12.88 h | 8.84 h | ×0.686 |

   The first column reproduces upstream's 12.1. **This is a model.** It assumes the ranked walk
   runs at the same trials per second as upstream's random draws. The ranked walk adds a host
   step (listing prefixes and uploading them each batch) and visits prefixes in a different
   order; its rate is unmeasured.

## Evidence

| Evidence | Kind | What it shows |
|---|---|---|
| Upstream trial rates, the 12.1 h figure, a mainnet spend in block 972,743 | author report | Not reproduced or verified here. Rates are for RTX 4090/5090/H100 on vast.ai with CUDA 12.6.3 and `-arch=native`. |
| `tests/test_pqb_ranked_emulation.py` | CPU emulation of the kernel source (`-DQG_EMU`) | For 3 pinning, 3 round-0 and 3 round-1 ranges (first, last and interior of each space, including multi-batch runs with two batches in flight), the complete hit set equals an independent pure-Python enumeration at a 12-bit gate; round ranges are the contiguous pqb subset ranks the grinder reports; out-of-space ranges are refused. |
| same file, DER-shape tests | CPU emulation | `der_shape` agrees with its definition on 2,000 random and 648 constructed digests; with the filter on, the gate-hit count is exact on a small range and every reported hit re-derives with the shape. |
| `research/pqb-ranked/tools/pqb_crosscheck.py`, run locally on 2026-11-11 | CPU emulation against pqb itself | All 302 hits from 8 ranked ranges reproduced by pqb's `gpu.HitChecker` (125 also through `grind.evaluate`), each nonce inside the range `pqb_ranges` states. The committed problems are exactly what pqb derives from the committed packets. Not run by CI. |
| `tests/test_pqb_handler.py` | CPU emulation | Request and problem validation; a small unit completes on each stage; a unit the grinder does not account for, a refused range, a timeout and a binding mismatch are not credited. |
| `tests/test_pqb_contract.py` | arithmetic | Units tile each round's subsets exactly once and the pinning units cover the usable nonces. |
| nvcc 12.8.93 in `nvidia/cuda:12.8.1-devel-ubuntu22.04` for linux/arm64, run locally on 2026-11-11 | compiler observation | The adapted `grind.cu` compiles for `sm_86` and `sm_89` with the lock's flags; its only warnings are three unused-symbol warnings that upstream's file also has. The host code is arm64 and the image was pulled by tag, so these are not the release binaries and their hashes are not recorded. |

Not done: any native GPU execution, any timing, an amd64 image build, the image's offline checks,
a vulnerability scan, a full solve of any stage, any end-to-end spend.

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
- **`--der-filter 1`**: gate hits are counted; only those with the DER shape are reported. This
  is the one change inside a kernel, a few instructions that run after a digest passes the gate.
  Upstream reports every 24-bit gate hit (about 80,000 per pinning unit), which the consumer
  would have to store and re-derive.
- Unknown options are refused. Under emulation `QG_NZ_MAX` is honoured, for tests.
- Compiled with the repository's pinned CUDA 12.8.1 image and a fixed `-arch=sm_86`, not
  upstream's 12.6.3 and `-arch=native`.

Without a ranked flag the search path is upstream's.

## Correctness and coverage limits

- **Exceptional curve cases are not detected.** The kernels assume no point addition meets equal
  or opposite points. A menu denominator of zero would spoil the shared inversion for its whole
  thread (4 z-blocks and all their menu points) with no error, and a sighash ≡ 0 mod n is not
  handled. For hash-derived inputs these are negligible in probability, but `range-complete`
  does not rule them out. The QSB subset worker handles its exceptional cases exactly; this one
  does not.
- **Candidates are necessary-condition hits.** Strict DER, the `SIGHASH_SINGLE` filter, key
  recovery for a verify-form stage, and the policy on hybrid-encoded keys (consensus-valid,
  refused where STRICTENC is enforced) all belong to the consumer.
- **The worker cannot validate a problem's meaning.** It checks shape and gate. Whether the
  preimage is the caller's transaction is the caller's check.
- **Fixed shapes.** Only pqb's `PQB` configuration: 12×2×3 pinning, a 109-slot/8-pick round 0, a
  101-slot/9-pick round 1. Rounds with an extra fixed deletion (`deletions_before`) are
  unsupported upstream and here.
- **Capacity.** 2²⁰ hits per batch and 32 candidates per unit, both fail-closed.
- **Unit sizes and the 3,300 s timeout are provisional.** A pinning unit is 16 `nSequence`
  values (about 1.4 × 10¹² trials); a round unit is 2³⁰ prefixes (about 3 × 10¹² trials for round
  0, 7 × 10¹¹ for round 1, uneven across the space). On upstream's 4090 rates those are minutes;
  on an A10G nobody has measured them. Changing either is a new `searchVersion`.
- **Hardware.** Upstream reports the workload is bound by 32-bit integer throughput and that
  consumer cards beat datacenter cards per dollar (their H100 runs pinning at 0.56× their 4090).
  The A10G rate is unknown, so the per-spend cost on the current AWS Batch fleet is unknown and
  may be well above upstream's vast.ai figure.

## What qsb-app would need

None of this exists yet: PQB vault construction and funding, an independent CPU verifier for
PQB candidates, problem construction and its sighash check, a coordinator that pins, runs round
0 then round 1, and re-pins when a round's whole space is empty, and the same contract vectors
tested on its side. This worker keeps no verifier, wallet or key material.

## Cost and cleanup

No paid hardware, no provider submissions, nothing to clean up. No budget was reserved.

## Next evidence gaps, in order

1. amd64 CI build of `worker/pqb/Dockerfile` and its offline image checks.
2. Native GPU correctness on the public fixtures: the same differential comparisons as the
   emulation tests, on the compiled binary, including a batch-boundary case.
3. Matched timing on one GPU, interleaved: upstream random mode against ranked mode for each
   stage, so the model's equal-rate assumption is replaced by a measurement. On an A10G and, if
   consumer cards are an option, on one of those.
4. A decision on hardware and unit sizes from (3), then a contract freeze.
5. The qsb-app side above, then one complete public-data pipeline run.
