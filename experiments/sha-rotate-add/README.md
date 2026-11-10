# Isolated SHA-256 rotate-add rounds (audit row 8)

Status: **HOLD**. The candidate compiled for sm_86 on 9 November 2026 and passed
native correctness checks on an A10G on 10 November, with a 3% round 1 gain (results
below). It is not in any image and nothing is released. Production sources, `worker/optimized/source-lock.json`, binaries, images and
descriptors are unchanged. There is no correctness or performance claim.

## What it is

On the `candidate/sha-rotate-add` branch the patch is applied to the committed subset
source; see [the candidate record](../../docs/promotion/2026-11-10-rotate-add-candidate.md).
There the build below reverses the patch to rebuild the baseline. The description
that follows is how the experiment ran.

`sha-rotate-add.patch` is upstream's change to `candidates/subset/GPUHash.h` between
`1650caf53a32b0ea16aae9e490ebbf5a8686d632` and
`582a99408761f904f7f92a5d64d9ca0dcc76924a` of
<https://github.com/Layr-Labs/quantum-safe-bitcoin-challenge>, with only the file path
rewritten. It is applied to a temporary copy of `research/optimized-subset`; the
committed file is not modified. `experiment-lock.json` binds the patch, the baseline
file and the patched result by SHA-256. The patched file is byte-identical to
upstream's at the head commit.

The patch rewrites the SHA-256 round macros (`S2Round`, and `S2RoundO` inside
`SHA256_RND`) so each Sigma is one rotation of a three-way XOR. Upstream reports that
on sm_89 the assembler then folds each outer rotation and its add into one `LEA.HI`,
saving one issue slot per round. Why this row was kept, and what else in row 8 was
ruled out, is in the [source review](../../docs/research/2026-11-09-yukon-rows-8-9-review.md).

The upstream attribution inside the patch names its authors. `GPUHash.h` carries GPL
notices that the patch leaves in place; upstream is Apache-2.0 at the top level.
`LICENSES.md` does not yet mention this patch and must before any adoption. That
point needs legal review before reliance.

## The question this answers

Does `ptxas` produce a shorter SHA round for **sm_86** (the A10G)? The only evidence so
far is the author's, on sm_89. An earlier local SHA experiment
(`origin/research/generic-sha-vector`) passed correctness and showed no promotion
benefit on an A10G, so this one stops at the compiler unless the code shape changes.

## What the workflow builds

`.github/workflows/sha-rotate-add-compile.yml` runs the offline tests, then
`build_variants.py` inside the pinned CUDA 12.8.1 development image. It verifies the
production source lock and the experiment lock, then compiles four binaries with the
locked production flags, `-arch=sm_86` and `-Xptxas=-v`:

| Variant | Source | Extra flag | Purpose |
| --- | --- | --- | --- |
| `baseline` | committed | — | the current code shape |
| `control` | patched | `-DQSB_SHA_LEA=0` | shows the patch is inert when switched off |
| `candidate` | patched | — | upstream defaults (`QSB_LEA_ORD=536`) |
| `candidate-ord0` | patched | `-DQSB_LEA_ORD=0` | the plain operand order; upstream's default order was tuned on sm_89 |

No binary is executed. The artifact holds each binary, its `ptxas` log and SASS
listing, `build.json` (hashes, flags, compiler) and `sass-comparison.json`
(per-function instruction counts and opcode differences against the baseline).

## Reading the result

- `controlMatchesBaseline` should be true. If it is not, the patch changes code even
  when off, and that has to be understood first.
- For `candidate` and `candidate-ord0`, look at the instruction delta of
  `kernel_digest` and at `leaInstructions`. Fewer instructions with new `LEA`
  opcodes is the shape upstream describes. No change, or more instructions, means
  the candidate stops here.
- Instruction counts are not timings. A shorter round is a reason to measure, not a
  result.

## What ran locally

`tests/test_sha_rotate_add.py` (8 tests, no compiler):

- the lock matches the patch, the production baseline hash and the patched result;
- the patch touches only `subset/GPUHash.h`;
- the patch's own PTX text for both `QSB_LEA_RLA` forms and both `QSB_LEA_RLM_D` forms,
  run through a three-opcode interpreter, equals the reference round on 22,000 inputs
  and reproduces `hashlib.sha256` on 224 single-block messages. The C parts of the
  macros are transcribed by hand in the test, so this checks the algebra and operand
  binding, not the compiled code;
- the SASS comparator on a synthetic listing.

Also checked by hand: the patched tree preprocesses with the production flags without
an `#error`.

Not run: the Docker build (the CUDA compiler does not run under emulation on the
development machine), any CUDA harness, any GPU.

## Compile result, 9 November 2026

Native Linux CI run
[42687871125](https://github.com/starknet-innovation/qsb-solver/actions/runs/42687871125)
at source commit `4d403e1`, CUDA 12.8.93, sm_86. No binary was executed. The retained
receipts are in [evidence/](evidence/): `build.json`, `sass-comparison.json` and
`artifact.sha256`, which lists the SHA-256 of every file in the downloaded artifact.
The binaries, SASS listings and `ptxas` logs themselves are in the CI artifact only,
which expires after 14 days. Run 42690353515 at `8ba7d03` rebuilt everything, reproduced
the baseline and candidate binaries and SASS byte for byte, and added the diagnostic
trace binary; `evidence/` now holds that run's receipts and `frozen-build.json`.

| Variant | Binary SHA-256 | Instructions, all kernels | Instructions, `kernel_digest` | `LEA*` opcodes vs baseline |
| --- | --- | --- | --- | --- |
| `baseline` | `8664f41f3deeeb91…` | 48,112 | 36,752 | — |
| `control` | `50abec355a44bff7…` | 48,112 | 36,752 | 0 |
| `candidate` | `bba9c4af12d65de4…` | 45,560 (−5.3%) | 34,496 (−6.1%) | +2,366 |
| `candidate-ord0` | `b4e3cef8bf6e1294…` | 45,560 (−5.3%) | 34,496 (−6.1%) | +2,366 |

- **The patch is inert when off.** The control's SASS is identical to the baseline's
  (`1e13e1493970…`). Its binary hash differs, which is consistent with host-side
  differences such as the build path, and was not investigated further.
- **sm_86 does fold the rotations.** `kernel_digest` gains 1,726 `LEA.HI` and drops
  2,256 instructions. The three small SHA kernels shrink too.
- **Operand order does not matter for size here.** Both candidates have the same
  counts, with slightly different SASS.
- **No resource change.** `kernel_digest` stays at 128 registers and 272 bytes of
  stack in every variant.
- **Cross-check.** The baseline binary and SASS hashes equal the ones recorded by the
  earlier `generic-sha-vector` experiment for the same source and flags.

Limits: these are static counts over every path compiled into the kernel, not only
the instructions the ranked workload executes. They are not a timing, and the
candidate binary has not run, so nothing here shows it is correct or faster on an
A10G. The earlier SHA experiment changed seven instructions and showed no benefit;
this one changes about 6% of the kernel, which is the reason to measure it.

## Native result, 10 November 2026

Three one-shot `g5.xlarge` sessions in Ireland (NVIDIA A10G, driver 595.91.07), run
under the plan in [A10G-PLAN.md](A10G-PLAN.md) with the owner's authorization. Public
synthetic inputs only. Receipts are in [evidence/](evidence/): `native-ranges.json`,
`native-trace-cpu.json`, `native-timing.json` and `native-sessions.json`.

**Correctness: passed.**

- Ranges: 32 of 32 samples complete. Baseline and candidate reported the same
  exhausted counts and no hits on four ranges in each of the four contexts.
- CPU differential: the candidate's recovered-key hashes matched qsb-app's CPU
  reference for all 3,116 candidates (6,232 hashes) across the 20 trace fixtures. The
  trace came from the diagnostic build; the unmodified candidate ran the same ranges.

**Timing: a small gain that meets the rule fixed in advance.** Startup-inclusive wall
seconds for 2^29 ranks, four interleaved pairs per context, one GPU:

| Context | Baseline samples | Candidate samples | Baseline median | Candidate median | Throughput gain |
| --- | --- | --- | --- | --- | --- |
| taproot-round1 | 14.28, 12.60, 12.56, 12.52 | 12.43, 12.19, 12.22, 12.20 | 12.580 | 12.210 | +3.03% |
| taproot-round2 | 7.15, 7.14, 7.13, 7.15 | 7.11, 7.10, 7.14, 7.11 | 7.143 | 7.106 | +0.52% |
| wpkh-round1 | 12.48, 12.47, 12.44, 12.48 | 12.12, 12.08, 12.09, 12.11 | 12.475 | 12.097 | +3.13% |
| wpkh-round2 | 7.10, 7.08, 7.07, 7.06 | 7.02, 7.03, 7.03, 7.03 | 7.075 | 7.029 | +0.66% |

- Round 1 gains 3.0% and 3.1%; round 2 gains 0.5% and 0.7%. The rule was at least 2%
  in round 1 for both layouts and round 2 no more than 0.5% slower, so the outcome is
  **worth a release-candidate review**.
- The round 2 gains are about the size of the sample spread (0.1% to 0.6%), so treat
  round 2 as unchanged rather than improved.
- The first baseline sample of the first context was a cold start (14.28 s against
  about 12.5 s). Medians are not affected, and the gain is the same with first
  samples dropped.
- Scaled linearly to full ranges, the medians save about 13 s of roughly 631 s of
  subset GPU time for one layout and 14 s of 626 s for the other, close to 2%.
  That is a projection from bounded samples, not a measured full range.

Limits: one GPU, one session, four pairs. This is component timing for the subset
stage. It is not whole-withdrawal time or cost, not complete-range coverage, and not
an on-chain fee. Pinning is untouched. The candidate is not in any image.

Cost and cleanup: USD 15 was reserved against the authorized cap; about USD 0.40 of
compute was used (21.4 instance-minutes at USD 1.123 per hour, excluding storage and
address charges). Provider billing has not been read. All three instances and their
volumes are gone, and a final check of both regions found no temporary resource left.
One extra scope failed at arming before any launch and created no instance.

## Next steps

The authorized run is complete and its budget is used; any further paid run needs a
new authorization. If the owner wants the gain:

1. Decide whether about 2% of projected subset GPU time justifies a new release
   identity and its evidence.
2. If yes, apply the patch to `research/optimized-subset`, regenerate the source lock,
   add the provenance to `LICENSES.md` (needs legal review before reliance), and build
   a `candidate-sm86-*` image.
3. That image is a new binary: it needs its own native component checks and a matched
   run before any descriptor. This experiment's receipts do not transfer to it.
