# Isolated SHA-256 rotate-add rounds (audit row 8)

Status: **HOLD, unexecuted**. The variants compiled for sm_86 in CI on 9 November
2026 (result below); no binary has been run on a GPU. Production sources, `worker/optimized/source-lock.json`, binaries, images and
descriptors are unchanged. There is no correctness or performance claim.

## What it is

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
which expires after 14 days.

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

## Next steps

The native run is planned, not authorized, in [A10G-PLAN.md](A10G-PLAN.md).

1. Review the artifact and record the hashes here.
2. Run the existing native component checks on the candidate binary.
3. One matched A10G run against the published image, with interleaved samples. That
   needs a complete test and collection plan and explicit authorization first.
