# Source review of audit rows 8 and 9, 9 November 2026

Status: **static review only**. Nothing was imported, compiled or executed on a GPU.
Both candidates stay on HOLD. This follows the
[upstream audit](2026-11-09-yukon-audit.md) and uses the same identities: upstream head
`582a99408761f904f7f92a5d64d9ca0dcc76924a`, subset base `1650caf`.

The question for each switch: does it reach the generic path this repository builds
(`ZLAB_TRIM=0`, `ZLAB_K2S=0`, `QSB_PAIR_SHARED=0`, `QSB_SPEC_FINISH=0`,
`ZLAB_DUAL_EPOCH_SHA=0`), is it exact, and does it depend on the sm_89 carrier.

## Result

| Switch | Reaches the generic path | Exact | Carrier-dependent | Disposition |
| --- | --- | --- | --- | --- |
| `QSB_SHA_LEA` round macros in `GPUHash.h` | Yes. `_SHA256Transform` uses `SHA256_RND`; the local path calls it for the window and outer hashes | Yes, a bit-level identity (checked numerically) | No. It is source-level; the benefit depends on what `ptxas` emits for sm_86 | **Retain.** Next evidence is an sm_86 compile and a disassembly check |
| `QSB_LEA_PARTS`, `sha_gate_fma.cuh` | No. Included only under `QSB_PAIR_SHARED` | Not reviewed | — | Not applicable |
| `QSB_OUTER_LITK` | No. Code is under `QSB_PAIR_SHARED && ZLAB_DUAL_EPOCH_SHA && ZLAB_K2S3M` | Not reviewed | — | Not applicable |
| `QSB_CONST_CALLEE` | No. Code is under `ZLAB_DUAL_EPOCH_SHA`; the default exists only when `QSB_S3` is on | Not reviewed | — | Not applicable |
| `QSB_TREE_WAVE_TOP`, `QSB_TREE_LANEMASK`, `QSB_TREE_ROW128` | Structurally yes: they change `qsb_block_inverse_tree`, which the generic path calls. Off by default without `QSB_S3`; guards pass when forced on | Only with the exact tree multiply. Upstream head defaults to a short-carry multiply (see below) | No | **Retain, conditional.** Needs four prerequisites listed below |
| `QSB_DIVSTEP_4LANE` | Same as above, through the limb root inverse in `inverse_limbs.cuh` | Author-stated; the decision value is read only on the four lanes that still compute it. Not independently proven | No | Retain with the tree set |
| `QSB_YOFF_S` | No. Guarded to `QSB_S3` (the GLV12 table) and `QSB_Y_PAIR` | — | — | Moved to audit row 11 |

## What the local build relies on for exactness

These were read from `research/optimized-subset/subset` and matter for any port.

- **Fixed-base chain:** `_FixedBaseSignedXYZZStream` runs `qsb_replay_chain_trial`, whose
  field operations set a flag when a result's top limb is near an edge
  (`qsb_replay_guard`), and then reruns `qsb_replay_chain_exact` if the flag is set.
- **Inversion tree:** `tree_inverse.cuh` uses `qsb_field_mul_raw`, documented as
  preserving the final reduction carry, with leaves returned as exact residues.
- **Exceptional points:** a vanished denominator is handed to exact host recovery
  (record bit 29) and overflow fails the range. This is a local adaptation and is
  absent upstream.
- `GPUHash.h`, `tree_inverse.cuh`, `zinv32.cuh`, `hm43_warp_inverse.cuh` and
  `window_schedule_shared.cuh` are byte-identical to upstream `1650caf`, so upstream's
  diffs for those files apply to an unchanged base. `tree.cu` is locally adapted and
  does not.

## Findings

1. **Upstream head rejects our flag set as-is.** Preprocessing head with our five flags
   stops at `QSB_YNEG_FOLD is written for the ZLAB_K2S3M front`. Head has not been
   built in the generic shape by its authors; "set a switch to 0 to get the previous
   code" is their claim, not a tested configuration.
2. **A guard-clean generic configuration exists.** With the 15-chunk table it needs
   `QSB_S3=0 QSB_YOFF_S=0 QSB_Y_PAIR=0 QSB_FOLD_REG=0`. Keeping the GLV table needs
   only `QSB_YNEG_FOLD=0`, but that is the row 11 architecture. Passing `#error` guards
   is not compiling, and not correctness.
3. **In that configuration head silently adds lossy arithmetic.** `QSB_SHORT_CARRY3`
   defaults to 1 and selects `qsb_field_mul_tree`, which calls the short-carry
   `qsb_filter_mul` and discards its flag. The tree products then carry the "drops a
   rare carry" class that upstream relies on its host gate to reject. The local tree
   does not have that class. `QSB_SHORT_CARRY4`, `QSB_SHORT_CARRY6`, `QSB_LOSS_FINK32`,
   `QSB_LOSS_SQRLEAN` and `QSB_LOSS_ROOTLAZY` are also on. One wrong tree product
   corrupts every inverse in its block of 256 lanes, so this is not a per-candidate risk.
4. **The row 9 switches are inert unless forced.** Their defaults sit inside the
   `#if QSB_S3` block of `tree.cu`. With `QSB_S3=0` they are undefined and evaluate to 0,
   so a naive rebuild of head in the generic shape gets none of them and no error.
5. **Host and benchmark features stay on** in every configuration tried:
   `QSB_CARRIER`, `QSB_CPU_GRIND`, `QSB_HOST_PRODUCERS`, `QSB_SLOT_PIPELINE`.
6. **The root inverse changed underneath row 9.** The wave top requires
   `QSB_ROOT_UNIFORM_WARP` and `QSB_INVERSE_LIMBS` (new `inverse_limbs.cuh`, and 369
   changed lines in `zinv32.cuh`). It has a bounded batch count with a fallback, per its
   comments. `QSB_ISO_ROOT_SCALE` and `QSB_ISO_FUSED_ROOT_SCALE` default to 1 and scale
   the root inverse by a problem-isomorphism constant; they belong to a pipeline we do
   not use and were not reviewed.

## Prerequisites before any row 9 port

1. Tree multiply stays `qsb_field_mul_raw` (`QSB_SHORT_CARRY3=0`, or do not import
   `filter_tail_sc.cuh`'s selector).
2. `QSB_LOSS_ROOTLAZY=0`, `QSB_ISO_ROOT_SCALE=0`, `QSB_ISO_FUSED_ROOT_SCALE=0`.
3. A review of the `zinv32.cuh` and `inverse_limbs.cuh` changes on their own, since an
   inverse error is block-wide. The existing `tree_audit.cu` and `scalar_audit.cu`
   harnesses are the natural check, extended to the new root.
4. The local exceptional-point and capacity handling in `tree.cu` is kept unchanged.

Scope if both are taken: `GPUHash.h` (181 changed lines) for row 8; four files and
about 900 changed lines for row 9, plus local defaults and guards in `tree.cu`.

## What ran

| Check | Result | What it shows |
| --- | --- | --- |
| Byte comparison of five local files against upstream `1650caf` | Identical | The upstream diffs start from our bytes |
| Enclosing-conditional trace of each switch (`ppstack.py`) | See table above | Which build shapes contain the code |
| `clang -E` of head `subset.cu` with stub CUDA and OpenSSL headers, `__CUDA_ARCH__=860` (`guardwalk.py`) | Our flags alone: 1 `#error`. With the four extra flags: none, also with the tree switches forced on and the lossy, host and ISO switches off | `#error` guards only |
| `clang -E -dM` macro dump for three configurations | Values quoted in the findings | Effective defaults |
| Numeric check of the two Sigma identities (200,005 words each) and the wave-top inverse formula (2,000 blocks of 16) (`algebra_check.py`) | Pass | The algebra in the upstream comments, not the CUDA code |

Not run: `nvcc`, any CUDA test harness, any GPU. No timing exists for either candidate
on any hardware in the generic shape, so there is no speedup claim. An earlier local
SHA experiment (`origin/research/generic-sha-vector`) recorded no promotion benefit on
an A10G; row 8 is a different change, but that result is the reason to check the sm_86
disassembly before paying for a run.

The scripts are in [2026-11-09-yukon-review-tools](2026-11-09-yukon-review-tools/). They
take the path to a clone of upstream at the head commit; `guardwalk.py` also takes a
directory of empty stub headers (`cuda_runtime.h`, `cpuid.h`, `immintrin.h`,
`sys/syscall.h` and the four `openssl/` headers).

## Next evidence gap

1. **Row 8, no GPU:** apply upstream's `GPUHash.h` diff on a branch, build the subset
   binary for sm_86 in CI, and compare `cuobjdump -sass` instruction counts for the SHA
   rounds against the current binary. If `ptxas` does not shorten the round on sm_86,
   stop there.
2. **Row 8, if it does:** the existing native component checks, then one matched A10G
   run against v0.3.0. That needs a complete plan and explicit authorization.
3. **Row 9:** the `zinv32.cuh` and `inverse_limbs.cuh` review in prerequisite 3 first.
   It is the larger and riskier change, and its gain on the generic path is unknown.

Cost: none. No cloud resource was requested.
