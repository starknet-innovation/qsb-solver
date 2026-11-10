# Candidate preparation: SHA-256 rotate-add rounds, 10 November 2026

Status: **HOLD, source prepared, nothing published**. No tag exists, no image was
pushed, no descriptor was generated and nothing was enrolled or deployed. The
published releases `combined-aws-sm86-v0.3.0` and `v0.2.0` are unchanged and remain
the images available for rollback.

## What changed

| Item | Value |
| --- | --- |
| Branch | `candidate/sha-rotate-add` |
| Source change | `research/optimized-subset/subset/GPUHash.h` only |
| Origin | Upstream `candidates/subset/GPUHash.h`, `1650caf53a32b0ea16aae9e490ebbf5a8686d632` to `582a99408761f904f7f92a5d64d9ca0dcc76924a`, taken verbatim |
| File SHA-256, before | `c8415e1ddc839e078421a1ee347a9db5036f84714b03edb700aa2e635e05fedd` |
| File SHA-256, after | `ac7c11110b5ccf205eb2ee007e0163439540e58dba80d21904f86ec29ec1c807` (byte-identical to upstream's file at the head commit) |
| Source lock | `worker/optimized/source-lock.json` updated for that one file; flags unchanged |
| Build flags | Unchanged. `QSB_SHA_LEA` is on by the file's own default; no new compiler flag is set |
| Pinning | Untouched |
| Contract | `ranked-v2` unchanged; no partition change, so no new `searchVersion` |
| Notices | `LICENSES.md` records the import; the file's GPL notices and upstream attribution are retained |

The change rewrites the SHA-256 round macros as an exact bit-level identity. The
review that selected it and ruled out the rest of upstream's subset changes is in
[the rows 8 and 9 review](../research/2026-11-09-yukon-rows-8-9-review.md).

## Evidence that exists, and what it covers

All of it is for the **isolated experiment binaries**, built from this same source
and flags but by the experiment's build recipe
([experiments/sha-rotate-add](../../experiments/sha-rotate-add/README.md)):

- sm_86 compile comparison: `kernel_digest` 36,752 to 34,496 instructions.
- Native ranges on an A10G: 32 of 32 complete, same counts as the baseline.
- CPU differential: 3,116 candidates and 6,232 recovered-key hashes matched qsb-app's
  CPU reference.
- Matched timing on one A10G: round 1 +3.0% and +3.1%, round 2 unchanged within noise.

**None of it attests a combined image.** The release recipe compiles the subset at a
different path without the verbose assembler flag, so its binary hash will differ
from the experiment's candidate (`bba9c4af12d6…`), exactly as the published subset
binary differs from the experiment's baseline. The experiment shows the source change
is sound and worth building; it is not a receipt for the image.

## Build check on this branch

CI run 42777354221 rebuilt the experiment variants from the committed source, with
the baseline produced by reversing the patch.

- **Device code is identical** to the measured binaries: the SASS hashes equal the
  frozen ones (`1e13e1493970…` baseline, `78c18c758b14…` candidate).
- **The file hashes are not.** Baseline and candidate each differ from the frozen
  binaries by one byte, in a compiler temporary name (`tmpxft_…`) that embeds a
  process counter. Moving the patch step from the candidate to the baseline shifted
  that counter. The control variant, whose position in the build did not change, kept
  its hash.

So a binary hash identifies one build, not the source, and two builds of the same
source can differ. Compare disassembly when the question is whether device code
changed, and keep binding evidence to the exact binary hash that ran.

## Gates before any descriptor

Each is a separate step. The first publishes and the third and fourth cost money, so
each needs the owner's explicit go-ahead.

1. **Merge or freeze the source commit,** then push a `candidate-sm86-YYYYMMDD-N` tag.
   That workflow compiles both stages, scans, **publishes** an attested image and a
   HOLD prerelease with the actual binary hashes. It emits no app descriptor.
2. **Verify the image:** provenance with `gh attestation verify`, the source commit,
   the contract hash and the installed binding. Check that the pinning binary is
   unchanged from v0.3.0, and compare the new subset binary's disassembly with the
   experiment candidate's (`78c18c758b14…`) as an applicability check.
3. **Native component checks** on that exact image on an A10G, against qsb-app's CPU
   reference, as for v0.3.0. The runners' pinned binary identities must be updated to
   the new hashes first.
4. **Matched A10G performance** against the v0.3.0 binaries, both rounds and both
   layouts, interleaved. A new measurement is required: unlike v0.3.0, the subset
   binary is not byte-identical to its predecessor.
5. **Descriptor** through the [combined release path](COMBINED-RELEASE.md), then
   enrollment in qsb-app as a separate, reviewed change. No app default changes
   automatically.

## Expected benefit and limits

About 3% higher subset round 1 throughput on an A10G, which projects to roughly 2% of
subset GPU time per layout. That is a projection from bounded component samples on one
GPU. It is not whole-withdrawal cost, complete-range coverage or an on-chain fee, and
it may differ for the image binary.

The import postdates the redistribution approval of 25 September 2026 and is not
covered by it. Publishing a compiled binary containing it needs legal review before
reliance.

## What ran for this preparation

Local unit tests and the repository CI on the branch, which compiles the combined
sm_86 candidate without publishing it. No GPU, no cloud resource and no cost.
