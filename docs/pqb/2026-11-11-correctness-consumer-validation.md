# PQB native correctness and consumer checks

Status: **13 native correctness cases passed; candidate remains HOLD**. This supplements the
[completed largest-unit campaign](2026-11-11-full-unit-validation.md). It neither repeats that
timing campaign nor changes its source attestations. All inputs are public synthetic fixtures.

## Exact artifact and native result

The clean, pushed source was `a24c0ddb84a129db556069a3964e8d8d3ce55201`. Successful push
CI run [43088388333](https://github.com/starknet-innovation/qsb-solver/actions/runs/43088388333)
produced binary artifact `13886724270`, ZIP SHA-256
`e4dbdbc750d108aa2e46a32675a8c14f922d3d2a435b998ac685cd86c24ad1ce`.
The ranked binary remains byte-identical to the completed full-unit campaign:
`0e811c59de2d36f66142a6f65393c55a64e0e37c7eb40df4251f86b713ef3d82`.
Its retained build receipt records nvcc 12.8.93, `-O3 -std=c++17 -arch=sm_86` and the actual
locked sources. Source lock and imported provenance hashes were checked against actual bytes.

The new explicit `correctness` host profile ran all 13 committed cases on NVIDIA A10G,
driver 580.126.09, using the same immutable CUDA runtime as the full-unit campaign:
`ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48`.
The bundle's binaries and runner were mounted read-only into an isolated, networkless
container. The two newer positive pinning cases now have native evidence:

| Case | z-blocks | Gate hits | Emitted hits | Exact reference set |
|---|---:|---:|---:|---|
| pin-der-filter-emits (compressed) | 16 | 586 | 1 | matched |
| pin-der-filter-emits-uncompressed | 16 | 555 | 1 | matched |

Both cases deliberately use a **one-bit test gate**, with the DER-shape filter enabled.
They exercise positive filter emission; they are not production 24-bit successes or strict-DER
solutions. The other 11 cases also passed, including partition boundaries, multiple batches
and the planted exceptional point. The runner compares complete hit sets and exact work/gate
accounting. The runner's elapsed time was 3.899 seconds; `timing` is explicitly `null`.
No performance samples or full units were repeated. Successful per-invocation raw hit files
are temporary; the retained result records the exact-set verdict and native range counters,
bound to the committed expected hit lists. Failed invocations retain raw diagnostics.

## Durable setup failures

`host-pqb-measure.sh` now installs its exit trap immediately after creating its one-shot result
directory. Image-pull, deadline-margin and GPU-query failures retain the original exit code,
logs and hash-addressed public archive, with container cleanup attempted on every exit.
Five host simulations cover these paths and both execution profiles. The original timing
profile keeps its bounds; correctness-only uses a 120-second runner deadline, 180-second outer
timeout and a 240-second remaining-time floor after pull. The independently armed 25-minute
host deadline is never reset. Local validation completed 157 tests: 156 passed, one Linux-only
test skipped on macOS; the Linux CI test job passed.

## Consumer compatibility

The tested consumer is [qsb-app PR #150](https://github.com/starknet-innovation/qsb-app/pull/150)
at `81c060dfbeddc64f1a16ef50a6195d68831e61b1`, installed with its lockfile using
`npm ci --ignore-scripts`. Its `pqb-ranked-v2` contract is byte-identical to the worker's:
file SHA-256 `eaae48fd867e9783c247e6bb9f33ba24011298d354d0a7d93e5f65904ce8ffb1`.
This is a file hash, distinct from the earlier report's canonical Python contract hash.

The consumer's actual TypeScript range implementation matched the worker on all 70 round0
units, all 174 round1 units and 106 sampled/boundary pinning checks (105 distinct units):
**350 comparisons**.
The worker's strict parser accepted all three consumer-generated public problem fixtures.
The consumer's 15 focused PQB tests passed, including reference problem/digest fixtures,
protocol checks and SDK assembly. Positive coordinator transitions mock CPU verdicts and
provider execution; these tests do not certify a real positive pipeline.

The consumer explicitly documents JavaScript's normalization of JSON `1.0` to integer `1`,
which it serializes as `1` on the worker wire. Python rejects the raw float token `1.0`.
The valid ranges and serialized integer requests agree; do not describe the lexical invalid
vector as identical behavior in both parsers.

The app's `HitChecker` also re-derived the retained production-gate round1 candidate through
its canonical transaction path, plus both new positive test-filter hit lines at their recorded
one-bit gate. All three remain **not strict DER and not full solutions**. The native round1
candidate and its original receipt retain their earlier source identity.

Repeat the CPU compatibility assessment against an explicitly pinned clean consumer checkout:

```sh
python3 scripts/check_pqb_consumer.py /absolute/qsb-app-checkout \
  81c060dfbeddc64f1a16ef50a6195d68831e61b1 /absolute/new-results
```

The command requires both source checkouts clean and creates a fresh output directory. It
uses installed locked consumer dependencies; it installs nothing and accesses no service.

## PQB image scan

CI now scans the actual PQB candidate image, separately from the combined historical image.
Grype 0.119.0 with database built 2026-11-11 06:21:32 UTC found **zero fixable critical
matches** and **20 unfixed critical package matches**, with severity taken from the worse
matched/related record. The repository's policy passed; this is not a vulnerability-free image.
The full scanner report and policy summary are retained. The Docker-local image ID was
`sha256:3593aa3fe5115d52e8b9f189862e549c819cc285922fa1bc150de69a1c845edd`.
It has no registry repo digest: it was neither published nor enrolled. Mutable apt/pip inputs
mean another build requires its own identity and scan review.

## Cost, cleanup and remaining work

The user authorized paid hardware as needed in this chat. A fresh $2 reservation preceded one
`g5.xlarge` submission in Ireland, with no retries, uncertainty or deadline extension. Estimated compute was **$0.0649** from 208 seconds between provider launch and shutdown
transition at $1.123/h. Independent read-back confirmed the instance terminated, its recorded
volume gone and every temporary role/profile/security group/schedule/function/staging bucket
removed; both regions have zero active benchmark instances. The reservation is released.
See the [complete evidence package](evidence/correctness-consumer-2026-11-11/manifest.json).
Provider billing was not read; compute estimates exclude storage, IPv4 and other charges.

The next evidence gap is a complete public-data solve through the consumer's real transport,
durable output and independent verification. The largest-unit receipts, reduced-gate filter
tests, CPU consumer checks and local image scan do not establish that end-to-end result,
whole-spend latency/cost, consensus execution or another GPU model. Publication, immutable
release descriptor enrollment and deployment remain separate actions. The candidate stays HOLD.
