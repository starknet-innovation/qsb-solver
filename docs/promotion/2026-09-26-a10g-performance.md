# Matched A10G performance: optimized candidate vs released `aws-v0.1.0`, 26 September 2026

Status: **executed and passed**. This closes release gate (b), the matched A10G performance check against `aws-v0.1.0` covering both subset rounds and pinning.

## What ran

- **Source:** `a510ac573e260e7b95f7472c5458fe2fdc9791de`. Bundle `882a189090b032d2599ca784b0062be04bbc04683f1c8e61fcfe5a98f9978079`, built by `scripts/prepare_performance_bundle.py` from that commit and the released baselines.
- **Candidate:** the frozen image `e22afc72…`. Subset `673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15`, pinning `cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62`.
- **Baseline:** the binaries from the released `aws-v0.1.0` image `9e62d3c4…`. Subset `672cf6689fd6e0c71d992ab2a6df2687ac9b2b0d5c7de42d63db6b51b69c6b5d` (byte-identical to the rebuilt baseline), pinning `f97d6a95a57841a619f1b842e3007320af1c0ff17f60366bb1b8b80912fe40e0`.
- **Host:** one On-Demand `g5.xlarge` (NVIDIA A10G, driver 595.91.07) in eu-west-1 per session, launched by `ops/aws-gpu-execution/control.py` with its fixed 25-minute deadline, scheduled cleanup and guest shutdown timer.
- **Execution:** `host-a10g-performance.sh`, one-shot per host, with network none, a read-only root and dropped capabilities.
- **Samples:** alternating baseline and candidate samples on the same GPU.
  - Subset: 24 samples of 2^29 ranks, over both rounds and both layouts.
  - Pinning: 12 samples of one sequence × 256,000,000 locktimes, over both layouts.
- **Validity checks, from the runners:** every sample reported its exact exhausted count, zero hits, one completion marker and a successful exit.

## Results (medians in seconds; projection = slowest startup-inclusive candidate sample scaled linearly)

| Stage | Baseline | Candidate | Throughput gain | Candidate full-range projection |
| --- | --- | --- | --- | --- |
| taproot-round1 | 16.431 | 12.558 | +30.84% | 402 s |
| taproot-round2 | 7.273 | 7.161 | +1.56% | 229 s |
| wpkh-round1 | 16.460 | 12.462 | +32.08% | 399 s |
| wpkh-round2 | 7.213 | 7.089 | +1.74% | 227 s |
| taproot-pinning | 1.481 | 1.480 | +0.09% | 115 s |
| wpkh-pinning | 1.347 | 1.347 | +0.03% | 105 s |

- **Subset round 1:** about **31–32% higher throughput** on the A10G, for both layouts. That's below the 76–81% measured earlier on an sm89 GPU.
- **Subset round 2:** about **1.6–1.7%**.
- **Pinning:** the repaired pinning matches the released pinning (+0.03% and +0.09%), so the host-error repairs carry no measurable cost.
- **Worker limit:** every candidate projection is below the 840-second worker limit and qsb-app's 900-second Batch timeout. A full subset round-1 range projects to about 400 s, round 2 to about 230 s, and a full 19.9-billion-candidate pinning range to about 105–115 s.

## Limits

- **Component timings only:** these are not a whole-withdrawal time or cost estimate, and not a pricing change. The full-range figures are linear projections, not measured full ranges.
- **Not coverage or correctness evidence:** the samples use public synthetic fixtures and grant no range credit. Correctness evidence remains the native component gate (`2026-09-25-a10g-components-v3.*`) and qsb-app's CPU verification of every hit.
- **Stopped sessions:** four sessions stopped before any GPU computation. They were operator-side issues: IAM propagation, Session Manager command handling twice, and a registry connection reset during the image pull. Each was cleaned up and verified; see `evidence/a10g-performance-2026-09-26/manifest.json`. No stage was run twice.

## Evidence

`evidence/a10g-performance-2026-09-26/` holds each stage's unmodified public result archive contents: `result.json`, `gate.log`, `gpu.txt` and `exit-code.txt`. `manifest.json` binds them to the source commit, bundle, image digests, binary and fixture hashes, and the host-reported archive hashes. Private operator receipts stay outside Git.
