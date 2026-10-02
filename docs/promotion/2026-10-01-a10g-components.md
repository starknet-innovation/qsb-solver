# A10G component gates passed for candidate-sm86-20261001-1

> Record of 1 October 2026. This is not authorization to repeat the experiment.
> The candidate stays HOLD until its descriptor is published and enrolled separately.

## Why this run

Candidate `candidate-sm86-20261001-1` (source `40b5d9f9f741eeac498c55ba98f52db08c288170`, image `sha256:6b4ac63b…`) rebuilt the published combined image with current Ubuntu runtime updates and the Runpod transport retired.

- Its pinning (`cd70b2c2…`) and subset (`673ad624…`) binaries are byte-identical to the September release.
- The runtime libraries they link against (`libc6`, `libssl3`) changed by patch releases, and the handler files lost their dead Runpod entry points.
- This run checks the September component gates against that runtime. It is not a performance comparison.

## Result

Two independent replicas each ran on one NVIDIA A10G (driver 595.91.07), on two different physical GPUs. The controller was commit `353cfad0328640aa7c6e62fcf1fa3297f2de2c97`. Every phase and count matches the [September component record](2026-09-25-a10g-components-v3.md):

- **Curve diagnostic:** 11,256 points, four infinity cases and 504 table checks; zero errors.
- **Exceptional recovery:** 156 branches matched the independently hash-bound CPU expectations. Synthetic injection is not naturally discovered preimage coverage.
- **Capacity:** seven cases (0, 1, 63, 64, 65, 1024, 1025) passed; overflow fails closed.
- **Memory:** seven checks passed under compute-sanitizer, using memory-tooling image `sha256:90dedfe0…`, built from the candidate digest.
- **Pinning host fault injection:** all 34 reached host calls were individually fault-injected and rejected. Overflow and publication checks passed.
- **Historical single-pin replay:** independently CPU verified (valid, sequence 2147507508, locktime 1497688167). It is not a fresh search or withdrawal.

## Inputs and bindings

- **Audit bundle:** [`validation-sm86-components-353cfad.tar.gz`](https://github.com/starknet-innovation/qsb-solver/releases/download/candidate-sm86-20261001-1/validation-sm86-components-353cfad.tar.gz), SHA-256 `6456b900…`, manifest `2fb66583…`.
  - It equals September's bundle except for the runner's commit pin, the host script's memory-image pin, the manifest's controller commit and the checksum list. The diagnostic binaries (built at `963147b`) are unchanged.
  - Offline, September's bundle rejects this candidate ("Wrong source or architecture"), and this bundle passes every pre-GPU check against it.
- **CPU reference:** the same six qsb-app `worker/cpu` files, context and expected-branch file as September, checked by hash before verification.
  - Before launch, the verifier reproduced September's verdict from September's result, and it rejected that result under this run's binding.
- **Public evidence:** the [public summary](2026-10-01-a10g-components.json) and, under [evidence/a10g-components-20261001](evidence/a10g-components-20261001/), each replica's result with GPU UUIDs redacted and its CPU verdict.
  - The [redaction manifest](evidence/a10g-components-20261001/manifest.json) records each original result hash. Only 18 device-UUID occurrences per result were replaced.
  - Infrastructure identifiers remain in local operational receipts.

## Execution, cleanup and cost

- **Scope:** one g5.xlarge per replica in eu-west-1c. Each had a fixed 25-minute deadline with an independently verified, tag-scoped cleanup schedule.
- **Commands:** one SSM host command per replica. No launch or compute submission was retried.
- **Runtime:** each instance ran about 4.9 minutes before termination. The estimated compute is $0.18 at $1.123 per hour; this is an estimate, not provider billing.
- **Cleanup:** independent postchecks at 19:07 UTC confirmed, for both replicas, instance termination, root-volume deletion, and removal of the security group, schedule, cleanup function, three roles and the instance profile. A sweep of eu-west-1 and eu-west-2 found no GPU or QSB-tagged instances and no remaining `qsb-bench-` resources.

## Limits

- The diagnostic executables are distinct from the release binaries.
- The release binaries are byte-identical to the September release. This run's evidence covers the changed runtime, not a new compiler output.
- Not covered: matched performance, a fresh search or withdrawal, live Batch certification, and external miner inclusion.
- Descriptor publication, qsb-app enrollment, the ECR copy and the job definition remain separate steps. Mainnet stays disabled.
