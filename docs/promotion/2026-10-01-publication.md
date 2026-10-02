# Publication record: combined sm86 AWS release, 1 October 2026

Status: **published on 2 October 2026 at 05:19:08 UTC as `combined-aws-sm86-v0.3.0`, targeting `490e21af84b95ed13aa5b3dae7260422f96718db` (verified 2 October).** Publication was approved by @adrienlacombe on 1 October 2026, conditional on the native component check, which passed. The descriptor is enrolled in qsb-app at `6082b55` ([qsb-app#131](https://github.com/starknet-innovation/qsb-app/pull/131)), not served; see [verified status](../README.md).

## What changed since combined-aws-sm86-v0.2.0

- **Runtime OS packages:** Ubuntu updates are applied from Ubuntu's archives only; the pinned CUDA packages are unchanged ([#9](https://github.com/starknet-innovation/qsb-solver/pull/9)). The scan gate passed with zero fixable findings.
- **Runpod transport retired** ([#10](https://github.com/starknet-innovation/qsb-solver/pull/10)). Both handler files lost their dead Runpod entry points.
- **Binaries unchanged:** pinning `cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62` and subset `673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15` are byte-identical to the September release. The subset build receipt matches in every identity field.

## Gates

- **Candidate build** `candidate-sm86-20261001-1`: GitHub-attested image `ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48` from source `40b5d9f9f741eeac498c55ba98f52db08c288170`. That source is tree-identical to `main` at `a876265`.
- **Native sm86 component checks** on two independent A10G replicas: every phase and count matches September, with independent CPU verification. See [2026-10-01-a10g-components.md](2026-10-01-a10g-components.md).
- **No matched performance run:** the binaries are unchanged, so the September per-stage A10G performance results describe the same executables. The runtime libraries received patch releases only. This is an applicability judgement, not a new measurement.

## What is published

- **Descriptor:** [qsb-ranked-v2-40b5d9f9f741-6b4ac63b897c.json](releases/qsb-ranked-v2-40b5d9f9f741-6b4ac63b897c.json). It is identical to the `solver` object that `scripts/prepare_combined_release.py` emitted after verifying the candidate's attestation; the preparation hashes are in [2026-10-01-publication.json](2026-10-01-publication.json). Against the enrolled September descriptor, only `id`, `image`, `solverCommit` and `kernelCommit` differ.
- **Search contract:** ranked-v2 `c570e14089e62de5185d9c8ba9f8f85d1b22c788edc524cd98a9ecaac5c26f7a`, unchanged.
- **Release tag:** `combined-aws-sm86-v0.3.0` on this record's merge commit `490e21a`, with the descriptor as `solver.json`. The name avoids both publishing workflows (`aws-v*`, `candidate-sm86-*`). No image is built for it, and no registry is written to.
- **Candidate tag:** `candidate-sm86-20261001-1` must never be moved or deleted, because it keeps the attested source reachable.

## Rollback

The previous release `combined-aws-sm86-v0.2.0` (`sha256:e22afc72…`) and its enrolled descriptor remain unchanged and available.

## Not part of this record

- Enrolling the descriptor in qsb-app, a separate reviewed app change ([qsb-app#131](https://github.com/starknet-innovation/qsb-app/pull/131)).
- Deploying it: copying the digest into ECR, registering a new job definition, and setting the app stack's `solver_release_id`.
- Any mainnet switch.
