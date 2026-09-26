# Publication record: combined sm86 AWS release, 26 September 2026

Status: **approved for publication by @adrienlacombe on 26 September 2026**. It isn't enrolled in qsb-app yet; enrollment is a separate app change.

## Gates, all met

Recorded on the merged qsb-solver#2 (`2e7e1e0`, a squash merge):
- **Native sm86 A10G checks** (pinning, exceptions, curve, memory): `2026-09-25-a10g-components-v3.*`.
- **Matched A10G performance against `aws-v0.1.0`**, covering both subset rounds and pinning: `2026-09-26-a10g-performance.md`. Subset round 1 is about +31–32%, round 2 about +1.6–1.7%, and pinning is unchanged. Every candidate full-range projection is under 840 s.
- **Final independent review:** qsb-solver#2 had all 11 threads resolved and a `merge_ready=yes` verdict at `bd9b358`.
- **Fresh wallet-backed proof:** removed from the gates by the user on 25 September. The first separately authorized mainnet withdrawal (qsb-app#22) provides the end-to-end evidence.

## What is published

- **Descriptor:** `releases/qsb-ranked-v2-43c77084648a-e22afc720df1.json`, a strict schema-3 descriptor for the app's consumer. It's identical to the `solver` object that `scripts/prepare_combined_release.py` emitted after verifying the candidate's GitHub attestation. The preparation hashes are in `2026-09-26-publication.json`.
- **Image:** the already tested, immutable `ghcr.io/starknet-innovation/qsb-solver@sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d`, built and attested from source `43c77084648aa0f4cbcb1589abfcc792c9cc0d9d` (tag `candidate-sm86-20260925-1`). It is **not rebuilt**. The candidate tag must never be moved or deleted: after the squash merge, it is what keeps the attested source reachable.
- **Binaries:** pinning `cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62`, subset `673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15`. Both are sm_86.
- **Search contract:** ranked-v2, `c570e14089e62de5185d9c8ba9f8f85d1b22c788edc524cd98a9ecaac5c26f7a`, unchanged from `aws-v0.1.0`.

## Release tag

The release is published as the GitHub release `combined-aws-sm86-v0.2.0` on the commit that merges this record. That tag name deliberately matches none of the workflow triggers: `release.yml` fires on `v*` and `aws-v*`, and would rebuild the historical solver; `candidate.yml` fires on `candidate-*`, and would build a new image. The release only carries this descriptor. No image is built or pushed.

## Not part of this record

- Enrolling the descriptor in qsb-app, a separate reviewed app change.
- Deploying it: copying the digest into ECR, a new job definition, and the app stack's `solver_release_id`.
- Any mainnet switch. Mainnet switches and exact-transaction authorization remain separate decisions.
