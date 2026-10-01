# Documentation and verified release status

Checked 1 October 2026. This page describes the solver `main` documentation and
its published combined release. Research branches and their experiment receipts
must be assessed separately; their code is not automatically included in this image.
AWS Batch is the only transport built or published; the Runpod transport was retired
on 1 October 2026 and its earlier releases remain immutable records.

## Published and enrolled artifact

[combined-aws-sm86-v0.2.0](https://github.com/starknet-innovation/qsb-solver/releases/tag/combined-aws-sm86-v0.2.0)
was published on 26 September 2026 at 17:36:58 UTC, targeting commit
`8fe127790397b6903640f8949219c1ef34a92db2`. Its `solver.json` describes the existing
image, without rebuilding it:

- Image: `ghcr.io/starknet-innovation/qsb-solver@sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d`.
- Attested image source: `43c77084648aa0f4cbcb1589abfcc792c9cc0d9d`, preserved by `candidate-sm86-20260925-1`.
- Descriptor: [qsb-ranked-v2-43c77084648a-e22afc720df1](promotion/releases/qsb-ranked-v2-43c77084648a-e22afc720df1.json).
- Consumer enrollment: the identical descriptor and its generated registry import
  are present in [qsb-app at c7c900e8](https://github.com/starknet-innovation/qsb-app/tree/c7c900e8b0a9dbed58433d70ae66fc8838dede56/src/lib/releases).

Enrollment is verified repository state. Live deployment, selected runtime digest,
mainnet activation and transaction execution were not checked by this documentation
audit and cannot be inferred from enrollment.

## Evidence and limits

The [publication record](promotion/2026-09-26-publication.md) binds the native
component checks, binary identities and final review. The
[matched A10G results](promotion/2026-09-26-a10g-performance.md) report subset round 1
about 31–32% faster, round 2 about 1.6–1.7% faster, and unchanged pinning.
These are bounded per-stage comparisons. Full-range times are projections;
they are not measured complete-pipeline throughput, withdrawal latency or
on-chain fee savings. New builds cannot inherit these results without an
artifact-specific applicability assessment.

## Reading map

- [Agent objective and process](../AGENTS.md): Yukon research assessment and image handoff.
- [Combined worker](../worker/promotion/README.md): integration and promotion requirements.
- [Combined publication guide](promotion/COMBINED-RELEASE.md): descriptor preparation and consumer boundaries.
- [AWS build compatibility](promotion/AWS-OPTIMIZED.md): architecture and transport identity.
- [Standalone optimized subset](../worker/optimized/README.md): a separate build target, not the complete published image.
- [A10G method record](promotion/A10G-PERFORMANCE.md): retained preparation methodology for the completed September gate.
- [AWS controller on main](../ops/aws-gpu-execution/README.md): historical scoped controller, not a standing launch authorization.
- [Licensing](../LICENSES.md): upstream notices and redistribution scope.

## Historical records

The dated files under `docs/promotion/` preserve observations and plans at their
recorded dates. September 25 HOLD statements and pending gate lists were
superseded for the exact published artifact by the September 26 publication
record. They do not apply unchanged to new artifacts, and are not instructions
to restart completed tests. Raw JSON receipts and their paths are retained.

[Archived ranked-v1 tooling](../research/archived-validation/README.md) and
[the original sm89 validation batch](../worker/promotion/validation/README.md)
remain historical references. Vendored upstream documentation is preserved with
its source snapshot; it is not current qsb-solver operational guidance.
