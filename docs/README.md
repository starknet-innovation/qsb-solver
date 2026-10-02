# Documentation and verified release status

Checked 2 October 2026. This page describes the solver `main` documentation and
its published combined releases. Research branches and their experiment receipts
must be assessed separately; their code is not automatically included in this image.
AWS Batch is the only transport built or published; the Runpod transport was retired
on 1 October 2026 and its earlier releases remain immutable records.

## Published and enrolled artifacts

[combined-aws-sm86-v0.3.0](https://github.com/starknet-innovation/qsb-solver/releases/tag/combined-aws-sm86-v0.3.0)
was published on 2 October 2026 at 05:19:08 UTC, targeting commit
`490e21af84b95ed13aa5b3dae7260422f96718db`. Its `solver.json` describes the existing
image, without rebuilding it:

- Image: `ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48`.
- Attested image source: `40b5d9f9f741eeac498c55ba98f52db08c288170`, preserved by `candidate-sm86-20261001-1`.
- Descriptor: [qsb-ranked-v2-40b5d9f9f741-6b4ac63b897c](promotion/releases/qsb-ranked-v2-40b5d9f9f741-6b4ac63b897c.json).
- Relation to v0.2.0: the same pinning and subset binaries, with Ubuntu updates
  applied to the runtime at build and the Runpod transport retired.
- Served: on 2 October 2026 an uncached `/api/config` of the eu-west-2 deployment
  reported this release ID, and a bounded AWS Batch preflight on its job definition
  (`nvidia-smi` only) ran image digest `sha256:6b4ac63b…`.
- Consumer enrollment: the identical descriptor and its generated registry import
  are present in [qsb-app at 6082b55](https://github.com/starknet-innovation/qsb-app/tree/6082b55ae7aa9ce46b9da84fcda845bc02f04337/src/lib/releases).

[combined-aws-sm86-v0.2.0](https://github.com/starknet-innovation/qsb-solver/releases/tag/combined-aws-sm86-v0.2.0)
was published on 26 September 2026 at 17:36:58 UTC, targeting commit
`8fe127790397b6903640f8949219c1ef34a92db2`. Its `solver.json` describes the existing
image, without rebuilding it:

- Image: `ghcr.io/starknet-innovation/qsb-solver@sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d`.
- Attested image source: `43c77084648aa0f4cbcb1589abfcc792c9cc0d9d`, preserved by `candidate-sm86-20260925-1`.
- Descriptor: [qsb-ranked-v2-43c77084648a-e22afc720df1](promotion/releases/qsb-ranked-v2-43c77084648a-e22afc720df1.json).
- Consumer enrollment: the identical descriptor and its generated registry import
  are also present in [qsb-app at 6082b55](https://github.com/starknet-innovation/qsb-app/tree/6082b55ae7aa9ce46b9da84fcda845bc02f04337/src/lib/releases).

v0.2.0 stays enrolled in qsb-app for rollback. Enrollment is verified repository
state, and the served release and runtime digest above were checked on 2 October.
Mainnet activation and transaction execution were not checked by this documentation
audit and cannot be inferred from enrollment or serving.

## Evidence and limits

For v0.3.0, the [publication record](promotion/2026-10-01-publication.md) binds the
[native component checks](promotion/2026-10-01-a10g-components.md), run on two A10G
replicas, the binary identities and the candidate's release scan. That scan found
no fixable findings on 1 October; nothing rescans published images. No matched
performance run was made for v0.3.0: its binaries are byte-identical to v0.2.0 and
only runtime libraries received patch releases, so the September results below
apply by an applicability judgement, not a new measurement.

For v0.2.0, the [publication record](promotion/2026-09-26-publication.md) binds the native
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
record; the October 1 records apply to the v0.3.0 artifact. They do not apply
unchanged to new artifacts, and are not instructions to restart completed tests. Raw JSON receipts and their paths are retained.

[Archived ranked-v1 tooling](../research/archived-validation/README.md) and
[the original sm89 validation batch](../worker/promotion/validation/README.md)
remain historical references. Vendored upstream documentation is preserved with
its source snapshot; it is not current qsb-solver operational guidance.
