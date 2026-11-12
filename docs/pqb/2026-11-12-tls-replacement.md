# TLS-fixed replacement qualification

The user authorized a fresh build and qualification from merged `main`, conditional
publication after release-blocker review, registry provenance verification and enrollment
handoff in the existing qsb-app PR #150 on 12 November 2026. Deployment, served release
selection, ECR mirroring and transactions are separate actions.

The assessed source is `cfd99e3844698f59679e4c15cf567db2976b9ffc`, exactly the merged
`main` tip when this campaign began. The frozen alias `codex/pqb-qualify-tls-20261112`
starts the dedicated signed OCI qualification build, run `43205074943`. The build
does not publish an image. Mutable package inputs are recorded by the actual receipt.

Before hardware allocation, source tests, original cleanup reconciliation and fresh
account/quota/AMI/network/price reads are required. The new external campaign reserves
$10, with at most one single-A10G session active, a fresh fixed 60-minute deadline,
guest shutdown and independent Scheduler/Lambda cleanup. The initial selected shape is
Ireland `g5.2xlarge`, at the verified $1.35296 per hour; each session reserves up to $5.
Failed or uncertain work is retained and reconciled before any new session. No old
campaign, deadline or reservation is resumed.

Ireland rejected fresh `g5.2xlarge` and `g5.16xlarge` launches for capacity; both
identities were reconciled with no instance and their temporary resources removed.
Virginia now has effective eight-vCPU G quota, no active GPU instances, and a verified
regional copy of the same Amazon-owned AMI release. The execution controller explicitly
allows `us-east-1` with focused region/shape tests; each Virginia session uses a fresh
external configuration, regional staging bucket, reservation, token and deadline.
Its `g5.2xlarge` price is $1.212/hour. This controller change does not rebuild or alter
the assessed image from `main`.

Qualification imports the exact attestation-verified archive, checks both normalized
runtime configurations, and runs 13 native small cases before each of the three largest
production units. The installed parser/failure and 16-chain TLS regressions must pass.
The credential-free live probe reads the installed S3 client's actual selected trust
store, tests 14 published bad hosts and two valid controls (including regional S3),
and treats network errors or expiry-only rejection as inconclusive/failure. No credentials
or HTTP requests are sent. Every original result and collection hash is retained.

The pinned consumer independently rechecks the native archive, reviewed gate identity,
39 case invocations and emitted candidates. This is fresh unit qualification and CPU
verification, not a new complete served solve, matched speedup or spend validation.
The older complete public Batch/S3 solve retains its original image identity.

Publication stays blocked until the actual scan, TLS regressions, native and consumer
results and source/binary/runtime applicability are reviewed. Publish by copying all
manifests of the qualified archive with preserved digests, without rebuilding. Retain
and verify the original build's signed OCI bundle from the registry as well as GitHub.
Only the verified published descriptor may be copied verbatim into PR #150; preserve
all earlier descriptors and existing deployment/default selection.

Build, qualification, publication and handoff results are pending in this initial plan.

After the regional and explicit-zone single-GPU rejections, an explicit `g5.12xlarge`
capacity fallback is permitted for this campaign: one active instance, four allocated
A10Gs, only physical GPU 0 exposed to the qualification container, and all host GPUs
retained in the inventory. The freshly verified Ireland rate is $6.33167/hour. The
session reserves $8 within the campaign's $10 reservation; all earlier zero-instance
reservations are released. The fixed 60-minute deadline and 840-second unit bounds
remain unchanged. Costs include the complete host; no matched hardware speedup is claimed.

The larger A10G request was also rejected with no instance. London exposes a full L4
in `g6.2xlarge` (eight vCPUs, $1.24095/hour). The selected new gate names L4 explicitly
in its committed expected-case inventory and checks that identity in every small case
and full-unit log. The 13 hit sets, ranges, production gate and 840-second worker bound
are unchanged. Historical A10G archives remain bound to their original gate and device;
they cannot be relabeled as fresh L4 qualification.

[NVIDIA's Ada compatibility guide](https://docs.nvidia.com/cuda/ada-compatibility-guide/index.html)
states that compute-capability 8.6 cubins run on 8.9 devices; the existing sm86 binary
therefore needs no rebuild for L4. This establishes applicability, not measured
correctness or timing: all native checks still must pass on the actual L4. No JIT,
kernel, timeout or experimental flag override is enabled. L4 serving would require
its own explicit Batch/deployment configuration; enrollment alone does not select it.
