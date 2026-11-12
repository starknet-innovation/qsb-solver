# Final PQB image qualification and provenance

This is a new assessment authorized on 12 November 2026, separate from the completed public
solve. No prior campaign, deadline, reservation or automation is resumed. Publication of an
app release, enrollment, deployment and transactions remain separate actions.

## Build and provenance

The `codex/pqb-qualify-*` branch push workflow builds the actual `worker/pqb/Dockerfile` AWS
target, sm86, with its exact source commit. It exports an OCI archive with BuildKit provenance,
verifies all blob hashes, imports that archive for offline worker/failure checks, records the
actual installed binding/build receipt, config, packages and notices, and scans the exact
archive. A GitHub-hosted runner signs both the archive/checksum assets and the actual OCI
manifest digest. No registry credentials, image push, release, descriptor enrollment or app
deployment are part of this workflow.
Offline checks exercise the installed completion parser with a simulated grinder log larger
than 2 MiB: an early duplicate completion must fail, while one completion passes the parser.
The actual no-GPU binary failure remains a separate check; simulated logs are never native evidence.

Before native work, download the successful exact-source push artifact; verify its GitHub
attestations with the exact repository, signer workflow `.github/workflows/pqb-qualify.yml`,
source branch/ref, source commit and `--deny-self-hosted-runners`. Verify archive/checksum
and OCI subject digests, and the OCI subject name `ghcr.io/starknet-innovation/qsb-solver`.
Retain the signed bundles and verification JSON. The digest of `image-manifest.json` is the
publishable OCI index digest, not the Docker config digest. Signing this prospective subject
does not assert that its image is available from GHCR. Later authorized publication must copy
the qualified archive with all manifests and preserved digests, without rebuilding it, then
verify registry-side provenance and the resulting digest.

APT/Python inputs are mutable; record the actual packages/compiler/runtime. These are exact
artifact identities, not a claim of bit-for-bit rebuild reproducibility. Keep all notices,
MIT source attribution and material adaptation records. The CPU reference stays outside the
image.

## Native public plan and collection

Use one fresh **60-minute** single-A10G session for all three largest `pqb-ranked-v2` units.
Capacity rejections and the retained host import failure motivated consolidation before any
new session was armed; no earlier deadline is extended. `--session-minutes 60` is frozen at
prepare. The controller's existing 25-minute single-unit mode remains available for separately
authorized future assessments. Record the new source and bundle identities before launch.
If xlarge capacity is unavailable, a fresh session may use the controller's explicit
`--instance-type` at prepare: single-A10G G5 sizes through `g5.16xlarge`. The controller checks
the provider's actual GPU/CPU description and effective quota before submission. Verify fresh
pricing against the recorded session reservation first. Preserve and clean up failed sessions before
choosing a new size; no armed deadline or request is edited or retried. The image/partition
remain the same; different CPU resources are recorded and are not a matched performance claim.
Fresh sessions may explicitly select `--auto-default-subnet` at prepare to let EC2 choose
the Availability Zone within the verified default VPC. Before launch, the controller verifies
that VPC and its public default subnets, and retains the dedicated no-ingress security group.
It records the actual selected subnet/AZ. This makes one regional launch request, not a loop
of uncertain launches. Explicit subnet placement remains the default. See the
[RunInstances subnet semantics](https://docs.aws.amazon.com/AWSEC2/latest/APIReference/API_RunInstances.html).
Each session imports the same verified OCI archive; the actual rootfs diff IDs and every
runtime config field must equal the attested image's configuration before compute. Docker's
containerd store can report an index/manifest in `.Id`, so that field is retained separately
and never mislabeled as a config digest. The mounted public gate contains no worker
copy. Native import uses the host Docker client directly: Ubuntu 22.04's Skopeo 1.4 daemon
transport uses an API version rejected by the pinned host's Docker 29. That setup failure
is retained separately and is not a GPU result. The signed image itself is unchanged.
`qualify_image.py` imports and validates the installed image's actual bound handler,
partition and binary, and checks the committed contract vectors.

Each stage first runs all 13 existing independent small hit-set cases, including boundary,
multi-batch, DER-filter-positive and planted exceptional-point cases, with a 60-second
preflight allowance. Test gates/flags are explicit in the committed expected cases only.
The full unit uses the unmodified installed handler, production 24-bit gate, exact attempt 0,
840-second worker timeout, unique candidates, independent hit derivation, batch/range counts,
gate-count sanity and native A10G identity. Each largest-unit invocation must finish within
the worker bound including CPU checking. Single-unit mode has a 1,000-second container bound.
The host refuses the three-unit container with less than 3,200 seconds left; its outer bound is
3,100 seconds. Each unit still has the unmodified 840-second worker limit, and the runner
requires at least 1,100 seconds before starting each next unit. Any failed unit or lost margin
stops subsequent work without credit. No worker timeout or unit-size override.

Retain every small invocation's original problem, arguments, native stdout/stderr/hits;
full-unit request/result/problem/native log/hits; exact installed binding/build receipt;
GPU/driver, imported config, host setup/import logs, exit status, deadline, source, image and
gate hashes. Results are durable before verification and packed even on host setup failure.
Collect the original gzip JSON archive, verify its byte count/hash, then decode separately.
All SSM requests, provider responses, instance/volume IDs and collection identities remain
in the external campaign ledger. Do not replay a compute command or uncertain submission.

Run local unit/negative checks before allocation. Use the committed/pushed execution controller,
dedicated SSM-only IAM/SG, prearmed independent Scheduler/Lambda cleanup and guest shutdown
sharing the fixed deadline. No other test GPUs may be active before each sequential session.
The operational reservation is **$10 total**, including up to $5 for the consolidated session and
staging overhead; persist it before paid submission. This is a reservation, not provider billing.
Check fresh pricing/quota/account/AMI/subnet and prior cleanup. Known capacity failures may
only be followed after reconciliation and complete cleanup with a fresh session identity;
unknown launch outcomes must never be retried. Never extend an armed deadline.

Terminate promptly after success/failure and verify each recorded root volume is gone before
the next session. Independently reconcile temporary IAM, SG, function, schedule and staging
objects/bucket. Preserve all original receipts and fresh reconciliation separately. Cleanup
uncertainty takes priority over new work.

## Acceptance and applicability

All three exact-image stages and offline negative/parser checks must pass. Re-run consumer
contract/schema compatibility against the final identities. Record actual binary/source/flag
differences before applying earlier native arithmetic and complete-public-solve evidence.
The existing complete solve remains evidence for its own older image; this assessment measures
final-image unit correctness and timing, not another full solve or matched speedup. Retain the
zero-sighash, completeness, broader hardware, native re-pinning, served orchestration and
wallet/consensus/miner limits. Failed/incomplete work remains in cost accounting.

Finish with exact artifact/provenance/descriptor preparation, qualification receipts, a source
applicability decision, known limits, estimated cost versus billing, independent cleanup and
the remaining publication/enrollment decisions. No release is called published until the
actual registry/release state has been verified.
