# Public synthetic PQB solve through the consumer transport

The [11 November campaign completed all three stages](../../docs/pqb/2026-11-11-public-transport-solve.md)
and independently verified cleanup. Its original receipts are retained. These preparation
instructions are not a request to restart that completed campaign or reuse its closed budget.

This development assessment uses the actual qsb-app `AwsBatch` SDK transport, public problem
export, request/result checks, range definitions, reservation arithmetic, stage application and
independent CPU verifier. It targets a temporary private image and isolated Batch environment.
It is not the served Step Functions coordinator, a release enrollment, wallet authorization,
consensus test or transaction submission. The candidate remains HOLD until evidence review.

The consumer is pinned by `consumer-lock.json`. `build.mjs` requires that clean checkout and
its installed locked dependencies. It bundles imports from that checkout; no consumer verifier
is copied into the GPU image. The local controller accepts only a public state and synthetic
manifest, not recovery state or a seed. Derive the public fixture locally from the consumer's
committed public synthetic reference; keep the seed out of cloud payloads and controller input.

Before hardware, complete local tests, clean/push both the controller and image source, obtain
the exact successful push CI image artifact when available, verify its ZIP and every contained checksum,
prepare all collection paths, read previous cleanup and record fresh request/budget identities.
The ordinary release workflows do not publish this image. The `codex/pqb-batch-*` CI push path
exports a hash-bound image archive without publishing. `publish_private.py` checks its actual
Docker image/binding, then imports it into one temporary immutable private ECR repository.
Runtime ECR credentials stay inside the isolated publisher process and are never logged.
If the artifact service is unavailable, a clean committed/pushed source may instead be built
on a bounded native Linux publisher. Repeat the actual image checks and vulnerability policy,
retain the raw image archive and byte hashes, and identify this origin as a separate native
build. Completed CI steps do not make a stalled or failed workflow a successful run.

The first complete unit is a real transport preflight. After its checked success the controller
fills up to 16 ordinary A10G workers, using production 24-bit predicates, the same partition and
840-second worker timeout. No experimental CUDA options, reduced gates, known-solution seeds,
patched verifier verdicts or fast-path arithmetic are enabled. Each input object is immutable.
The consumer checks the exact Batch definition/compute limits before preparing a submission.
The controller durably saves its identity and nonrefundable 900-second reservation before its
single paid POST. Unknown outcomes stop submissions; no process resumes an existing output
directory. Failed/incomplete units stop the assessment without range credit.

An explicit fourth CLI argument may hand over the known initial pinning phase before any
solution has been accepted. It verifies the unchanged configuration/deadline, public input,
every request digest/provider ID, contiguous assigned attempts and every original 900-second
reservation. Completed outputs are read and checked again under the pinned CPU policy.
No paid request is replayed; unknown requests and later-stage checkpoint resumes are refused.

Each stage's hit is independently checked before advancement. Outdated jobs are cancelled and
drained; any completed output is still checked against its original problem/context. Exhausting
a round re-pins at the next pinning unit, retaining prior attempts and costs. All three final
hits are checked again against the original public intent. Success means a public three-stage
solution, not a signed spend. Original S3 envelopes, native CloudWatch logs, job details,
CPU decisions, cancellation outcomes, identities and controller checkpoints must be collected.
The bundled `export-reference.cjs` exports accepted public packets and candidates from a
checkpoint. Run `crosscheck.py` with the clean pinned upstream checkout to compare complete
problem bytes and check each hit through upstream `HitChecker` and canonical `grind.evaluate`.
Use a local environment with upstream's pinned `coincurve==21.0.0`; the default requires its
native libsecp256k1 binding and records its shared-object hash and Python runtime. The explicit
`--wasm-shim` option gives separate supplemental evidence using upstream's pure-Python curve
shim and vendored Bitcoin test-framework arithmetic. Neither executes Bitcoin Core consensus.
Its only packet adaptations convert public decimal scalar strings to integers and add the
nonce-space size. Keep the upstream acceptance policy unchanged; this is not miner acceptance.
`crosscheck-emitted.py UPSTREAM CAMPAIGN STATE_DIRECTORY STAGE PACKET_EXPORT NEW_OUTPUT`
also checks every completed unit's emitted hits against upstream and the saved consumer verdict,
including negative hits. It binds the original S3 input bytes. `PACKET_EXPORT` may be the
accepted reference export or a public `{packet, problem}` object. Each receipt covers one exact
problem; other problems after re-pinning are listed as unexamined and need their own exports.

The fresh campaign has one fixed six-hour deadline, a 600-unit / 540,000 GPU-second reservation
ceiling and at most 16 g5.xlarge instances. Record a $200 operational reservation before paid
submissions and distinguish it from billing. A separate 25-minute publisher host, if needed,
uses its own recorded $2 reservation and the existing one-shot controller. Do not extend either
deadline. The Batch guest launch template shares the campaign deadline. An independently armed
Scheduler/Lambda disables the queue/environment, cancels/terminates work and deletes the Batch
fleet at expiry. It does not delete evidence. The operator stops it promptly on success/failure.

Use `control.py prepare`, upload the exact cleanup ZIP, then `arm` once. After the publisher is
fully cleaned up and its private image receipt verified, `batch` creates the isolated queue and
one-attempt job definition. Configuration, state and AWS MCP request/dispatch/result files stay
outside Git. Use the connected AWS MCP broker; never replay an uncertain resource mutation or
compute POST. Bind the actual GPU AMI, source/binary identities and private digest in the ledger.

Continuously record allocated instances and their root-volume IDs. At completion or failure,
`stop` drains/deletes the queue and environment. Collect and hash all S3 objects and logs before
removing them. Verify all campaign instances terminated and every recorded volume deleted;
then `remove` deletes the definition, IAM/profile/SG/launch template, ECR repository, scheduler,
function, bucket and log groups. Save fresh independent reconciliation separately. Unresolved
cleanup takes priority over new work. Keep original failed/negative receipts and explicit
source identities rather than relabeling the earlier component/full-unit campaigns.
