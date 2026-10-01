# QSB solver: objective and research-to-image process

## Objective

Turn well-supported research from
[Layr-Labs/quantum-safe-bitcoin-challenge](https://github.com/Layr-Labs/quantum-safe-bitcoin-challenge)
(the Yukon benchmark repository) into reproducible, validated worker images that
[qsb-app](https://github.com/starknet-innovation/qsb-app) can consume by immutable
digest and an explicitly enrolled release descriptor.

Prefer reusing and evaluating existing research over rediscovering completed work.
The objective is lower cost and latency for correctly completed public-data work,
with evidence for each stage and the complete supported pipeline. A leaderboard
score, isolated arithmetic speedup, successful build, or published image does not
by itself achieve that objective. Faster compute also does not establish lower
on-chain transaction fees.

The best candidate is the one with applicable, reproducible evidence and compatible
correctness and coverage semantics—not simply the largest reported score.

## Start with the current state

- Read `README.md`, `contracts/ranked-v2.json`, `worker/promotion/README.md`,
  `worker/optimized/README.md`, and the relevant experiment documentation.
- Inspect Git status and the actual build inputs before changing anything. Keep
  unrelated work intact. Do not deploy or remotely execute uncommitted source.
- Read `vendor/challenge/provenance.json` and
  `worker/optimized/source-lock.json`. The historical vendor import, adapted
  research snapshot, experiment harness, and published image are distinct objects.
- Read the applicable campaign ledger and latest completion/cleanup receipts
  before cloud work. Old budgets, schedules and launch permissions are not new
  authorization. Do not restart completed experiments or paused automations.

## 1. Audit Yukon research before selecting changes

Pin an upstream commit and record the comparison base, audit date and repository
URL. Compare complete trees, including additions and deletions. GitHub comparison
responses can cap the file list; do not infer that a track is unchanged from a
partial response. Check pagination and tree truncation explicitly.

Maintain a candidate assessment containing:

- Exact source identity and affected stage; whether the work is already imported,
  locally adapted, absent, or superseded.
- Evidence provenance: organizer result, author report, CPU test, compiler/static
  observation, native GPU execution, or matched timing.
- Hardware, runtime, workload and timing boundaries, plus correctness and coverage
  limitations relevant to our public contract.
- Disposition and reason: retain for review, already present, incompatible,
  rejected by evidence, or awaiting evidence.

Separate historical notes from current source attestations. Validate manifests
against actual bytes; commit messages such as “Accept” or “Validate” are not a
complete performance receipt. Preserve rejected results and negative findings so
later work does not pay to repeat them without a new reason.

## 2. Establish applicability and correctness requirements

Use public synthetic inputs for development and validation. Keep wallets, private
keys, recovery secrets, funded outputs and live transaction submission outside
this workflow. qsb-app retains its independent CPU verifier, coordinator, wallet
and release registry; do not move those trust responsibilities into the image.

Review candidate behavior against `ranked-v2`, including partition identity,
completeness, duplicates, exceptional cases, capacity limits, failures and durable
output. A benchmark that rewards verified hits can tolerate missed opportunities
that are incompatible with a complete-range claim. Exact checking of emitted
hits does not prove that no valid work was omitted.

Preserve required error checks and independent validation. Do not remove them to
improve a timing denominator. Do not silently enable experimental flags or combine
individually tested changes and call the resulting executable validated.

Keep imports and local adaptations attributable and reviewable. Preserve upstream
licenses and notices, including those required by linked or derived components.
Record source hashes and material deviations; do not identify a composite worker
as an unchanged upstream submission.

## 3. Bind validation to the artifact being assessed

Complete the public-input test plan and result-collection path before allocating
paid hardware. Exercise relevant local checks first. Native execution needs a
clean committed/pushed controller, exact source and binary hashes, an immutable
runtime, and a complete collection plan.

Separate correctness evidence from performance evidence. Record which checks
actually ran, which failed, and which remain unexecuted. New source, compiler,
flags, runtime or binary identities require an explicit review of whether older
evidence still applies; an old success is not a new attestation.

For performance assessments, require comparable baseline/candidate workloads,
the same hardware, repeated interleaved samples and the full retained receipt.
Distinguish cold process startup, warm device execution and steady-state work.
Report startup, transfers, computation, verification and output costs where
measured. Report pinning, round 1 and round 2 separately when applicable; claim
complete-pipeline throughput only when that complete pipeline was measured.

Keep isolated public-arithmetic results explicitly labeled as component results.
Account for failed/incomplete work when assessing cost; do not substitute submitted
work, self-reported counters or selected successful samples for validated results.

## 4. Produce a reviewable image and qsb-app handoff

Check the actual Dockerfile and release workflow before choosing a publication
path. Currently the ordinary release workflow builds the historical worker;
research files do not enter that image merely because they are committed nearby.
Combined validation candidates and normal app releases are separate paths.

The handoff must identify:

- Source commit, imported provenance and reviewed adaptations.
- Actual binary hashes, compiler/build flags, runtime and dependency identities.
- Immutable registry digest, build provenance, retained notices and release assets.
- Contract version/hash and the matching request/result vectors tested by both
  repositories. Partition changes require a new `searchVersion`.
- Correctness/performance receipts, known limitations, adoption decision and the
  previous image/descriptor available for rollback.

Keep candidates on HOLD until the applicable evidence has been reviewed. Never
fabricate a digest or reuse an older binary's receipt. Describe builds with mutable
package inputs accurately; pinned base images alone do not guarantee bit-for-bit
reproducibility.

Publication, qsb-app enrollment and deployment are separate actions. Follow the
repository's explicit authorization requirements and any authorization already
given in the current session. Do not silently change app defaults, overwrite old
descriptors, merge a draft, activate mainnet or broadcast a transaction. Prepare
the concrete evidence package before requesting any missing final approval.

## Cloud execution and reporting

Follow `ops/aws-gpu-execution/README.md` and the current campaign constraints.
Persist request identities and budget reservations before paid submissions; count
unknown submissions until reconciled. Use the committed controller, independently
verified cleanup, a fixed deadline, and isolated containers. Never retry an
uncertain launch or compute submission, or extend an active deadline.

Terminate promptly on completion or failure. Independently verify instance,
recorded volume and temporary-resource deletion. Unresolved cleanup takes priority
over new experiments. Preserve original receipts and save fresh reconciliation
evidence separately.

Finish each assessment with what changed, what was actually measured, the
applicability limits, cost accounting, cleanup state, and the next evidence gap.
Distinguish estimated/reserved budget from provider billing. Keep the source and
evidence ready for review; do not present publication or deployment as completed
without verifying the resulting state.
