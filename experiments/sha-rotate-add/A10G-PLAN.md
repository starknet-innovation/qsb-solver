# A10G native plan for the SHA rotate-add candidate

Status: **plan only, not authorized**. Nothing here has been launched, reserved or
requested. This document is not a launch permission, and earlier campaign budgets,
schedules and approvals do not carry over to it. Operator configuration, account
details and private receipts stay outside Git, as for every earlier run.

## What is being assessed

| Item | Value |
| --- | --- |
| Baseline binary | `8664f41f3deeeb91b3d189db3df469570c83e90610e4b54a955e2a625486606c` (committed subset source, production flags, sm_86) |
| Candidate binary | `bba9c4af12d65de4ffeea7c202ae2f830e815855a1f45a9f62f398730a9e65e1` (`candidate` variant: patched `GPUHash.h`, upstream defaults) |
| Built by | CI run 42687871125 at `4d403e1`, CUDA 12.8.93; see [README](README.md) |
| Not assessed | `candidate-ord0`, pinning, any upstream change other than this patch |

The baseline is the same binary the 30 September SHA experiment timed, so its
samples are a like-for-like reference for noise.

## Questions, in order

1. **Correctness:** does the candidate binary produce exactly the baseline's results
   on public synthetic inputs, and do its recovered-key hashes match qsb-app's separate
   CPU reference?
2. **Performance:** on one A10G, is the candidate faster than the baseline for subset
   round 1 and round 2, both layouts, with startup included?

Timing runs only if correctness passes. Neither answers whole-withdrawal cost,
pinning, complete-range coverage or on-chain fees.

## Decision rule, fixed before any run

- **Stop, do not promote:** any correctness mismatch, incomplete sample, unexpected
  hit, non-zero exit, or a failed prerequisite. No timing is reported in that case.
- **Worth a release-candidate review:** median throughput gain of at least 2% in
  round 1 for both layouts, and no round 2 median more than 0.5% slower.
- **Otherwise:** record "no demonstrated benefit" and keep the negative result.

The 2% bar comes from the 30 September receipt for the same baseline: warm samples
of one context differed by 0.1% to 0.6%, and one first sample was 16% slower than
its repeats. A gain under 2% is too close to that noise to justify a release.

## Sessions

Each session is one On-Demand `g5.xlarge`, one-shot, with the fixed deadline and
independent cleanup of the committed controller. A later session starts only after
the previous one is collected, cleaned up and verified.

| Session | Runs | Pass condition | Rough compute time |
| --- | --- | --- | --- |
| A. Ranges | Both binaries on four ranges, `(0,1)`, `(63,257)`, `(65535,65537)`, `(0,2^26)`, for each of the four contexts (two layouts, two rounds): 32 checks | Identical exhausted counts and identical hit sets for baseline and candidate; every sample complete | 2–3 min |
| B. CPU trace | The 20 committed trace fixtures on a diagnostic build of the candidate that prints recovered-key hashes, plus the unmodified candidate, checked against the pinned CPU reference | All 20 match; the diagnostic build is bound to the candidate by receipt | 3–4 min |
| C. Timing | Interleaved baseline and candidate, 2^29 ranks from rank 0, four pairs per context in A-B-B-A order: 32 samples | All samples complete with the exact count, zero hits and exit 0 | 5–6 min |

Sessions A and B may share one instance if a local dry run shows both fit the
compute budget with the required margin; otherwise they stay separate.

Timing reports, per context: every sample, the median for each binary, the gain, and
the first pair marked as cold. Wall time includes process startup. Full-range figures,
if quoted, are linear projections and are labelled as such.

## Prerequisites, none of which costs money

1. **Commit and push** the compile result, evidence and the ported tooling.
2. **Runner set: ported, tested locally.** `run_ranges.py`, `run_trace.py`,
   `run_pair.py`, `verify_trace.py`, `trace_source.py`, `host-full.sh`,
   `stage_full.py`, the CPU fixtures and the CPU reference lock come from
   `experiments/generic-sha-vector` at `b96752330d6d376a5bb0ba97cb6b2abe37d4e9eb`.
   Changes: the candidate hash, four pairs per context, the decision rule, no
   extracted-function compression prerequisite, a trace receipt that also binds the
   patched `GPUHash.h`, and identities that are `None` until frozen. With a `None`
   identity, staging and timing refuse to start. The controller files (`operate.py`,
   `chunk_results.py`, `ssm_command.py` and the 60-minute `control.py`) come from the
   same commit, with their tests.
3. **One frozen build: prepared, not yet run.** The build now also produces the
   diagnostic trace binary, its diff and receipt, and a small `sha-rotate-add-pair`
   artifact for staging. After it runs: check that the baseline and candidate hashes
   above reproduce, then freeze the run ID, commit, pair archive hash and trace binary
   hash in `stage_full.py`. If the hashes do not reproduce, the new ones replace those
   in this plan and that is recorded; package inputs are not snapshot-locked. The
   first CI artifact expires on 23 November.
4. **Runtime image: verified on 9 November.** The validation runtime the 30 September
   run used, `ghcr.io/starknet-innovation/qsb-solver@sha256:86eba696ee50bfd5e7b90eca1d3ed6dfa3f60582779a653eff5e9229b55cbfbf`,
   still verifies with `gh attestation verify` against this repository, built from
   `068a90dee65fb4567df1086261ee6350942558e7`. It is the CUDA 12.8.1 development
   image with Python and is never enrolled as a solver release.
5. **CPU reference.** Check out qsb-app's `worker/cpu` at the locked commit and verify
   it against the lock.
6. **Collection plan.** Result archive names, hashes, the bounded collector, and what
   is published (hashes and redacted results) against what stays private.
7. **Local dry run.** The ported tests already exercise real child processes with
   inert stand-in binaries, including timeout, short count and unexpected hit, and the
   staging script against a synthetic archive. A dry run with the frozen identities
   follows step 3.
8. **Pre-launch checks on the day:** clean, pushed controller commit; live price;
   effective quota; zero other test GPU instances; a fresh reconciliation showing no
   leftover resources from earlier scopes.

## Budget to authorize

| Item | Proposal |
| --- | --- |
| Allocations | At most three (A, B, C); two if A and B share an instance |
| Reservation | USD 5 per allocation, USD 15 in total, recorded before each launch |
| Compute price | USD 1.123 per hour was the Ireland `g5.xlarge` price on 30 September; to be re-read live |
| Lifetime | The controller's fixed 60-minute deadline per session; never extended, and terminated as soon as the session finishes or fails |
| Launch attempts | One per availability zone. An explicit capacity rejection allocates nothing and may be followed by the next zone. Any uncertain launch is reconciled, never retried |

Reservations are conservative bounds, not provider billing. Earlier sessions of this
size reserved USD 5 against an estimated USD 1.74.

Capacity is a real risk: on 16 October every launch attempt in the region was
rejected for insufficient capacity. Those attempts allocated nothing and were
verified clean. If that repeats, the plan stops and waits; it does not widen scope
to another instance type.

## Decisions needed from the owner

1. **Controller: decided on 9 November.** The research-branch controller, pinned at
   `b96752330d6d376a5bb0ba97cb6b2abe37d4e9eb`. Choosing it is not a launch
   authorization, and its 30 September 60-minute lifetime approval was for that
   campaign only.
2. **Authorization and cap:** the budget above, or a different one, including the
   60-minute lifetime per session.
3. **Region:** Ireland or London, the two the controller accepts, within the approved
   operator scope.

## After the run

Terminate on completion or failure, verify instance, volume and temporary-resource
deletion independently, and keep the original receipts. Record what ran, what
failed, the cost reservation against provider billing if known, the cleanup state
and the next evidence gap. A passing result is a reason to prepare a combined
candidate through the existing `candidate-sm86-*` path with its own evidence. It is
not a release, an enrollment or a deployment.
