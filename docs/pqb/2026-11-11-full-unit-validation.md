# Native full-unit validation, 11 November 2026

Status: **all three largest units passed; candidate remains HOLD**. These are public synthetic
unit-duration and accounting results, not a full solve, complete-pipeline throughput, release
image attestation, qsb-app enrollment or deployment.

## Artifact and execution

- Full-unit source/harness: `0a25ec4a31eeabd0d9e98ee929415baea1b7c75d`.
- Ranked binary: `0e811c59de2d36f66142a6f65393c55a64e0e37c7eb40df4251f86b713ef3d82`,
  from successful push CI run [43075207523](https://github.com/starknet-innovation/qsb-solver/actions/runs/43075207523),
  artifact `13880507991`. Its build receipt records nvcc 12.8.93 and
  `-O3 -std=c++17 -arch=sm_86`, with the imported/adapted sources locked by hash.
- Contract: `pqb-ranked-v2`, canonical SHA-256
  `5217daa6415b83dcce2d85159130df4994ab0e9bb67910c7bdf00e5804f4ee71`.
- Runtime only: `ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48`.
  The binary, bound handler/scheduler and development reference came from the read-only
  validation bundle, not from that historical image. These are CI artifacts, not release binaries.
- Three fresh on-demand `g5.xlarge` instances, sequentially, in eu-west-1b: NVIDIA A10G,
  driver 580.126.09, reported memory 23,028 MiB. Fresh instances do not establish that the
  provider assigned three distinct physical cards.
- Each session used the clean/pushed controller, a fixed 25-minute pre-launch deadline,
  independent cleanup schedule and guest shutdown timer. The isolated container had no
  network, a read-only root, dropped capabilities and a results mount. No deadline was extended.

The [plan](FULL-UNIT.md) selects the largest unit of each partition, all attempt 0. The
production 24-bit gate and DER-shape filter were enabled. Each unit ran through the bound
handler with its ordinary 840-second timeout, after all 11 small independent-reference
correctness cases passed on that session's GPU.

## Measurements

| Stage | z-blocks accounted for | Worker seconds | Worker + checking seconds | Gate hits | Candidates re-derived |
|---|---:|---:|---:|---:|---:|
| pinning | 16,800,000,000 | 490.946 | 490.972 | 71,956 | 0 / 0 |
| round0 | 7,141,805,239 | 504.683 | 504.699 | 81,897 | 0 / 0 |
| round1 | 15,282,749,791 | 487.286 | 487.318 | 58,504 | 1 / 1 |

Every worker response was `completed` / `range-complete`. The retained completion report
named exactly the requested unit, summed batch z-blocks matched it, the candidate lists were
unique, and gate counts passed the recorded sanity check. Round1's one candidate independently
re-derived inside the range and satisfied the 24-bit gate and DER shape. It remains a
necessary-condition candidate: strict DER, sighash policy, recovery/consensus checks and
transaction meaning were not certified by this check.

The earlier size predictions were 486 / 502 / 486 seconds. The measured invocations fit below
840 seconds on these instances. This is evidence for these units and hosts, not a guarantee
about every host or an actual 900-second AWS Batch/application job.

Each unit started a new grinder process after the small GPU preflight. Worker timing includes
that process's startup, device work, transfers, output and handler accounting. Independent
candidate verification was timed separately (about 8.8 ms for round1's one hit); the checking
column also includes receipt parsing/writes. VM boot, image pull, SSM and Python harness
startup are outside worker timing. Native setup and batch timers remain in the full logs;
overlapping device timers are not summed into a pipeline time. No matched baseline was run
for this full-unit assessment.

## Source/evidence changes during the campaign

An earlier full pinning unit passed at `a7d36af7d754d5cb06d3cf3f4583fac48d49ad1a`, binary
`f884bebdcbd177a41b554a798adb4756f5778151a112a9525f398086ef500b19`, in 491.796 seconds.
When review tightened round slot-spacing validation, the campaign pinned `0a25ec4` and used
its fresh CI artifact for all three stages. The older successful receipt is retained separately;
it is not an attestation of the newer binary.

Later review at `ca9ca959613bee7f094b73c44d858b387b031694` tightened duplicate-output/event
checks, retained failed preflight artifacts and added two filter-positive cases. Its successful
push CI run [43081715151](https://github.com/starknet-innovation/qsb-solver/actions/runs/43081715151),
artifact `13885625408`, produced the **byte-identical ranked binary** above. CUDA source,
source lock and compile flags did not change. The later output guard rejects duplicates that
these retained outputs do not contain; its injected-duplicate test passed locally.
An offline replay through the current problem/range parser accepted every retained unit,
and independently re-derived the production candidate again; its separate receipt is retained.

The full units and their 11-case preflights were executed at `0a25ec4`, not with the later
handler binding or expanded 13-case harness. The two new pinning filter-positive cases passed
under CPU emulation/CI and remain **unexecuted natively**. A supplemental bundle was prepared,
but its full measurement profile's 780-second remaining-time requirement could not be assured
after the last unit's collection. No supplemental compute command was sent, no deadline was
extended and no new hardware was allocated for it. Round1 does provide native production-gate
filter-emission evidence; it does not replace those specific pinning cases. The latest local
suite passed 150 tests with one existing skip.

## Cost and cleanup

Fresh authorization in the current chat permitted paid hardware as needed. An operational
reservation of $2 per session was recorded before submission; the earlier component session's
$5 cap was not reused. Four GPU instances were launched, one at a time: the earlier `a7d36af`
pinning assessment and the three primary units above. All four completed successfully.

Estimated compute is **$0.90**, using the AWS Pricing API's $1.123/hour Linux on-demand Ireland
rate and provider-reported launch-to-user-shutdown intervals. This includes the older pinning
run and instance startup/collection time. Storage, public IPv4 and transfer/control-plane costs
are outside that compute estimate. Provider billing was not read; reservations are not billing.
The earlier $0.13 component measurement is a separate historical session.

One setup attempt failed before any GPU submission: the AWS MCP transport converted inline
Lambda ZIP bytes to text and AWS rejected the cleanup function. That attempt's resources were
removed; an uncertain security-group delete was read back before explicit deletion. Subsequent
sessions uploaded the exact cleanup ZIP via S3 and checked the returned code hash.

Results were collected and hash-checked before instance termination. Force termination with
OS shutdown bypass was used after archiving; EC2 still took minutes to finalize deletion.
Independent checks verified all four instances terminated, all recorded volumes deleted, and
no campaign security group, role, instance profile, schedule, function or staging bucket left.
There are no pending submissions, remaining reservations or resources to clean up. Original
operator receipts remain outside Git; fresh reconciliations are retained separately. An older
terminated instance aged out of the final EC2 listing, so its earlier saved termination/deletion
reconciliation is retained as well.

## Retained evidence and next gap

[evidence/full-unit-2026-11-11](evidence/full-unit-2026-11-11) contains the manifest, actual build
receipts/binding, cost/cleanup summaries, the four complete compressed public receipts and
their extracted result summaries. Each `receipt.json.gz` is the original gzip payload of the
host's `public-result.b64`: a JSON map from relative filenames to public text contents. The
manifest binds both its gzip bytes and original base64 bytes. It includes exact requests,
problems, worker responses, native logs/hits, device metadata and every small-case result.

Gate statistics and worker counters do not prove complete coverage. Full CPU enumeration,
a full solve/spend, application transport and matching cross-repository vectors were not
executed. The zero-sighash exceptional branch still lacks its own planted test, and other GPU
models remain unmeasured here. Review these receipts and consumer compatibility before a
contract freeze; then validate the complete public-data pipeline. Publication, descriptor
enrollment and deployment remain separate actions. The candidate stays HOLD.
