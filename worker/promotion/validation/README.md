# Historical exact-binary validation batch

This is the original sm89 candidate batch, retained for reproducibility. It is not
the later sm86 release gate or a current launch plan. See [current release status](../../../docs/README.md)
and the [completed A10G results](../../../docs/promotion/2026-09-26-a10g-performance.md).
Do not restart spent-fixture replays from this record.

`benchmark.py` validates the candidate-20260925-1 subset executable against its
published SHA256, then downloads and checks the historical subset executable
extracted from the attested v0.1.0 OCI image
`sha256:badfcac297db6c242cf0e91e78fe294fa900d3c59f363258ec6d0d502162c755`.
The validation-only baseline release asset is not a new solver release.

Fixtures contain only public GPU parameters. Benchmark fixtures were exported by
the separate qsb-app CPU reference with synthetic nonexistent 00/11 outpoints,
SegWit/Taproot output layouts, and both subset stages. Each runs three alternating
baseline/candidate samples of 2^31 ranks on the same GPU. Wall times include process
startup. Results must pass `summarize.py`; incomplete, duplicate, wrong-range or
wrong-binary measurements are rejected, and any new benchmark hit requires separate
CPU verification before the summary is accepted. The batch permits 20 minutes, with 120 seconds per process and process-group
termination on timeout. An external 30-minute resource deletion watchdog is required.

Two historical one-candidate replays require the expected indices, recovery ID and hash choice. They test
the new binary's hit path; they are not a fresh search, independent CPU verification
of new hits, a withdrawal, or permission to reuse the original spent fixture.

Run only in an isolated candidate OCI filesystem on one GPU. This script performs
no signing, transaction broadcasting, durable coverage credit, or production enrollment.

### Corrected pinning full-hash differential preparation

`corrected_pinning_trace.py prepare --app /reviewed/qsb-app --fixture
 tests/fixtures/cmsverify-v1 --output /new/public-plan.json` checks all fixture and
CPU-reference source hashes before constructing 80 expected recovered-key hashes
from complete corrected transactions. The public synthetic fixture uses
nonexistent outpoints. The matrix covers both sequence endpoints and four-lane
locktime windows crossing 64/128/256 boundaries plus the supported final window.
Pinning FindAndDelete removes the pin signature from the corrected full script;
no precomputed GPU digest or exporter midstate supplies the expected sighash.

`instrument --source /reviewed/repaired/pinning.cu --output
 /new/diagnostic/pinning-trace.cu` inserts one full-hash print before the unchanged
predicate. It refuses changed/ambiguous anchors and existing output. This is a
**diagnostic derivative**, not a replacement release executable. Preserve the
printed diff, complete source-tree hashes, compiler/flags, exact release binary,
diagnostic binary and immutable image identities before any native run.
`verify_trace` requires exactly the planned `(sequence, locktime, recovery-id)`
map; missing, duplicate, extra, malformed and mismatching lanes fail closed.

This preparation does not allocate hardware, compile CUDA, launch a solver or
credit any range. Future native collection must run the ten four-locktime cases
through the traced executable and the unchanged release executable separately,
with `single_hash`, `seq_count=1` and `lt_count=4`. Validate normal exit and exact
completion, preserve logs/hits, and independently CPU-check any actual hit. A hit
may make the unchanged kernel return before printing its other recovery branch;
that is a failed diagnostic inventory, not permission to omit an expected hash.
Use the existing bounded watchdog and one-shot receipts for a future run.

Passing this diagnostic would cover sampled pinning recovered-key arithmetic on
the corrected transaction. It would not prove exhaustive coverage, a real
pinning hit, exceptional cases, final-binary internal hashes, fresh withdrawal or
external miner acceptance. Those remain separate qualification requirements.

### One-GPU fresh pinning search

`fresh_pinning_search.py` runs only the pinning stage against a public
`export-pinning.json` from qsb-app's offline fixture harness. The six public CPU
reference modules are separately staged with an explicit filename→SHA256 JSON
manifest. Only public exports and those modules may reach the GPU host; never
stage recovery JSON, a wallet, or the full local proof directory.

Supply `--public`, `--binary`, `--binary-sha256`, `--reference`,
`--reference-hashes`, `--output`, and an absolute `--deadline`. The first run
requires a deadline no more than 23 hours ahead; resume binds that same deadline,
request, binary and CPU source hashes. Runtime checks require exactly one GPU.
This program provisions nothing and is not permission to spend: the operator must
independently enforce the campaign's aggregate GPU-hour and total-dollar budget,
pre-arm host and control-plane termination, and use the approved immutable image.

The runner re-exports parameters with the independent CPU reference before GPU
execution. It uses the existing `ranked-v2` range partition and direct executable
arguments, records and fsyncs the intent before compute, and preserves each
range's logs and result. Per-range compute has a maximum 840-second timeout; the
runner stops launching ranges with less than the timeout plus 90 seconds left.
Every reported hit is checked for assigned-range membership and independently
CPU verified. A verified pin writes a public solution and stops; transfer only
that public solution to the local fixture harness to export the subset rounds.
No stage advancement or withdrawal assembly occurs remotely.

Failed, interrupted, missing-result or uncertain intents block resumption.
Completed records must retain their exact result hash and work partition before
the next attempt is selected. Never edit records or blindly restart a failed
range. Completion of a pinning range does not solve the full withdrawal. Preserve
and retrieve all journals before terminating the isolated host.

Each range uses **two explicit commands**: `prepare` persists the next intent
without launching a GPU process; the host wrapper must successfully archive that
public intent off-host before `execute --attempt N`. Execute claims that exact
prepared record locally and can run it only once. After execute, archive all
public logs/results/journals off-host and require upload success before preparing
the next range. Keep presigned upload URLs exclusively in the trusted host wrapper,
never the container or public receipts. A remotely recovered prepared intent is
**uncertain**, not authorization to execute again: reconcile it first. This
protocol preserves coverage and unknown attempts if the watchdog deletes EBS.
No continuous loop is built into the container runner.

Execution additionally requires `--intent-ack-dir`. After fsyncing the
`compute-intent` record and before starting the binary, it waits at most 60 seconds
for `{binding}-{attempt:08d}.json` in that directory. The trusted host supervisor
must first upload a snapshot containing those exact record bytes, then atomically
write an acknowledgement with exactly `recordPath` (`range-NNNNNNNN/record.json`),
`recordSha256`, and `binding`. A missing or mismatching acknowledgement prevents
compute and leaves a failed intent. The campaign binding distinguishes stages or
fixtures even when attempt numbers repeat. Credential URLs stay outside both
mounts. Public logs are capped at 1 MiB per process (checked during execution),
and preparation stops before retained snapshots approach 256 MiB. Completed
records require their retained log hash as well as their result hash on resume.
