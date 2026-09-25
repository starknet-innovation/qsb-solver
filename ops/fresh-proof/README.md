# Fresh sm86 proof cost admission

Status: implemented and locally tested; **no fresh sm86 launch or search yet**.
Native component/performance and proof-execution preparation gates remain pending.
This wrapper is not promotion approval or a mainnet activation path.

The user authorized at most USD200 for fresh-proof compute and associated
infrastructure, separately from the USD100 mainnet BTC pilot. `control.py` connects
`budget.py` to the committed one-shot AWS controller. Use this wrapper for every
fresh-proof infrastructure operation. The historical generic controller remains
available for separately authorized bounded validation; it rejects budget-bound
state for non-cleanup operations unless the budget guard is present. Direct
emergency cleanup remains possible even if ledger access is broken.

## Admission and ownership

The authoritative ledger binds one campaign UUID, frozen public request hash,
candidate source and immutable image digest. Never copy, reset or restore it to
increase available funds; all operators must use the same ledger and state paths.
The local owner lock excludes competing controllers; it is not cloud IAM fencing
against another machine or independently invoked AWS credentials.

Each transaction checks the original file identity and campaign authorization.
An immediate SQLite transaction reserves USD2 and records each prepare/arm/launch
attempt before that operation can reach the provider. USD20 remains unavailable
as campaign contingency. One unresolved intent blocks replacements. Crashes and
unknown provider outcomes retain their reservations, and an attempted operation
cannot be automatically replayed. Clean pushed source is required before admission.

Live AWS Pricing responses must uniquely match Ireland On-Demand Linux g5.xlarge,
gp3 storage and in-use public IPv4, with rate ceilings of USD1.123/hour,
USD0.10/GB-month and USD0.005/hour respectively. The allowance covers one full hour
of compute/IP plus80GB storage and USD0.50 for ancillary/cleanup costs. The existing
independent 25-minute cleanup deadline is unchanged. This is a conservative
allowance, not a provider-enforced invoice ceiling or a quote for a full proof.
Startup, idle time and delayed shutdown count. No fresh work is admitted if pricing
is missing, ambiguous, above its ceiling or stale.

Infrastructure name, IDs, deadline and schedule are frozen after preparation and
arming. Resource names must derive from the reserved client token. A crash before
preparation receipts are bound blocks further paid operations and requires
reconciliation. Never infer that the absence of a receipt means no operation ran.

## Cleanup and settlement

`cleanup` invokes the existing controller; `reconcile` independently reads AWS
identity, instances by both token and tag, volumes, security groups, schedules,
functions, IAM roles and instance profiles. An allocated instance must be terminal,
its root volumes and temporary resources absent, and its observed lifetime within
the reserved hour. Missing timestamps or an overrun retain the reservation and
block more work; they require separately reviewed cost reconciliation.

Late returned instance IDs attach to the original intent. An unknown launch with
no visible instance does **not** settle on absence alone. Explicit
InsufficientInstanceCapacity is recorded only from the actual launch error;
settlement then requires matching token/tag absence and zero temporary resources.
A cleanup receipt is persisted before settlement. The full USD2 allowance stays
charged even after a rejected launch; no automatic estimate-based refunds exist.
Thus the ledger may stop before the actual invoice reaches USD200. Any future
refund/accounting change requires verified evidence, not presumed savings.

The controller verifies cloud cleanup facts; the ledger additionally validates
their structure and identity. Neither controls AWS billing during provider failures.
No code here claims an absolute invoice guarantee.

## Commands and remaining gates

Initialize exactly once with a public campaign JSON containing `campaignId`,
`requestHash`, `candidateSource` and `imageDigest`. The source and digest are fixed
to the frozen sm86 candidate. Keep the ledger and all runtime state outside Git.

```sh
python3 ops/fresh-proof/control.py init --ledger /absolute/budget.sqlite --campaign /absolute/campaign.json
python3 ops/fresh-proof/control.py prepare --ledger /absolute/budget.sqlite --campaign /absolute/campaign.json --state /absolute/fresh-session/execution.json
# Only after successful prepare, then arm, then launch; never repeat uncertain operations.
# Cleanup and reconcile use the same arguments and original state.
```

The wrapper only prepares and bounds infrastructure. Before any actual fresh-proof
launch, complete native gates and the public-only execution/result-collection plan,
announce the current price, prepare fresh commitments and range accounting, and
verify cleanup is prearmed. No wallet key or recovery material belongs in the
host payload. No proof context or coverage may be borrowed from a spent fixture.

Local tests cover atomic reservation races, replacement-ledger rejection,
restart/unknown outcomes, exact limits, stale/expensive prices, owner locks,
late provider IDs, capacity rejection, terminal/volume checks, lifetime overruns,
mutable cleanup names and frozen scope changes. The actual controller guard is
tested to reject an unreserved preparation before its first cloud mutation.
Provider responses are mocked in these tests; they do not certify a live funded
search or the complete wallet/Core proof.

## Prepared sm86 session runner (not yet executed)

`worker/promotion/validation/run_fresh_sm86.py` is separate from the historical
sm89 runner. It checks the installed sm86 source/binary binding, validates the
public request with the installed handler, and exclusively creates a retained
result intent. Each active attempt is atomically persisted and fsynced before
invocation. Failed, interrupted or malformed results keep the active attempt
unresolved; the runner never retries it. Candidates stop the batch for independent
CPU verification. Neither a candidate nor a completed worker result directly
credits authoritative coverage.

`ops/aws-gpu-execution/host-a10g-fresh.sh` preserves the fixed image and container
isolation. After setup it requires at least 1,020 seconds before shutdown, gives
the container a 960-second outer limit, and forcibly removes it afterwards. The
runner admits a call only with 860 seconds of its 900-second session remaining,
covering the installed handler's 840-second timeout and termination grace.
The reserve is rechecked after checkpoint fsync, immediately before execution;
a late write produces a never-started bounded stop. Normal
short calls can yield multiple results; longer calls leave no room for another.
This does not shorten the range or change any cryptographic predicate.

Local tests use mocked solver calls. Native component and matched performance
gates, fresh wallet/fixture generation, host handoff/result collection, CPU-bound
coverage accounting, and full fresh Core proof remain pending. Do not allocate
fresh-proof infrastructure merely because these runner tests pass. Public batch
files and authoritative local intents must bind the same fresh campaign and budget
ledger before a launch. No historical wallet, commitments or coverage are reused.

Host results are retained in `public-result.b64`, with byte count and SHA256
emitted as a compact receipt. A collector must retrieve chunks and verify that
receipt before accepting the results; SSM stdout alone is not the result archive.

### Result collection validation

`results.py` validates ordered chunks against the host archive byte count and
SHA256, bounds decompression, rejects duplicate JSON keys and unexpected filenames,
and checks the submitted batch bytes, frozen binary binding and contiguous range
identities. A clean outcome must agree with the host exit code and candidate state.
Interrupted or uncertain outcomes remain reconciliation-required. The archive's
self-reported binding is consistency evidence; host/image attestation must still
be established independently before accepting an execution.

`persist_collection` validates first, then exclusively creates a new evidence
directory. It fsyncs the archive, submitted batch and extracted public files,
writes a hash inventory/receipt last, and fsyncs the directory. Existing or partial
directories are never overwritten. These routines do not invoke AWS, submit work,
terminate instances, verify cryptographic candidates or mutate coverage. The SSM
transport, cross-host reconciliation and authoritative CPU verification/coverage
integration remain pending. Local archive tests do not certify remote retrieval.

### Resuming public SSM result reads

`collect.py` consumes saved execution and original host-command receipts; it never
starts a solver. It reads the original invocation first and waits if that command
is still pending. Terminal commands must contain exactly one archive hash/length
receipt. A collection context freezes the instance, original command and submitted
batch hash. Each bounded read has a durable intent before `send-command`; an
uncertain submission without a saved command ID requires manual reconciliation.
A saved read command is polled on subsequent runs, never replaced automatically.

```sh
python3 ops/fresh-proof/collect.py --execution /absolute/session/execution.json \
  --command /absolute/session/host-command.json --batch /absolute/session/batch.json \
  --collection /absolute/session/collection
```

The CLI uses only profile `snf`, account `905846953990`, region `eu-west-1`.
Run it again to poll a returned pending command ID, using the same inputs. An
already-created evidence directory is not overwritten, including after a partial
local write. Inspect its collection receipt or reconcile the failure. Do not
interpret an observation timeout as a stopped original execution. Cleanup remains
mandatory through the execution controller and independent deadline; this collector
does not terminate instances or settle the budget. Local tests include executing
the exact generated read command against public bytes, but AWS transport remains
mocked until a future authorized session. No fresh-proof launch is enabled by this
collector alone.

The CLI explicitly sets `AWS_MAX_ATTEMPTS=1`, with bounded connection, response
and process timeouts; an underlying CLI retry must not duplicate `send-command`.
The original terminal invocation is retained alongside metadata for provenance.
Tests cover multiple chunks with distinct IDs and a pending middle read, not only
single-chunk archives. These safeguards concern collection commands only; they do
not attest the solver or permit replay of an uncertain paid session.

### Fresh local regtest wallet preparation

`prepare_wallet.py` creates a new disposable wallet and new QSB commitments from
four hash-pinned public app reference files. This is the user-authorized local
wallet proof, not an Xverse signature demonstration. It rejects existing output
directories and changed reference sources. Private key and recovery JSON remain
mode0600 under a mode0700 `private/` directory; stdout contains only a public
preparation receipt. Never upload that directory or its parent as a bundle.

```sh
python3 ops/fresh-proof/prepare_wallet.py --source /absolute/app/public/qsb \
  --destination /absolute/new-local-regtest-wallet
```

Only `public/public-request.json` may be passed to the offline fixture preparer.
The mainnet-formatted nested SegWit address is a compatibility detail of that
regtest-only schema: **never fund it on mainnet**. This command does not fund,
search, assemble, sign or broadcast. Keep any partial preparation for inspection;
do not rerun into it, print its contents or substitute an older wallet/commitment.

### Independent CPU evidence check

`verify.py` revalidates the collection archive/inventory and externally frozen
public fixture hash. It re-exports the exact stage parameters, including the
subset pin context, and compares both bytes and hash to the submitted request.
Candidate membership is checked before independent CPU puzzle verification.
The six CPU reference sources are fixed by hash and copied into a fresh temporary
directory; each call runs in a new isolated Python interpreter, avoiding shared
cwd/module state and existing bytecode caches.

```sh
python3 ops/fresh-proof/verify.py --collection /absolute/session/collection/evidence \
  --fixture /absolute/campaign/public-fixture.json --fixture-sha256 FROZEN_SHA256 \
  --reference /absolute/campaign/cpu-reference --output /absolute/session/cpu-verified.json
```

An uncertain execution cannot be published through this command. Unexpected CPU
rejection stops for diagnosis. A verified hit or DER-only hit is never eligible
for whole-range credit; no next attempt is inferred across it. All receipts still
say `grantsRangeCredit=false`: the durable coordinator must separately verify
admission, attested execution identity, provider termination and context before
writing coverage or advancing the stage. The fixture digest must come from the
previously frozen campaign, not be recomputed as a workaround for changed inputs.
Mocked tests and an actual pinning-parameter export confirm the local verification
path; they are not a fresh GPU search or solved proof.

### Atomic proof journal (local API; live coordinator wiring pending)

`journal.py` adds proof state, frozen batches, command intents and coverage to the
**same** existing budget database. Initialize once before any reservation; never
reset a campaign to retry. Registration binds the current stage, exact next attempt,
frozen manifest and verified pin before launch. Budget launch admission now requires
that registration whenever a proof journal exists. The command send intent commits
before the single host submission; an uncertain send cannot be claimed again.

Publication takes a trusted verification callback which must re-read the frozen
collection, run the pinned CPU verifier and independently bind host/image/command
provenance. This callback is still an integration responsibility, not permission
to trust a provider-supplied JSON verdict. The journal requires the allocated budget
session to be settled after independently verified cleanup. It atomically records
empty-range coverage and advances a verified solution to the next stage. Hits
never earn whole-range credit; DER-only results block for explicit reconciliation.
All three solutions stop further budget reservation. Unknown host outcomes block
new work even after infrastructure cleanup. An explicit capacity rejection can
close a registered batch only after the existing budget reconciliation confirms
no allocation and cleanup; it neither credits a range nor refunds the allowance.

Local regression tests cover lost sends, reopen/duplicate publication, wrong
fixture/command/pin context, pre-cleanup rejection, atomic rollback, all three
stage transitions, solved-budget refusal and capacity rejection without skipped
coverage. Verifier/provider observations are mocked. No live proof ledger was
initialized or mutated by these tests, and no GPU was allocated. The executable
end-to-end coordinator and fresh proof remain pending.
