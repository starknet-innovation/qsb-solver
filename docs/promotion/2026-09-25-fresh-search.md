# Fresh locally signed regtest proof — in progress

Status: **HOLD; full proof incomplete**.

The user authorized generating a new disposable local key for the fresh proof.
Fresh commitments and a new offline Core 30.2 regtest fixture were created for
request `ec9605bc-8fb0-47a6-b024-7f0637eb1de7`. No old fixture was reused. The
private key and recovery material stay outside Git and outside the GPU payload.
This will be a locally signed proof, not an Xverse signing test or external miner
inclusion test. There is no mainnet authorization.

The search uses the already tested candidate2 image
`sha256:9e86d94a66d7893e31d8e8d6bec7ddbc9b59f47f09e2f7a6015679fd95ab8b52`
from source `bef76bf9aec123d95fdff53fb839a0c44f378927`. The separate public-only
batch runner was committed and pushed at
`59d18d5af644c1eaf2296f9d2fe2c14a958df1a1` before execution. No solver binary or
predicate changed for the fresh search.

## First bounded batch

At 10:31 UTC on 25 September, the worker completed pinning attempts 0–17 without
hits. Its terminal status was `bounded-stop`, with no active attempt. The saved
public result SHA256 matched the worker's terminal log:
`f9ee6029b6d10d2d09877b69b00cd96416be7d464d6b8cb7520695a6034c0479`.
Independent local reconciliation re-exported the CPU parameters, checked frozen
manifest/source/range identities, and preserved the next attempt as 18.

The pod was deleted and a provider read confirmed zero pods before the next
batch. GPU execution total was 508.425 seconds; at $0.74/hour this is approximately
$0.105 of execution time, excluding startup, idle time and storage. It is not an
invoice or a whole-proof cost estimate.

## Second bounded batch

At 10:41 UTC, attempts 18–35 also completed without hits. Terminal status was
`bounded-stop`, with no active attempt. The result SHA256 matched the worker log:
`a52c24d8fd981d7621fb3dcf745327ea55a06a470c4658f4094ad78e1f066e57`.
Local reconciliation passed with the shared membership checker. The second pod
was deleted and zero pods confirmed; both historical endpoints still had
minimum/maximum workers zero. Cumulative complete ranges: **36**. The preserved
next attempt is **36**, with the same fixture, manifest and public parameters.
No pin has been found, no helper transaction signed, and the fresh fixture
remains unspent. These are search checkpoints, not a completed proof.

## Candidate and completion handling

The public membership checker rejects pins outside their assigned sequence and
locktime rectangle, and checks raw subset lexicographic rank before the CPU
reference converts indices into HORS order. Tests cover all subset range edges
and sampled ranks (10,662 combinations), exclusive pin boundaries, malformed
records, and every record in a returned file. Membership alone is not a
cryptographic verdict: each hit still requires independent CPU verification.

Read-only independent review confirmed that the frozen single-slot pinning and
generic ranked subset host loops finish their assigned ranges even when they
publish candidates. The CPU verifier recomputes alternate recovery branches.
Only successful complete ranges can advance coverage; failed or uncertain work
requires provider reconciliation, with no automatic retry. A per-container
restart marker is supplemented by local durable batch intents and saved IDs.

Each batch uses one GPU, an external deletion watchdog under 30 minutes, and
terminal result collection before deletion. All three puzzles must be solved and
CPU-verified before local one-time assembly/signing and exact-byte Core acceptance.
No completed fresh withdrawal, promotion approval, app enrollment, or mainnet
readiness is claimed here. Historical completed endpoints remain disabled.
