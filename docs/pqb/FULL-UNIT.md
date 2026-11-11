# Full-unit PQB validation plan

Status: **prepared, not natively executed; candidate remains HOLD**. This checks public synthetic
unit durations and accounting. No partition, search version or CUDA flags change.

## Work and acceptance

Run one stage per fresh session. The controller arms a fixed 25-minute deadline before launch.
All three largest units plus setup do not fit safely into one session; never extend a deadline
or replay an uncertain command. The bundle finds the largest unit in each committed partition
(all three are attempt 0):

| Stage | z-blocks | Estimated seconds from the old component rate |
|---|---:|---:|
| pinning | 16,800,000,000 | 486 |
| round0 | 7,141,805,239 | 502 |
| round1 | 15,282,749,791 | 486 |

These are estimates. Each request uses `pqb-ranked-v2`, the production 24-bit gate and DER-shape
filter. There is no CLI option to shrink a unit or raise the 840-second worker timeout. Before
the full unit, all 11 existing small independent-reference cases must pass on this binary within
a 60-second preflight allowance, including boundary, multi-batch and exceptional-point cases.
The short matched-throughput comparison is not repeated.

A stage passes only if the bound worker returns `completed` / `range-complete`, its retained
completion line describes exactly the requested unit, batch z-block accounting matches,
candidates are unique and independently re-derive inside the unit with the gate and DER shape,
and the gate count meets the recorded six-sigma sanity bound. Worker plus independent checking
must finish within 840 seconds, leaving margin under a 900-second job limit. The device must
report an A10G; emulation cannot produce a native pass. Timeout, overflow, malformed output,
identity mismatch or a failed preflight fail the run. Nothing retries automatically.

Gate statistics and worker counters are diagnostics, not independent completeness proofs.
The full-unit reference checks emitted hits only; the small cases compare complete hit sets.
Strict DER/consensus verification, transaction meaning and the application's verifier remain
separate gaps. Necessary-condition candidates do not constitute a solved stage or spend.

## Prepare without hardware

Run local checks and CI first. From a clean, pushed checkout, download
`pqb-measure-binaries-sm86` from that exact commit's successful **push** workflow run. Do not
reuse the old `266f4a0` binary/receipt for current source.

```sh
python3 -m unittest discover -s tests -v
python3 scripts/prepare_pqb_full_unit_bundle.py /absolute/artifact /absolute/new-bundle
```

The builder rejects dirty/unpushed source, mismatched artifact commit/hash/source lock, a
non-sm86 receipt, actual source bytes differing from the lock, or inconsistent contract vectors.
It binds the binary, exact handler/scheduler, public fixtures, development reference, contract
and plan in `SHA256SUMS`. Store the printed checksum-list hash and tarball hash before staging.
The reference and fixtures stay outside the worker image. Its optional `evidence_directory`
Python argument retains the public work directory; requests cannot select it.

The immutable CUDA runtime is the combined image from the
[component receipt](2026-11-11-a10g-measurement.md), used only as a runtime. Solver and handler
come from the bundle. These are CI artifacts, not attested releases. A later image rebuild
needs its own identity/evidence review.

## Authorized host operation and collection

Follow [the controller procedure](../../ops/aws-gpu-execution/README.md). Before paid submission
persist fresh request identities and budget reservations, verify account/price/quota, previous
cleanup and no other test GPUs, and use committed/pushed source. Record the allocated volume.
The independent cleanup and guest shutdown timer must both be armed. Run `ready.sh` through
SSM first. Stage the verified bundle and committed host script, with public inputs only.

```sh
bash /absolute/committed/host-pqb-full-unit.sh \
  /opt/qsb-pqb-full-unit /var/tmp/qsb-pqb-full-unit-results \
  DEADLINE_EPOCH SHA256SUMS_HASH pinning
```

Select exactly one of `pinning`, `round0`, `round1`. The host checks both shutdown safeguards,
all bundle hashes and a fresh result directory. After pulling the pinned runtime it requires
at least 1,100 seconds until the existing deadline. Its isolated container has no network, a
read-only root and a 1,000-second outer timeout. It forcibly removes the named container on
exit and packages receipts even on setup failure.

Collect `public-result.b64` (gzip/base64 JSON map of relative paths to public file contents),
verify its returned byte count/hash and preserve the original archive before decoding. Retain:

- Deadline, bundle hash, stage, image pull log, device/driver identity, exit code and gate log.
- `unit/result.json`: source/runtime/binary/contract identities, all preflight outcomes, unit
  status, timing and retained-file hashes.
- `unit/request.json`, `worker-result.json`, `unit.json`: request, worker response, range
  accounting and independently checked candidate nonces/digests.
- `unit/work/P.txt`, `compute.log`, `hits.txt`: original public problem and native outputs,
  including interrupted or failed work.

An outer kill may leave `status: incomplete`; count it as failed/incomplete work and reconcile
before another session. Report worker invocation, independent checking and host/session cost
separately. Native setup/batch events remain in the log; overlapping device timers must not be
summed into pipeline time. Boot, image pull and SSM overhead are outside worker timing.

Terminate promptly after collection or failure. Independently verify instance, recorded volume
and temporary-resource deletion, saving fresh reconciliation separately. Estimate cost from
actual launch/termination times and verified pricing; distinguish it and budget reservations
from provider billing. Review all three native receipts before freezing the provisional
contract. Next is qsb-app's consumer and a complete public-data pipeline. Publication, descriptor
enrollment and deployment remain separate decisions.
