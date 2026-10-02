# One-shot optimized A10G gate

This documents the controller shipped on `main`, with its original Ireland scope
and 25-minute deadline. Later research-branch controllers and campaign permissions
do not change this implementation. The recorded gate is historical; do not restart
it from these instructions. See [release status](../../docs/README.md).

Adapted from the completed qsb-app AWS execution controller at c8c6f21833798900ae1e6a21f0b5d10d2adab291.
This operator-specific experiment uses one g5.xlarge in an explicitly authorized region (eu-west-1 or eu-west-2). No app activation.
Before launch: verify price, effective quota, zero other test GPUs, clean pushed
controller source and exact candidate attestation. Prepare creates dedicated SSM-only
host access and a tagged-instance cleanup role. Arm records an absolute 60-minute
deadline; the independent Scheduler invokes cleanup in the following full minute
(to avoid an early minute-precision invocation). Guest shutdown shares the deadline.
Control-plane latency is not a guaranteed billing ceiling. Terminate immediately
on success/failure and verify instance, volume and temporary-resource removal.

Never reuse a state file or retry an uncertain launch; reconcile its token.
Record the returned root volume before setup. A fresh `run_a10g.py` output file is
a one-shot execution marker. Bind-mount the committed public validation directory
read-only into the attested candidate container, run with network none, GPU access,
read-only root, dropped capabilities, temporary /tmp and only a results mount.
Use a 12-minute outer timeout and the script's 10-minute deadline. A run must never
start with less than 13 minutes remaining before shutdown.

The gate checks two historical subset hits and 16 small/sampled ranges. It is not
full domain enumeration, independent CPU differential, live Batch certification,
pinning validation or a fresh withdrawal. Preserve earlier candidate2 evidence.
All resource config/state and receipts remain outside the Git checkout. No secrets
or user wallet files are accepted by this gate.

## Readiness before staging

SSM Online may precede cloud-init completion. Run the committed `ready.sh DEADLINE`
through SSM before creating the gate directory or issuing the one-shot compute
command. It waits at most three minutes for the boot marker and both systemd
services, while requiring 18 minutes remaining for image setup plus the gate.
A readiness failure terminates the experiment without starting the solver. Do not
reset the fixed deadline. The historical readiness attempt recorded at 17:13 UTC failed ten seconds before the boot
marker existed; no bundle was staged or solver executed, and no rerun was issued.

## External operator scope

Set `QSB_AWS_OPERATOR_CONFIG` to an absolute JSON file outside every Git checkout.
The file contains exactly `account`, `profile`, `region`, `ami`, `subnet`, and
`vpc`; do not put credentials in it. For example, use your approved values in:

```json
{"account":"123456789012","profile":"operator","region":"eu-west-1","ami":"ami-00000000","subnet":"subnet-00000000","vpc":"vpc-00000000"}
```

These are placeholders, not launch configuration. The controller verifies STS
against the configured account and restricts the region to Ireland or London. Regional AMI/network values must be independently verified; existing execution state cannot change region. New external
execution receipts freeze the configuration; resume rejects changes or legacy
state without that binding. Never mutate an old receipt to bypass that check:
reconcile prior resources using their original committed controller and scope.
No prior experiment is authorized to relaunch by this configuration change.
Keep original private operational receipts outside Git; public evidence uses
hashes and cleanup counts. Earlier branch history remains unchanged and must be
considered separately before any requested history rewrite.

## SSM shell and early-failure collection

Use the committed `operate.py STATE_DIRECTORY MODE` adapter for future scoped
experiments (`record`, `ready`, `send`, `poll`, `terminate`). Do not copy historical
operational adapters into a new run. `send` wraps the host template in an explicit
`exec /bin/bash -s` with a quoted, collision-checked heredoc: AWS-RunShellScript's
outer `/bin/sh` must never interpret Bash-only options, arrays or conditionals.
The literal wrapped command and its hash are saved before the single SSM send.
An existing send intent is still non-retryable until reconciled.

On terminal SSM failure, raw output is saved even if the host failed before emitting
its result envelope. Missing, duplicate, oversized or malformed result envelopes
produce a separate collection-error receipt; instance termination remains in the
`finally` path. A result-envelope error never counts as a successful GPU gate.

The 30 September allocated experiment failed at its first `set -o pipefail` under
`/bin/sh`; no GPU test ran. Its instance, root volume and temporary infrastructure
were independently confirmed deleted. Original execution receipts remain unchanged.
Six local transport/operator regression tests cover the shell failure, literal
payload preservation, pipeline failure status, result validation, durable send
intent and termination after missing results. These tests use inert local Bash
and mocked AWS responses, not a new cloud execution. The capacity watcher remains
paused; correcting this adapter does not automatically authorize another paid run.

## Extended multi-region capacity watch

The operator authorized sequential London and Ireland capacity checks and a maximum
60-minute host lifetime on 30 September. Each new scope keeps one g5.xlarge,
independent cleanup and the same absolute guest deadline. Never extend an active
deadline. Terminate immediately when the prepared gate finishes or fails. Existing
25-minute receipts retain their original deadlines. A longer lifetime is not an
advance capacity reservation and does not change the 12-minute outer compute limit
or authorize additional paid experiments after an allocated attempt.

## Large public validation results

The adapter also accepts a single `QSB_PUBLIC_RESULT_META` line binding the byte
length and SHA256 of `/var/tmp/qsb-a10g-results/public-result.b64`. It reads at most
2 MB of encoded output in 18 KB SSM chunks, checks command/instance identities,
then verifies the assembled checksum before decoding at most 8 MB of flat text
files. Every read submission has a durable intent. An uncertain send is never
retried automatically. Collection must leave two minutes before host shutdown;
collection failure retains raw terminal evidence and still requests termination.
These transport checks do not validate solver output or grant range credit.

The pinned CUDA development base lacks Python. The validation-only Dockerfile at
`experiments/generic-sha-vector/Dockerfile.validation` adds the interpreter needed
by the Python runners. A build is not an approved runtime: record and verify its
immutable registry digest, dependency checks and host handoff before allocation.
Do not replace the frozen solver binaries with artifacts built in that image.
