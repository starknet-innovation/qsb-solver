# One-shot optimized A10G gate

This documents the controller shipped on `main`, with its original Ireland scope
and 25-minute deadline. Later research-branch controllers and campaign permissions
do not change this implementation. The recorded gate is historical; do not restart
it from these instructions. See [release status](../../docs/README.md).

Adapted from the completed qsb-app AWS execution controller at c8c6f21833798900ae1e6a21f0b5d10d2adab291.
This operator-specific experiment uses one g5.xlarge in eu-west-1. No app activation.
Before launch: verify price, effective quota, zero other test GPUs, clean pushed
controller source and exact candidate attestation. Prepare creates dedicated SSM-only
host access and a tagged-instance cleanup role. Arm records an absolute 25-minute
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
against the configured account and restricts the region to Ireland. New external
execution receipts freeze the configuration; resume rejects changes or legacy
state without that binding. Never mutate an old receipt to bypass that check:
reconcile prior resources using their original committed controller and scope.
No prior experiment is authorized to relaunch by this configuration change.
Keep original private operational receipts outside Git; public evidence uses
hashes and cleanup counts. Earlier branch history remains unchanged and must be
considered separately before any requested history rewrite.

## MCP transport request planner

`mcp_plan.py` is a separate, opt-in operator planner for AWS MCP `call_boto3`.
It does not call AWS or shell the AWS CLI. It emits PascalCase API operations
and their exact parameter objects after persisting each phase's intent. The
legacy `control.py` remains unchanged. Both require clean, pushed source and
external operator configuration. A per-state advisory lock serializes planner
transitions. The operator must still execute each recorded mutation at most once;
reconcile any uncertain response instead of repeating it.

Use a **new external state file**. `prepare --evidence caller.json` expects the
actual STS caller-identity result. Execute the nine recorded prepare calls in
order. Save a corresponding ordered receipt array with `success: true`,
`operation`, `requestSha256` (SHA256 of the canonical JSON call, sorted keys and
compact separators), and `result`, all derived from successful MCP responses.
Then run `prepared --evidence receipts.json`. These envelopes are operator
records, not cryptographic cloud attestations; retain original tool receipts.

`arm` freezes the 25-minute deadline and cleanup ZIP hash. `Code.ZipFile` in the
emitted JSON is a base64 transport representation; decode to SDK bytes at the
MCP boundary. Wait for the Lambda to be Active and its exact hash/configuration
to match before executing the scheduled-cleanup call. Do not extend or re-arm.

`launch --evidence preflight.json` requires fresh (at most 60 seconds old)
`observedAt` epoch seconds and actual readbacks named `caller`, `lambda`,
`schedule`, `quota`, `instances`, `activeGpus`, `images`, and `groups`.
`instances` must be the token-filtered EC2 response; `activeGpus` must contain
all active GPU experiments in the approved account/regions (not just this token).
The Lambda readback is `GetFunctionConfiguration`; the other fields retain
AWS response envelopes. A successful plan persists `launch-intent` **before**
returning the sole `RunInstances` request. It can never plan a second launch.
Immediately retain the actual instance ID and root volume IDs in the external
receipt, and independently confirm boot termination and watchdog settings.

The planner does not install a candidate or run tests. Use a separately reviewed,
committed gate pinned to the current immutable candidate; historical host scripts
hardcode old images and are not suitable for a new candidate. Preserve the
readiness and 13-minute minimum remaining-time gates described above.

`cleanup-inventory` emits read-only inventory requests for token-tagged instances,
recorded volumes (including detached volumes), and temporary resources. It does
not infer cleanup or automatically remove resources. Terminate promptly using
the retained token/instance identity; verify terminated instances and deleted
recorded volumes, then remove the named schedule, function, instance profile,
three dedicated roles/policies and security group. Retain independent deletion
readbacks, including all pagination. Incomplete preparation must also be
reconciled by the pre-recorded resource names before another experiment.
