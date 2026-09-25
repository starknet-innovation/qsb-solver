# One-shot optimized A10G gate

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
reset the fixed deadline. The 17:13 UTC attempt failed ten seconds before the boot
marker existed; no bundle was staged or solver executed, and no rerun was issued.
