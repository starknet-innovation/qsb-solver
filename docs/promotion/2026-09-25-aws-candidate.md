# Optimized AWS candidate: bounded A10G gate passed

Status: HOLD. No app enrollment or mainnet activation.

- Candidate tag: `candidate-sm86-20260925-1`.
- Source: `43c77084648aa0f4cbcb1589abfcc792c9cc0d9d`.
- Attested image: `ghcr.io/starknet-innovation/qsb-solver@sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d`.
- Pinning SHA256: `cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62`.
- Subset SHA256: `673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15`.

GitHub attestation was checked against the exact source, tag and candidate workflow.
The pulled image's installed files match its pipeline binding and sm86 receipt.
Native Linux build CI passed both combined targets and license checks. The actual
pulled AWS image passed the offline fake-S3 transport test for all three stages,
including input-integrity rejection. These were failure-path tests, not GPU success.

The committed `run_a10g.py` gate binds these exact binaries. It requires one A10G,
two historical subset replays and sixteen small/sampled ranges from four public
fixtures. It has a ten-minute internal deadline and a one-shot output marker.
These limited checks will not establish independent CPU differentials, full range
coverage, pinning correctness, a fresh withdrawal, or external miner inclusion.

Three explicit one-instance g5.xlarge attempts in eu-west-1a, 1b and 1c each returned
`InsufficientInstanceCapacity`. No instance was allocated and no GPU test ran.
Each attempt had a distinct durable intent and independent cleanup schedule;
previous attempts were reconciled and cleaned before the next attempt. Live AWS
list price was USD1.123/hour, excluding storage/IPv4; no EC2 compute was consumed.
The test controller uses an absolute 25-minute deadline, an external cleanup
invocation in the following full minute, and guest shutdown. Control-plane latency
is not a guaranteed hard billing ceiling.

The initial capacity wait was resolved by the authorized retry below. Continue
remaining correctness and final-image proof before reviewed enrollment.
Do not reuse failed launch intents or attribute the previous sm89 proof checkpoint
to this image. The USD100 Xverse pilot still has no funded mainnet vault or approved
exact transaction.

## Authorized retry: actual A10G gate passed

The committed readiness wait resolved the earlier SSM/cloud-init race. Controller
`bbed7531a4e416584605a01230bd49c251aed223` ran the exact frozen candidate above on
one On-Demand g5.xlarge in Ireland. Both historical subset replays and all sixteen
sampled ranges passed, with exit code zero and the expected source/architecture/
binary binding. Public result identity is in `2026-09-25-a10g-result.json`.

This closes only the bounded native execution gate. The status remains HOLD for
independent CPU differential, pinning correctness, broader coverage and matched
performance, and fresh final-image withdrawal/miner evidence. No app enrollment,
mainnet activation or transaction broadcast occurred.

The subsequent [sampled A10G differential](2026-09-25-a10g-differential.md) passed
20 cases / 3,116 candidates / 6,232 CPU-checked hashes. This supersedes the pending
sampled subset differential gate above, not full-domain or pinning validation.
