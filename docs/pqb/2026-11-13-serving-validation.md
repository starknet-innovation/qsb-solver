# TLS-fixed PQB: isolated consumer-workflow qualification

The published TLS-fixed image completed a fresh public synthetic solve through the
actual Step Functions → Lambda coordinator → AWS Batch/S3 consumer. The native
preflight, complete solve, independent CPU checks and offline Core component checks
passed. The campaign is closed and its operational reservation released after
independent cleanup. This qualifies the tested isolated SNF Ireland configuration;
production app-account runtime readiness and PQB selection remain separate gates.

The [public evidence package](evidence/serving-2026-11-13/README.md) contains every
public unit request and successful response, independent CPU decisions, exact Core
inputs/results and a checksummed assessment. Operator configuration and original
AWS receipts remain outside Git; the package binds their sealed receipt hashes.

## Artifact and consumer identity

- Producer source: `cfd99e3844698f59679e4c15cf567db2976b9ffc`.
- Descriptor: `pqb-ranked-v2-cfd99e384469-edce7a14b554`.
- Canonical image: `ghcr.io/starknet-innovation/qsb-solver@sha256:edce7a14b5548a079f8ebf1e866c533cb14573328cf739a6647b150cca08756e`.
- Contract: `pqb-ranked-v2`, SHA-256 `5217daa6415b83dcce2d85159130df4994ab0e9bb67910c7bdf00e5804f4ee71`.
- Native consumer/controller: qsb-app `16a842a11811b0ecc036ee9b15291360275d755e`.
- Coordinator ZIP: `59816f3a0c21e2b2c4f0cf8f0aaa4eb4252a8bf5e31a7b1e866a9b8fc6b7eff2`.
- API ZIP: `1d23ffc6f4545fd3d1b330e0a0be6b3d5ef694a6deb03bb6dba48dd1d0ee9c35`.
- Independent generator: `eccdd09772edf14ab37fc63992b0626ad7ff2221`, native coincurve 21.0.0; shared-object hash is retained in the CPU receipt.

The original build attestation was verified and the full OCI index copied without
rebuilding into an immutable mirror. The digest and enrolled descriptor were not
changed. [Release provenance and TLS review](2026-11-12-tls-replacement.md), retained
licenses/notices and the disclosed 20 unfixed Critical matches continue to apply;
this execution does not resolve those package matches or constitute a new security
audit. Mutable package resolution still prevents a universal bit-for-bit rebuild
claim.

## What ran

Hardware was `g5.xlarge`, one NVIDIA A10G per host, driver `580.178.04`, in
`eu-west-1`. Each worker had four vCPUs, 12,000 MiB memory, a read-only root,
temporary writable storage, dropped capabilities and no new privileges. Peak
concurrency was sixteen hosts; twenty hosts were allocated over the lifecycle.

The fresh preflight completed one full pinning unit, with a 490.157-second Batch
runtime. Its workflow took 822.079 seconds including queueing, cold startup and
polling. It passed native accounting and both CPU checks before the solve began.

| Full solve stage | Completed | Coordinated cancellation | Successful worker process seconds, summed |
|---|---:|---:|---:|
| Pinning | 23 | 15 | 11,282.255 |
| Round 1 | 46 | 14 | 19,126.491 |
| Round 2 | 39 | 10 | 16,651.210 |
| Total | 108 | 39 | 47,059.956 |

The full workflow ran from **13:48:30.998 to 14:54:24.612 UTC on 13 November
2026**, taking **3,953.614 seconds (65 minutes 53.614 seconds)**. This boundary
includes its queueing, startup, transport, coordinator CPU checking and polling;
it excludes the preflight, build, subsequent audits and teardown. Summed worker
process times are not steady device timings or workflow wall time. Transfer,
computation and verification costs were not individually isolated.

All 147 full-solve submissions were reconciled. The 39 provider-declared
coordinator cancellations had an earlier CPU-verified winner for the same packet
and receive no completion credit. Including the separate preflight, the sealed
audit checked 109 successful units, all 15 emitted candidates and all three full
solutions. The independent pinned upstream native backend reproduced the public
problem bytes, eight sampled canonical sighashes per stage and every emitted
full-predicate verdict. No grinder was simulated. The final coordinator result
was `verification / awaiting_authorization`; no funded output or transaction
submission was involved.

This is one complete public fixture solve, not a latency distribution or a matched
baseline/candidate comparison. It supports no new comparative speedup, fee saving
or complete-domain enumeration claim. Range accounting and the statistical gate
count bound remain necessary consistency checks, without proving no opportunity
was omitted.

## Offline Core result and checker provenance

The exact 1,616-byte synthetic transaction passed the packaged Bitcoin Core 27.2
script interpreter with a public OP_TRUE helper. All twelve changes were rejected:
destination, output amount, fee, extra output, either outpoint, either sequence,
locktime, version, co-signature and missing vault scriptSig. All thirteen inputs,
transaction hashes, results, binary/library hashes and immutable network-disabled
container identity are retained in the evidence package.

The original checker accepted the transaction and rejected its first ten
mutations, then stopped because its locator assumed exactly one long DER
signature. The valid scriptSig contains two. The reviewed correction selects the
final signature/key pair, checks the key against the lock's HASH160 and mutates
only the final signature's S byte. A two-signature regression covers this case.

The corrected checker ran from qsb-app
`a3b28bfea190bf606cebed4dd7e73bfb69654d28` after independent cleanup. Its explicit
retained mode verifies every sealed native file, binds the solution to the sealed
solve-table row, permits only checker/docs changes and requires all 28 packaged
artifact hashes to match. It reassembled the byte-identical transaction and used
the original Core binary, library and immutable container. Native execution remains
attributed to `16a842a`; the checker correction grants no new native work credit.

This component check does not validate a helper-wallet signature, live UTXO
existence, chain acceptance, miner policy or inclusion. Legacy input signatures do
not commit prior-output amounts; production chain and exact-spend checks retain
that obligation. No broadcast occurred.

## Cost, cleanup and handoff

At the retained Linux on-demand rate of **$1.123 per host-hour**, recorded launch
and termination transitions estimate **$18.73 of VM compute** for this campaign.
Using first observed terminated times gives a conservative compute bound of
**$22.44**. The three stopped SNF campaigns add a separate conservative bound of
**$3.65**, including incomplete work and late allocations: **$26.09 combined**.
These figures exclude EBS, IPv4, registry/storage, control-plane, logging and
network charges. They are estimates, not queried provider billing. The $200
operational reservation is released, not reported as spend.

Independent cleanup passed 321 checks. All twenty recorded hosts are terminated
or reconciled absent and all twenty volumes are deleted. One older host had aged
out of EC2 listings; its sealed terminal receipt and a fresh exact-ID absence
lookup reconcile that case. The dedicated queue, pool, workflow, functions,
schedules, tables, roles, boundary, profile, security group, launch template,
artifact bucket and native log group were removed; job definitions are inactive.
The immutable mirror and untouched pre-existing network are intentionally retained.
No uncertain launch or paid submission was replayed.

The descriptor is enrolled by merged [qsb-app PR #150](https://github.com/starknet-innovation/qsb-app/pull/150).
The deployment baseline includes merged [PR #151](https://github.com/starknet-innovation/qsb-app/pull/151).
[PR #153](https://github.com/starknet-innovation/qsb-app/pull/153) contains the
validation controller and corrected offline checker. A fresh production metadata
readback after cleanup still selected Config A, with the same coordinator bundle
hash. This isolated-account assessment does not establish the London app account's
PQB IAM, capacity or native runtime readiness. Production PQB adoption remains on
hold pending that deployment-specific verification and explicit selection review.
The existing Config A image, descriptor and deployment remain available for
rollback; there is no separately qualified prior PQB release for PQB vaults.
