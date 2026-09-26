# A10G component gate: harness failure

Status: HOLD. The bounded component audit stopped before the first diagnostic
solver process started. No native component gate passed in this run.

Controller `a0deef59e3ed29219e12861fadb9e3e70291cf4d` launched the attested
memory-tooling derivative, preserving the exact frozen sm86 solver executables.
Installed release identity checks passed. Docker mounted `/tmp` with `noexec`,
so the hash-verified diagnostic copy failed to start with `PermissionError`.
The result was collected before immediate termination was requested.

Fix `d7e7f92` explicitly permits execution on that temporary diagnostic mount,
while retaining network isolation, read-only root, dropped capabilities,
`nosuid`/`nodev`, a bounded tmpfs and the absolute cleanup deadline. It also
records a failed phase as failed instead of leaving its aggregate status running.
A local Linux/amd64 Docker test reproduced exit126 with the old mount and exit0
with the corrected mount using a copied system executable. This is a harness
regression check under emulation, not GPU certification. All74 local tests pass
with one skipped. Frozen solver source and numerical binaries are unchanged.

The three diagnostic artifacts were built at
`963147b0969f74e5d638d3fafef2c3c7f7d3e6e6`. The pinning rebuild differs from the
frozen executable only in one byte of an nvcc temporary filename in a nonloaded
ELF string table; the comparison verifies all other bytes and rejects differences
inside any PT_LOAD segment. Exact release pin replay and memory checks remain
separate from diagnostic derivative checks. Neither ran to completion here.

Independent cleanup checks at18:33:11UTC confirmed the instance terminated, its
recorded root volume deleted and zero remaining test security groups, schedules,
Lambda functions, IAM roles or instance profiles. The fix and all four failure
receipt hashes also passed independent review. A timeout before child return
can still leave aggregate status running; it cannot produce a false success.
The fresh-proof USD200 authorization is separate from the USD100 mainnet BTC
pilot. Its durable cost admission controls are not implemented yet; no fresh
sm86 search has started. No mainnet activation or transaction broadcast occurred.


## Corrected attempt: capacity rejected

Controller `c0c9579d267600cafc016bef760069e116a00c1a` prepared a fresh, hash-verified
bundle containing the reviewed mount correction. AWS explicitly rejected the one
On-Demand g5.xlarge launch in eu-west-1c with InsufficientInstanceCapacity. Reads by
both client token and campaign tag found no allocated instance. Independent
cleanup at18:37:24UTC confirmed no remaining temporary resources. No native gate
ran, and no automatic replacement was issued. The original failed experiment and
all its receipts remain preserved. See `2026-09-25-a10g-components-capacity.json`.
