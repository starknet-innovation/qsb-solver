# Combined candidate pinning repair — HOLD

Independent review of the promotion branch identified three host-side pinning
problems: unchecked CUDA input/reset/readback calls, unchecked hit-file publication,
and silently clamped hit counts above 64. Commit 52b1398 repairs these in the
combined-candidate build only. The historical vendor and historical release recipe
remain unchanged. The effective supported geometry is explicitly SLOTPIPE=0.

Independent regeneration confirmed 39 guarded host calls and byte-identical code
before main (including device code). The reviewer found the three issues addressed
in that source scope; this is not final native release approval. Optional cache
configuration failures now also stop the run, which can reduce availability on an
unsupported device rather than silently continuing.

The published candidate-20260925-1 image still contains the earlier pinning binary.
Its subset benchmark and curve audit evidence remain scoped to the recorded
binaries; they do not certify this repaired pinning build. A new immutable candidate
identity and native regression evidence are required before enrollment.

## Native audit preparation

`pinning-audit.yml` builds normal repaired pinning and a separate host diagnostic.
The diagnostic replaces only the host guard macro and injects a capacity count at
the host guard. It does not change device predicates or arithmetic. Its receipt
records both binary hashes, source hashes, compiler, and flags. It must never be
published as the normal solver binary.

`run_pinning_audit.py` verifies artifact hashes, runs a 256-locktime synthetic range,
and discovers the guarded calls actually reached. It injects an error at each such
call and requires exit 2, no Done marker, no hit publication, and no later guarded
call. A separate injected count of 65 must fail closed. Reached calls are not all
source sites: alternate branches and successful real-hit readback need additional
native tests. Public parameters only, one GPU, and an external 30-minute deletion
watchdog are required. No fresh search, funded fixture, or withdrawal is authorized
by this diagnostic.

Local harness/source/header tests pass; the Linux disk-full header test runs in CI.
Native diagnostic execution and exact new-binary regression remain pending.
Independent final approval and a fresh wallet-backed final-build proof are still
required. Mainnet and production defaults remain unchanged.

The reviewer caught an unreachable overflow injection in the first diagnostic
harness before GPU allocation. The corrected diagnostic injects after counter
readback and before the positive-hit branch. An explicitly synthetic device record
also exercises the extra hit-index read guard and directory/disk-full publication
failures. This record is not a discovered hit or cryptographic proof. Baseline
normal execution still requires zero real hits; any unexpected hit blocks this
audit for separate CPU verification.
