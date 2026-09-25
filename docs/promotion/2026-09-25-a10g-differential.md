# A10G sampled subset differential passed

Status: HOLD for promotion; this bounded subset gate passed.

The frozen sm86 candidate at source `43c77084648aa0f4cbcb1589abfcc792c9cc0d9d`
ran on one NVIDIA A10G through controller `d55febf26580b0631c7e2abf0832c78301ce9c53`.
The diagnostic was built in GitHub Actions from `43d1ad49aabe11b267205425dcc4d0ee3a877538`.
Its unmodified build hash matched the exact installed candidate. Source-lock,
architecture, effective flags, receipt and artifact hashes were checked before
execution. No numerical solver source or candidate image was changed.

Twenty SegWit/Taproot cases cover both subset rounds: rank zero, small counts,
block boundaries, a high interior rank, and the final 257 ranks of the domain.
Both the exact installed binary and source-locked trace derivative completed each
range. The independently hash-bound application CPU reference matched **3,116
candidates / 6,232 recovery hashes**, checked exact rank/recid multiplicity and
reconstructed each full transaction sighash. Recovery hashes are compared as the
two-branch set per candidate. Missing/duplicate trace and corrupted-hash negative
controls each rejected. No unexpected candidate hit occurred.

The trace derivative exposes internal hashes and is a different executable.
Running the exact release binary on the same bounded inputs does not make its
unexposed internal states directly observable, nor prove exhaustive correctness.
These results do not certify pinning, all exceptional arithmetic paths, new wallet
signatures, a fresh withdrawal, external mining, or mainnet readiness.

The instance ran with the fixed 25-minute cleanup deadline and network-disabled,
read-only candidate container. The complete public result was collected in chunks
and its whole-file hash verified. A transient AWS OAuth refresh rate limit during
collection was reconciled using saved read-command IDs; sequential collection
completed without rerunning the solver.

See [the machine-readable receipt](2026-09-25-a10g-differential.json) for source,
binary, fixture, independent reference and result identities and per-case counts.
The diagnostic-only public bundle is `validation-sm86-trace-d55febf.tar.gz` on the
existing candidate prerelease; it is not an enrolled solver.

Next: native sm86 pinning/exception/memory assessment, matched performance, and a
fresh final-image wallet-backed proof with unmodified Core. External miner
inclusion remains a separate gate. No app enrollment or mainnet activation.
