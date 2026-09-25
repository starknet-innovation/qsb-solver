# Exact-binary validation batch

`benchmark.py` validates the candidate-20260925-1 subset executable against its
published SHA256, then downloads and checks the historical subset executable
extracted from the attested v0.1.0 OCI image
`sha256:badfcac297db6c242cf0e91e78fe294fa900d3c59f363258ec6d0d502162c755`.
The validation-only baseline release asset is not a new solver release.

Fixtures contain only public GPU parameters. Benchmark fixtures were exported by
the separate qsb-app CPU reference with synthetic nonexistent 00/11 outpoints,
SegWit/Taproot output layouts, and both subset stages. Each runs three alternating
baseline/candidate samples of 2^31 ranks on the same GPU. Wall times include process
startup. The batch permits 20 minutes, with 120 seconds per process and process-group
termination on timeout. An external 30-minute resource deletion watchdog is required.

Two historical one-candidate replays require exact expected hit records. They test
the new binary's hit path; they are not a fresh search, independent CPU verification
of new hits, a withdrawal, or permission to reuse the original spent fixture.

Run only in an isolated candidate OCI filesystem on one GPU. This script performs
no signing, transaction broadcasting, durable coverage credit, or production enrollment.
