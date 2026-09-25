# Combined worker promotion

This candidate joins host-repaired historical pinning to the optimized
subset build for round1/round2. The pinning repair checks CUDA host operations,
hit capacity and output publication while preserving its device code and
SLOTPIPE=0 configuration. Both stages use the public `ranked-v2` request/result contract;
`kernelCommit` identifies the combined repository commit rather than falsely
claiming either upstream commit describes the whole pipeline.

Every request checks the installed pinning/subset binaries, wrapper and scheduler
against the generated pipeline binding. This detects local inconsistency, not a
malicious provider. The app must still verify every hit independently and pin the
published image digest. No CPU verifier or wallet material is copied into this image.

`candidate-*` tags compile on native Linux, run offline no-GPU checks, publish an
attested image and HOLD prerelease with actual binary hashes and compiler receipt.
They never emit an app release descriptor. The existing `v*` release workflow
continues to publish the historical baseline, so a candidate cannot silently
replace it.

Before promoting a combined candidate:

- Verify the image provenance, source commit, contract and actual binary binding.
- Execute all three stages on a compatible GPU and compare public results against
  qsb-app's separate CPU reference, including boundary and exceptional cases.
- Compare matched fixtures against the historical image on the same GPU; historical
  tail-cache speedups do not certify this freshly compiled binary.
- Complete a fresh full-predicate withdrawal proof with the final image; distinguish
  bounded smokes and historical replays from that proof. Any real mainnet spend
  still requires concrete user transaction authorization.
- Publish a new normal release and enroll its descriptor only after reviewing that
  evidence. No automatic application deployment or default change is performed.

The pinning device algorithm remains historical. Both stages fail closed when
the supported host hit capacity is exceeded; this is not unlimited output support.
The integration does not claim to publish the fastest Yukon leaderboard submission. The optimized subset
has fail-closed capacity/exception handling; deterministic failures must not be
credited or blindly retried.
