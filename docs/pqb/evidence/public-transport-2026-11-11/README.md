# Public transport evidence

See the [assessment](../../2026-11-11-public-transport-solve.md) and `manifest.json`.
All three production-predicate stages passed; candidate remains HOLD.

The four tar.gz files preserve original relative paths and byte hashes:

- `provider-receipts.tar.gz`: scoped AWS reads, original job details, scaling, storage and cleanup receipts.
- `cloudwatch.tar.gz`: 142 job streams and one independently verified absent stream for a job cancelled before starting.
- `controller-records.tar.gz`: original checkpoints, submission intents, CPU decisions, handovers and controller logs.
- `s3-objects.tar.gz`: 143 raw inputs, 118 raw outputs, three control objects, the native builder result and collection metadata.

Extract them together to restore the campaign layout. `publisher/public-result.json.gz` is the
original gzip JSON mapping of native build/scan text receipts; its original base64 envelope is
also retained. The wider operator RPC responses and a CloudTrail receipt containing temporary
credential identifiers stay local. Their hashes are recorded; originals were not modified.

The exact 2.2 GB image archive and compiled development controller bundles are retained in the
local campaign directory outside Git; `externalOriginalsRetainedInCampaignDirectory` lists their
hashes. The temporary ECR repository has been deleted. No public release was enrolled.

`package-verification.json` records verification of all 1,201 archived files and replay of
`final_audit.py` from the restored package with the retained image archive. To repeat that audit,
provide `publisher/image.tar.gz`, rename the existing `final-audit.json` to preserve it, and run
`python3 final_audit.py RESTORED_DIRECTORY`. Only the new check timestamp should differ.

The final independent curve checks are `upstream-accepted-3-native-result.json` and
`upstream-native-final-{pinning,round1,round2}.json`. Use the committed checker under
`ops/pqb-public-solve/`, the clean pinned upstream commit and native coincurve 21.0.0 to repeat
them. Older receipts without backend metadata used upstream's pure-Python WASM curve shim;
`reference-shim-runtime.json` identifies it. Those supplemental receipts are distinct from the
final native libsecp256k1 checks. Neither executes wallet signing or Bitcoin Core consensus.
