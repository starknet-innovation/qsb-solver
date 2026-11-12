# Final PQB image evidence — HOLD

Read the [assessment and publication handoff](../../2026-11-12-final-image-qualification.md).
This review package does not publish an image, enroll a descriptor or deploy an application.

- `build/`: original signed build assets, raw signed bundles, runtime/installed-file/compiler
  identities, dependency inventory, notices and scan. The original `SHA256SUMS` also binds
  the 2.2 GB OCI archive, retained outside Git and in the exact hosted build artifact. Added
  build-run metadata and build logs have their own package-manifest hashes.
- `verification/`: actual GitHub verification output, verification environment, fresh consumer
  replay, local checks and original bundle inventories. The build-only verifier's report and
  proposal were captured before native execution and retain that original pending-native state.
  The current final proposal is in `release/`; native and consumer receipts are separate.
- `native/`: original 355,949-byte gzip receipt and collection identities, full stage verdicts,
  loaded runtime identity and timing/candidate summary. The gzip is a JSON object mapping
  relative paths to original UTF-8 file contents, not a tar archive. Hash it before decoding.
  It retains every native small-case invocation/problem/stdout/stderr/hit file, full-unit
  request/result/problem/log/hits, device/compiler/binding records and exit state.
- `source/`: exact import/lock/build source and a complete local-Git tree/input comparison.
- `release/`: HOLD descriptor envelope and exact shared range contract. The inner schema-3
  object is prospective and unenrolled. The index digest is real; GHCR availability has not
  been asserted. Do not substitute the historical descriptor from the earlier full solve.
- `cloud/`: scoped failures, cleanup and accounting. Full operator RPCs and short-lived signed
  collection URLs stay in the private external ledger. Unrelated account resources are omitted
  from public projections, whose original-receipt hash and projection scope are explicit.

`manifest.json` binds every package file. Signed build provenance is distinct from the native
collection receipts and consumer results. See the assessment for the exact verified signer
policy, source/binary identities, timing boundaries, scan limitations, cleanup and remaining
publication/adoption decisions. No receipt is relabeled as a test of another image.
