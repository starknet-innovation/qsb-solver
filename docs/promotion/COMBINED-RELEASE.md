# Publishing the tested combined image

Status: **prepared, not approved or enrolled**. The current candidate remains HOLD.

A normal version tag currently triggers `release.yml`, which compiles the historical
solver. It must not be used to claim publication of the optimized candidate.
Rebuilding a combined image would also create a new binary/image identity needing
its own final-image evidence. Promotion should publish a descriptor referencing
the already tested immutable candidate digest, preserving its original build
provenance and source commit.

## Prepared descriptor path

The automated read-only preparation command performs strict GitHub verification
of source commit, candidate tag, candidate workflow and GitHub-hosted builder,
then pulls the immutable digest and checks/extracts its installed binding in an
offline read-only container. It does not allocate GPUs or publish anything:

```sh
python3 scripts/prepare_combined_release.py \
  --candidate-tag candidate-20260925-2 \
  --source-commit bef76bf9aec123d95fdff53fb839a0c44f378927 \
  --image-digest sha256:9e86d94a66d7893e31d8e8d6bec7ddbc9b59f47f09e2f7a6015679fd95ab8b52 \
  --output-directory /path/to/new/preparation-directory
```

Failed verification stops before Docker execution. Outputs retain the verified
attestation, extracted files and HOLD proposal; the directory must not already
exist. Requirements: GitHub CLI with attestation support, Docker capable of
running Linux/amd64, and the exact public source commit available locally.

The lower-level command below is available when provenance and extraction have
already been verified independently.

After independently verifying the candidate image's GitHub provenance, extract
`/opt/qsb/pipeline.json` and `/opt/qsb/optimized-build-receipt.json` from that exact
image in an offline read-only container. Run:

```sh
python3 scripts/combined_descriptor.py \
  --pipeline /path/to/extracted/pipeline.json \
  --build-receipt /path/to/extracted/optimized-build-receipt.json \
  --source-commit bef76bf9aec123d95fdff53fb839a0c44f378927 \
  --image-digest sha256:9e86d94a66d7893e31d8e8d6bec7ddbc9b59f47f09e2f7a6015679fd95ab8b52 \
  --output /path/to/new/descriptor-proposal.json
```

The command validates the combined pipeline inventory and build-receipt binding.
It emits a HOLD proposal, not an enrolled release. Hashes in that proposal are
consistency evidence; they do not replace registry provenance verification or
independent source review. The source argument must match the image's attested
source, not the current checkout or a later documentation commit.

The proposed consumer object uses schema 3 and the canonical SHA256 fingerprint
of `contracts/ranked-v2.json` read by `git show` from the exact candidate source
commit. A newer checkout cannot silently replace that contract. Missing source
objects fail closed; fetch the public attested source before preparing the proposal. `kernelCommit` matches the combined worker's actual
wire identity. The separate upstream commits remain lineage in the pipeline;
neither describes the combined executable. Historical descriptor generation and
already published releases remain unchanged.

## Consumer dependency

The current default qsb-app branch cannot enroll arbitrary external descriptors.
[App PR #47](https://github.com/starknet-innovation/qsb-app/pull/47), checked at
`922c6c1d68ab992aa1fd2028b7cf3cc49a12af83`, contains the strict schema 3 consumer.
The candidate2 proposal passed that actual consumer's schema, registry and paid
search-contract checks locally. This is compatibility evidence only; the PR is
open and no descriptor was copied into its registry. The contract fingerprint is
`c570e14089e62de5185d9c8ba9f8f85d1b22c788edc524cd98a9ecaac5c26f7a`.

## Required completion sequence

1. Complete a fresh wallet-backed full-predicate withdrawal using this exact image,
   fresh commitments and a new fixture. Bind all stage/range/provider identities,
   CPU-verified solutions, the exact locally approved Xverse signature and
   unmodified Core acceptance to the request. Historical fixture replays do not
   satisfy this gate. Only public request/result data leaves the user's device.
2. Obtain final independent review of the source, image identities, accumulated
   validation evidence and fresh proof. A JSON status flag is not review approval.
3. Review and commit the final publication record and descriptor. Publish the
   descriptor against the existing immutable digest through a separately reviewed
   promotion operation, without triggering the historical rebuild workflow.
   Preserve candidate provenance and state the tested source commit explicitly.
4. Once the app's external consumer is merged, submit the descriptor and generated
   registry as a separate app change. Verify the strict parser, duplicate guards,
   contract fingerprint and release freezing. Do not change historical descriptors
   or the default release implicitly.
5. Before any selected-release paid execution, deploy only committed/pushed source
   and verify that its endpoint serves the exact image. An echoed kernel commit
   alone does not attest an image. Do not share a single endpoint between
   incompatible selected releases. Verify the actual enrolled and deployed state.

No step enables mainnet. External miner inclusion and any exact mainnet transaction
remain separate gates. The old completed proof endpoints and spent fixtures stay
untouched. This document is a completion plan, not evidence that steps 1–5 ran.
