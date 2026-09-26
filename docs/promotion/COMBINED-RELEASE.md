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
  --target aws \
  --candidate-tag candidate-sm86-20260925-1 \
  --source-commit 43c77084648aa0f4cbcb1589abfcc792c9cc0d9d \
  --image-digest sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d \
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
image in an offline read-only container. Save `docker image inspect --format
'{{json .Config}}' IMAGE@sha256:DIGEST` as `image-config.json` from that same
provenance-verified digest. AWS preparation requires sm_86, `/opt/qsb` as the
working directory and the exact AWS command without an entrypoint override. Run:

```sh
python3 scripts/combined_descriptor.py \
  --target aws \
  --image-config /path/to/extracted/image-config.json \
  --pipeline /path/to/extracted/pipeline.json \
  --build-receipt /path/to/extracted/optimized-build-receipt.json \
  --source-commit 43c77084648aa0f4cbcb1589abfcc792c9cc0d9d \
  --image-digest sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d \
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

[App PR #47](https://github.com/starknet-innovation/qsb-app/pull/47) merged on
25 September at 10:25 UTC as `8c7049064d28be75f3a0537cb4542fe9e8407597` and adds
the strict schema 3 consumer. The candidate2 proposal previously passed that
consumer's schema, registry and paid search-contract checks locally at
`922c6c1d68ab992aa1fd2028b7cf3cc49a12af83`. This is compatibility evidence only;
the optimized descriptor has not been enrolled. The contract fingerprint is
`c570e14089e62de5185d9c8ba9f8f85d1b22c788edc524cd98a9ecaac5c26f7a`.

## Required completion sequence

1. Complete native sm86 pinning, exceptional recovery, curve and memory checks,
   plus matched A10G performance against `aws-v0.1.0` for pinning and both subset
   rounds. Publish exact binary/image/tooling bindings and reviewable evidence.
2. Obtain final independent source and evidence review. On 25 September the user
   explicitly removed the fresh wallet-backed regtest search from this release's
   gates. Do not start that search for this PR. The first separately authorized
   mainnet pilot will provide the new release's end-to-end withdrawal evidence;
   component checks and historical replays do not establish that evidence.
3. Review and commit the final publication record and descriptor. Publish the
   descriptor against the existing immutable digest through a separately reviewed
   promotion operation, without triggering the historical rebuild workflow.
   Preserve candidate provenance and state the tested source commit explicitly.
   Release publication requires the user's explicit approval. Never delete or
   move the candidate tag: it preserves the attested source after a squash merge.
4. With separate explicit user approval, submit the descriptor and generated registry as a separate app change against
   the merged external consumer. Verify the strict parser, duplicate guards,
   contract fingerprint and release freezing. Do not change historical descriptors
   or the default release implicitly.
5. Before any selected-release paid execution, deploy only committed/pushed source
   and verify that its endpoint serves the exact image. An echoed kernel commit
   alone does not attest an image. Do not share a single endpoint between
   incompatible selected releases. Verify the actual enrolled and deployed state.

No step enables mainnet. External miner inclusion and any exact mainnet transaction
remain separate gates. The old completed proof endpoints and spent fixtures stay
untouched. This document is a completion plan, not evidence that steps 1–5 ran.

## Executed preparation check

The real command at `bbaf782874e83b26a5c8bbca241613787e4ccf89` verified candidate2
through GitHub, pulled its immutable digest and executed the installed binding
check in a local Linux/amd64 container without network access or GPU. The extracted
proposal exactly matched the source-bound proposal accepted by the pending app
consumer. A real wrong-candidate-tag attempt failed attestation before extraction.
A post-check showed no extraction containers remaining. The
[preparation receipt](2026-09-25-preparation.json) records artifact hashes.

The initial command combined two mutually exclusive GitHub CLI flags and failed
before Docker. The executed correction uses exact certificate identity, source
ref/digest and signer digest; no claim relies on the failed attempt. Unit tests
cover verification failure, immutable identity rejection, HOLD extraction and
container removal after timeout. These tests do not grant promotion approval.

## Merged app consumer check for sm86

App PR47 merged at `8c704906`; the current checked app commit
`476a47c` includes its strict schema3 consumer. In an isolated checkout, two actual
consumer tests passed for the source-bound sm86 proposal already extracted and
verified in the AWS candidate preparation. They checked exact source/image and
paid-search contract acceptance, and rejected changed contract, duplicate ID and
mutable image data. No registry file, deployed configuration or default changed.
This closes consumer compatibility for that proposal, not enrollment or promotion.

## Deterministic pinning failures

Treat `QSB_RANGE_INCOMPLETE`, hit-capacity overflow and repeatable publication or
CUDA failures as a stopped work unit. Preserve the exact range, image and logs;
do not blindly resume or retry. The current app may describe exit-2 results as
resumable incomplete ranges, but that is not evidence that retrying will help.
Diagnose and correct the cause before authorizing another paid attempt. No
failed or truncated range receives completion credit.
