# TLS replacement artifact assessment

The assessed image was built from merged `main` commit
`cfd99e3844698f59679e4c15cf567db2976b9ffc` by signed qualification run `43205074943`.
Its OCI index is `sha256:edce7a14b5548a079f8ebf1e866c533cb14573328cf739a6647b150cca08756e`.
Publication remains pending completion and review of this assessment. No image is
called published until its actual registry digest and original build provenance verify.

Nine fresh hardware requests were rejected before allocation: eight capacity
rejections across A10G/L4 sizes and placements, and one Virginia quota-enforcement
discrepancy (the quota API reported eight vCPUs; EC2 enforced zero). Every identity was
reconciled. No new native execution or timing is claimed. One cleanup controller timed
out awaiting a tool response; its remaining known resources were removed with separate
durable requests and independently read back absent. Original timeout/state receipts
are preserved. The earlier native campaigns were never resumed.

The assessment therefore checks applicability of the existing native evidence by
complete filesystem comparison of the exact signed reference and replacement images.
The reference is `sha256:0fd3775769c9fb6d6611c5f30be4d901ae65fc0694ceb27853b826d4f3bb060c`;
its original three largest units and 39 small-case invocations retain their original
archive, source, image and timing identities. They are never relabeled as new image runs.

Both images have the same 11,044 filesystem paths, runtime configuration, package
versions and compiler receipt. The grinder, handler, partitioner, CUDA/Python/OpenSSL
libraries and runtime loader cache are byte-identical. The only transport semantic
change is the explicit S3 system CA selection. Binding metadata changes only its
source commit, and the retained license notice matches each committed source.

The remaining byte differences are 195 Python cache timestamp headers, four installation
logs and the ldconfig auxiliary installation index. Each changed Python cache has
identical marshaled code, identical source bytes, matching magic/flags/size, and a
timestamp matching its own source. Other contents, permissions, owners, links, additions
or deletions fail the comparison. File mtimes are retained but do not become a new
performance measurement. The actual runtime `/etc/ld.so.cache` and library bytes match.
See [PEP 552](https://peps.python.org/pep-0552/) and the
[runtime linker cache documentation](https://man7.org/linux/man-pages/man8/ld.so.8.html).

This is an explicit component applicability review under the repository's artifact
binding rules, superseding fresh GPU attempts for this transport-only delta. It is not
a new native attestation, matched performance result, complete solve or broad completeness
proof. The original native evidence applies only to the identical compute stack and its
recorded supported A10G environment. Unexecuted L4/controller adaptations remain separate
experimental branches and are not adopted by this release.

The replacement's actual installed client selects the updated system store despite an
ambient stale `AWS_CA_BUNDLE`. It passes all 16 offline bad-chain regressions, rejects
14 live compromised-key hosts and accepts Python.org and regional S3 controls. A fresh
public S3 transport round trip and consumer/installed-wrapper compatibility review are
required before a publication decision. The original 20 Critical matches remain in
the scan: mitigation applies to the supported S3 path, not a global Python backport.

Publication must copy all manifests of the qualified archive without rebuilding,
verify the registry index/platform/config and original signed OCI bundle, and retain
the descriptor, contract, notices, scan and evidence. Only then may the published
descriptor be enrolled verbatim in existing qsb-app PR #150. Deployment, ECR serving
configuration, default selection, mainnet switches and transactions are separate.
