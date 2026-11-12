# PQB Critical findings review — publication blocked

**Do not publish the qualified `0fd37757…` image or enroll its descriptor.** Four of
the 20 Critical package matches expose a reachable transport problem. The other 16
do not meet the exploit preconditions in this Linux, one-shot AWS worker. The source
fix is prepared and locally tested; it is not a replacement qualified artifact.

The reviewed image is the exact native-qualified index
`sha256:0fd3775769c9fb6d6611c5f30be4d901ae65fc0694ceb27853b826d4f3bb060c`,
from source `ecb31d384fbdec9c67cd802548460b774a722baf`. Local Docker identity,
rootfs diff IDs and runtime configuration were checked against the signed build
before the probes. Original native and scanner receipts are unchanged.

## All 20 package matches

| CVE | Package matches | Applicability and decision |
| --- | ---: | --- |
| [CVE-2026-115557](https://github.com/python/cpython/issues/160040) | 4 Python packages | **Release blocker.** Compromised eMudhra keys can authenticate attacker certificates. The worker's outbound S3 client uses a bundled botocore trust store that still accepts affected cross-signed chains. |
| [CVE-2026-19445](https://mail.python.org/archives/list/security-announce@python.org/thread/QMQIUQB6WGGC3MI7I3WKQXOYOBDSPPS3/) | 4 Python packages | Not reachable in the supported worker: this issue requires a Python TLS server with an SNI callback switching contexts and unsafe lifetimes. This process is an outbound client; upstream excludes TLS clients. |
| [CVE-2026-118131](https://ubuntu.com/security/CVE-2026-118131) | 12 GnuPG packages | Platform preconditions absent: the reported issue concerns Windows ProgramData permissions and GnuPG 2.5.21 for Windows. This artifact is Linux/amd64 with GnuPG 2.2.27, and its compute/transport path does not invoke GnuPG. |

The [machine-readable review](evidence/critical-review-2026-11-12/review.json)
enumerates every package/version and binds the original scan hashes. These are three
distinct CVEs across 20 package records. Ubuntu's Medium priorities and Needs evaluation
statuses do not establish a fix. No scanner match is deleted, downgraded or globally ignored.
This review covers these Critical matches, not all High/Medium findings or a full audit.

## Reproduced blocker

The [Python advisory](https://mail.python.org/archives/list/security-announce@python.org/thread/FNAJMZV6XQYLVPABNINDMF3VF66AYLW4/)
and [public disclosure](https://emudhra.we-have-a-problem.com/) identify compromised
intermediate keys, including cross-signs. Removing one issuer path is insufficient.

The exact image has two different trust stores:

| Store | SHA-256 | Offline compromised chains accepted | Live compromised hosts accepted |
| --- | --- | ---: | ---: |
| botocore default `/usr/local/lib/python3.10/dist-packages/botocore/cacert.pem` | `9d6d5021fcc8a2232fce8eb4b3f982dc484252d555493ac5c2a3cbf2cb19438a` | 8 / 16 | 7 / 14 |
| updated system `/etc/ssl/certs/ca-certificates.crt` | `e05a523d99de77c6b1f2c7b7c3af502c8378f29e6e8484358ec55f96b0972ad6` | 0 / 16 | 0 / 14 |

Every accepted live bad leaf matched the disclosure's published certificate hash.
A normal `www.python.org` TLS control succeeded with both stores. The offline cases
include a key-rollover chain; the live cases include a certificate without CT logging.
Probes used botocore's TLS context factory, hostname/certificate verification, and no
credentials, HTTP requests or AWS API calls. Results and exact probe sources are retained
in the [review package](evidence/critical-review-2026-11-12/manifest.json).

The shared AWS entrypoint constructs its S3 client with the default trust selection.
That makes the vulnerable bundled store relevant to real input/output transport, not
an unused installed package. AWS authorization material and result transport could be
exposed to a network attacker. This is not evidence of an attack on the earlier runs.

## Prepared remediation and remaining gate

`worker/aws/entrypoint.py` now explicitly passes
`verify='/etc/ssl/certs/ca-certificates.crt'` to the S3 client. Certificate verification
stays enabled. Timeouts, the single-attempt transport, immutable output writes, public-only
inputs and independent CPU checks stay in place. An ambient `AWS_CA_BUNDLE` cannot silently
select a stale store instead. The system bundle is updated during the image build.

The new unit regression checks the actual client arguments and retry/time limits. The
image check inspects a real installed SDK client's selected store, rejects all 16 public
bad chains offline, and requires a valid Amazon Root CA positive control. The fixture time
is pinned to when the bad chains were valid, so expiry cannot be mistaken for distrust.

On the original image the new regression fails as expected. With only the proposed
entrypoint mounted read-only, it passes, along with the existing no-GPU/failure-credit and
whole-log parser checks. This is an explicitly identified **local overlay experiment**.
It neither changes the original image nor qualifies an image that contains the patch.
The mitigation covers this transport path; it is not a global CPython security backport.

Before publication, build and sign a new committed artifact, test its real selected CA
bundle and current scan, and qualify that artifact with explicit source/binary/runtime
applicability review. The prior native receipts remain tied to their original digest.
Only then can the qualified archive be copied without rebuilding, its registry index,
platform manifest and GitHub provenance verified, and release assets created.

Enrollment preparation belongs in the existing [qsb-app PR #150](https://github.com/starknet-innovation/qsb-app/pull/150).
Its [preparation record](evidence/critical-review-2026-11-12/enrollment-preparation.json)
remains blocked: no release asset, registry file or default was created. After verified
publication, copy the published descriptor verbatim there and run registry/app checks.
Serving, ECR mirroring/deployment and mainnet authorization remain separate.

No new paid hardware, cloud submission or resource was created for this review. The
completed native campaign and its cleanup/deadline/reservation were not resumed.

## Source merge readiness

The original PR #18 review snapshot recorded six findings, separate from the TLS blocker: campaign
state durability, cleanup pagination, live remote commit verification, native gate/case
binding, omitted runtime configuration fields and final-archive durability. The
[review snapshot](evidence/critical-review-2026-11-12/merge-readiness.json) links each thread.
The subsequent [source review closure](2026-11-12-review-readiness.md) documents their
fixes and regression checks. The linked snapshot remains the original historical receipt.
Current GitHub checks and review state determine source merge readiness. Source merge,
image publication and app enrollment are separate gates; the old image remains blocked.
