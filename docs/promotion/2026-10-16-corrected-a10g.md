# Corrected Config A: bounded A10G native gate

**Bounded native gate passed; release remains HOLD.** This tests corrected-script
public exports against a freshly built combined candidate. It is not a fresh
withdrawal or evidence that the entire possible search domain is correct.

The candidate was built from `7ebebd05e2bea3cb4ca48cbd3f47b0fe0c6641d1`, with
`scriptVersion=qsb-config-a-cmsverify-v1` and unchanged `ranked-v2` partitioning:

- Immutable image: `ghcr.io/starknet-innovation/qsb-solver@sha256:d22c9b5842eca2eca1d8f27f45d7760f213fdaa4e01511de1eda77541ef51e47`.
- Exact subset SHA256: `673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15`.
- Exact pinning SHA256: `cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62`.
- Diagnostic trace SHA256: `39ae10764dba342accc67f678a02525506e19a51e3bee46463481574fddcfb03`.
- Hardware: NVIDIA A10G; driver 595.91.07; compiled architecture sm86.

The diagnostic's independently built unmodified subset hash exactly matched the
candidate's subset. Source lock, build flags, architecture and source commit also
matched. The retained trace patch adds a printf before the unchanged real DER
predicate. The collector and plan are separate from the candidate image; their
newer controller revision does not change the candidate's recorded source commit.
See [collector operation and limits](CORRECTED-NATIVE-QUALIFICATION.md).

## Observations

Sixteen four-candidate subset ranges completed in both diagnostic and unchanged
executables. The diagnostic emitted exactly **128 expected recovered-public-key
SHA256 hashes**, with no missing, duplicate or extra lanes. Expected values came
from the hash-pinned app reference's complete transaction construction,
FindAndDelete and EC recovery, rather than reinterpreting GPU parameter layouts.
Both rounds, the first and final ranks, windows crossing ranks 64 and 128, and
minimum/maximum sequence and locktime were exercised.

Two additional one-candidate pinning smokes completed at sequence/locktime
`2147483648/500000000` and `4294967295/1744599999`. These checked native execution
and boundary overrides only; they did **not** trace or independently compare
pinning hashes. All runs retained the real predicates and produced zero hits.
No hit verification, funded output, wallet signature or transaction was involved.

Three alternating baseline/candidate process samples per subset round each
searched 268,435,456 ranks, on the same GPU and corrected parameters. The baseline
is the separately rebuilt historical subset implementation, hash
`672cf6689fd6e0c71d992ab2a6df2687ac9b2b0d5c7de42d63db6b51b69c6b5d`; its full build
receipt is retained. It is not an assertion that a historical image has been
qualified for corrected-script application dispatch.

| Round | Baseline median | Candidate median | Throughput increase |
| --- | ---: | ---: | ---: |
| 1 | 8.3893 s | 6.5320 s | 28.43% |
| 2 | 3.8778 s | 3.8235 s | 1.42% |

These are startup-inclusive process wall times including GPU table preparation,
transfers and output. Three short samples do not establish sustained-kernel or
complete-pipeline improvement; the small round-2 difference may be noise.
No pinning throughput was compared. These measurements do not change pricing.

## Evidence and remaining gates

[Manifest](evidence/cmsverify-a10g-2026-10-16/manifest.json) binds the retained
[raw receipt](evidence/cmsverify-a10g-2026-10-16/native-result.json), public plan,
source/build receipts and exact diagnostic patch. A second local pass rechecked
all case identities, expected hashes, range bounds, real-mode logs, hit absence
and timing sample inventory after collection. Full local tests passed before
native execution; no claim relies solely on the receipt's pass status.

Still required: pinning hash differential, broader supported script/output
layouts and SHA alignments, this build's exceptional/capacity/error-path
assessment, independently reviewed fresh real hits, and the fresh full-predicate
corrected withdrawal proof. The exact executable's empty-range completion does
not replace diagnostic coverage evidence, and bounded diagnostic evidence does
not prove full-domain completeness. External miner inclusion remains separate.
Image publication, release approval, app descriptor enrollment and deployment
are different steps; this gate does not authorize enrollment or activation.

## Cleanup and cost scope

The independent [cleanup receipt](evidence/cmsverify-a10g-2026-10-16/cleanup.json)
confirmed the host terminated and its root volume, schedule, cleanup function,
instance profile, temporary roles, security group and staging bucket were absent.
Termination was requested promptly after collection. Launch at 08:09:50 UTC to
local verified-receipt capture at 08:22:18.55 UTC bounds elapsed host lifetime by
12 minutes 29 seconds; capture time is not the exact termination timestamp.
At the quoted $1.123/hour compute tariff this is below $0.234 compute, excluding
EBS, network and control-plane costs. This is an upper estimate, not a provider bill.
