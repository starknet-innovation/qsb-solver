# Corrected script: bounded native collector (unexecuted)

This is an additional gate for the corrected candidate in
[CHECKMULTISIGVERIFY-MIGRATION.md](CHECKMULTISIGVERIFY-MIGRATION.md). It does not
change solver sources, enable a release or perform cloud operations. Only the
operator's fresh committed campaign may allocate an isolated GPU.

Prepare a public plan locally before any allocation:

```sh
python3 worker/promotion/validation/corrected_qualification.py prepare \
  --app /path/to/corrected-qsb-app \
  --fixtures tests/fixtures/cmsverify-v1 --output /new/public-plan.json
sha256sum /new/public-plan.json
```

The preparer verifies fixture and CPU-reference hashes from provenance before
importing the reference. It independently constructs each complete transaction
and applies FindAndDelete, then recovers both public keys and hashes them. The
plan has 128 expected hashes: both rounds, first/final domain ranks, four-rank
windows crossing 64/128 boundaries, and minimum/maximum sequence/locktime. It
uses public deterministic fixtures with nonexistent outpoints. Nothing is funded.

Build the diagnostic through `trace-audit.yml` workflow_dispatch at the exact
reviewed source revision. It builds the locked subset for sm86 on a native Linux
CPU runner, then injects only a trace printf at the generic recovered-key hash.
Download `native-trace-audit-sm86`, retaining receipt, patch and source commit.
The collector rejects a trace whose recorded unmodified binary does not equal
the exact candidate subset binary. A separate build with different bytes is not
accepted simply because its source lock matches. No compilation is done on the
paid host. Compare source lock, flags and commit against candidate build receipts
before staging, including ensuring the trace has unchanged real predicates.

Inside the candidate's immutable image on one isolated A10G, with this validation
directory and plan/trace artifacts mounted read-only and a fresh results mount:

```sh
python3 /validation/corrected_qualification.py run \
  --plan /inputs/public-plan.json --plan-sha256 ACTUAL_PLAN_SHA256 \
  --trace /trace/trace-subset --trace-sha256 ACTUAL_TRACE_SHA256 \
  --trace-receipt /trace/receipt.json \
  --subset /opt/qsb/subset --subset-sha256 ACTUAL_SUBSET_SHA256 \
  --pinning /opt/qsb/pinning --pinning-sha256 ACTUAL_PINNING_SHA256 \
  --output /results/corrected-native.json
```

The 600-second internal deadline complements the campaign's outer timeout and
independent cleanup deadline. Exact output-file creation prevents overwriting an
earlier attempt. Every subset range runs the diagnostic and unchanged executable;
all expected lanes must occur exactly once with exact independent CPU hashes.
Missing/duplicate/malformed/extra traces fail. Two pinning boundary smokes execute
the unchanged binary at one candidate each. All executions retain real predicates;
unexpected hits stop for separate CPU verification, with no range credit.

**Evidence limits:** these pinning smokes are not pinning hash differential or
valid-hit evidence. Subset tracing is a diagnostic derivative; unchanged executable
completion alone does not prove full-domain coverage. This plan does not cover
all SHA alignments, every supported output layout, exceptional paths, capacity,
matched throughput, fresh discovered hits or a fresh full-predicate withdrawal.
Those gates remain separately required. Neither plan generation nor collector
unit tests are native qualification. Keep the candidate HOLD until actual
receipts and remaining gates are reviewed.

Optional `--baseline /baseline/subset --baseline-sha256 ACTUAL_SHA256` adds three
alternating baseline/candidate process samples per subset round, 2^28 ranks each,
using identical corrected parameters and hardware under the same deadline. The
retained wall time includes process startup, transfers and output. This is a
bounded process-throughput comparison, not sustained-kernel, pinning or
full-pipeline performance. Preserve the baseline build provenance independently.
