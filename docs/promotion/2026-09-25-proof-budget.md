# Fresh-proof budgeted controller

Status: local integration complete; no fresh sm86 cloud launch has used this path.
PR2 remains HOLD for the remaining native, performance and full-proof gates.

The fresh-proof wrapper reserves funds before paid preparation, enforces one
unresolved intent and records each operation before calling the existing bounded
AWS controller. Unknown outcomes cannot resubmit. Explicit capacity rejection
requires token/tag reconciliation and complete cleanup before settlement. Provider
IDs returned late attach to the original intent. Resource scope is frozen and
cleanup names derive from the client token. Missing or over-one-hour lifetime
evidence blocks settlement rather than undercounting costs and unlocking more work.

Authorization is USD200 with USD20 retained headroom and a conservative USD2 debit
per bounded session. Every debit remains consumed after settlement, including a
capacity rejection. This can stop admission below the actual invoice total; it
is not an AWS-enforced invoice ceiling. See the full operational contract and
remaining execution prerequisites in [the runbook](../../ops/fresh-proof/README.md).

Read-only live pricing verification returned USD1.123/hour for g5.xlarge,
USD0.088/GB-month for gp3 and USD0.005/hour for public IPv4. The wrapper refreshes
scope-bound prices before paid transitions. No infrastructure mutation or GPU
allocation was performed for this integration.

Independent review identified and closed three issues: stale handles accepting a
replaced ledger, mutable names hiding cleanup resources, and settlement ignoring
lifetime overruns. All28 budget/controller tests independently passed. The full
suite ran102tests:101passed and1skipped. Cloud launch/cleanup responses are mocked;
the real base-controller guard is exercised before any cloud mutation. These tests
are not a successful funded search, fresh withdrawal or provider invoice proof.
