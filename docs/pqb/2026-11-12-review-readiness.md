# PR #18 source review closure — 12 November 2026

This change addresses the six remaining source review findings. It does not qualify
or publish a replacement image. The [Critical review](2026-11-12-critical-review.md)
still blocks publication of the previously qualified image; the TLS source fix needs
a replacement artifact and applicable qualification before qsb-app PR #150 enrollment.

| Review thread | Fix | Regression evidence |
| --- | --- | --- |
| `PRRT_kwDOUq1e7s62hpKk` | Both controllers flush/fsync checkpoint files, rename atomically and fsync the parent before dependent mutations. | File/rename/directory ordering and both fsync failure barriers. |
| `PRRT_kwDOUq1e7s62hpKn` | Shared Lambda discovery follows `NextMarker` until found or exhausted; failures prevent cleanup completion. | Target after 50 unrelated functions, and failed second-page cleanup. |
| `PRRT_kwDOUq1e7s62hpKr` | Both controllers require clean HEAD to equal the configured remote branch's live `ls-remote` result. | Real bare remote moves/deletes the branch while the local tracking ref remains stale. |
| `PRRT_kwDOUq1e7s62kTLu` | Replay binds the gate checksum inventory to reviewed Git inputs and signed build assets, then checks all 13 original case identities and outputs per stage. | Altered gate, placeholder/duplicate cases, missing invocation and changed hit sets rejected after rehashing archive claims. |
| `PRRT_kwDOUq1e7s62kTL1` | Runtime comparison checks the union of both configurations with explicit defaults; import tags the inspected immutable image ID. | Nondefault omitted fields and unknown fields rejected; mutable loaded tag cannot change the inspected identity. |
| `PRRT_kwDOUq1e7s62kTL_` | Collector fsyncs an exclusive partial archive, renames it and fsyncs the directory before reporting metadata. | Actual embedded collector ordering/hash check and fsync failure with no metadata. |

The full local suite passes: **237 passed, one platform-specific skip (238 total)**.
The 11 focused regression tests are in `tests/test_pqb_six_reviews.py`; their logs and
the [fresh CPU replay receipt](evidence/review-closure-2026-11-12/manifest.json) are retained separately. A fresh CPU
replay also passes against the clean pinned qsb-app commit
`276f2ae09d50ca44d46b035e45b6d0365802edcf`, using the original native archive
`70526ef7da4920820e888bbaae5baa72b543e6b827ad1ea111f48584deb189ce`, original build
assets and reviewed gate commit `4dff68d2eeeeaed7b437eb598f668d33a7f47205`.
It checks all 39 retained small-case invocations and independently rechecks the three
native envelopes through the pinned consumer. This is a stronger verification of
existing native evidence, not new GPU execution or a new complete solve.

Original final-image and Critical-review evidence packages are unchanged. No hardware,
cloud mutation, registry publication, enrollment or deployment is performed for these
fixes. Existing campaign cost and verified cleanup receipts remain as recorded; there
is no new reservation or provider billing query. Current PR checks are the authoritative
CI result for the pushed source. Source merge does not remove the publication HOLD.
