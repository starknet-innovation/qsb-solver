# Matched A10G performance gate

Status: preparation; no A10G speedup claim yet.

The frozen optimized candidate remains source43c77084648aa0f4cbcb1589abfcc792c9cc0d9d,
image sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d.
The historical sm89 benchmark executable cannot serve as an architecture-matched
sm86 baseline. The `Build A10G performance baseline` workflow compiles the
repository's historical adapted subset using its unchanged Docker build recipe,
CUDA12.8.93 toolchain and sm86 flags. This is a validation artifact, never an
optimized release or application registration.

Before GPU execution, freeze the successful workflow run ID, source commit,
artifact digest and complete receipt. Compare the archived adapted source to the
committed historical preparation inputs. Verify the binary hash and effective
architecture independently. Do not use a moving workflow artifact as a launch input.
The build receipt says UNEXECUTED and does not establish correctness or performance.

The subsequent bounded gate must alternate baseline and exact frozen candidate
on one A10G, for both subset rounds and SegWit/Taproot layouts, recording all
completion logs and wall times. Require three paired samples per layout/stage,
identical candidate counts and rank starts, no incomplete ranges, and no silently
ignored hit that would shorten a sample. Preserve startup-inclusive timing and
avoid extrapolating subset throughput into whole-withdrawal cost or pricing.
All existing one-instance, live-price, fixed-deadline, result-collection and verified
cleanup rules apply. A build does not authorize an unprepared GPU launch.

## Baseline build receipt

Workflow run36182244943 succeeded at source
`f2fcc9a02ed2dca82a1370c671688c34df8f8ac3`. Downloaded artifact digest:
`sha256:7204e4bfe97fdbb4150d32b2366a90d127b8c9f912d14f5ffd4d4763fd6b8f19`.
The sm86 baseline binary SHA256 is
`672cf6689fd6e0c71d992ab2a6df2687ac9b2b0d5c7de42d63db6b51b69c6b5d`.
All receipt file hashes matched, and all13 adapted source files were independently
reproduced from the committed historical preparation inputs. Compiler receipt is
CUDA12.8.93. This verifies build inputs/artifact consistency; native execution,
effective binary architecture inspection and measured performance remain pending.

## Prepared runner, not yet executed on GPU

`run_a10g_performance.py` pins both binary hashes and the externally frozen fixture
hash. It requires one A10G and the installed candidate binding, then runs 24 samples:
three alternating pairs for both rounds and both layouts. Each sample requests
exactly2^31 ranks and must report that exact exhausted count with zero hits in its
summary, one completion marker and a successful process exit. Missing, shortened,
nonfinite, duplicate or reordered samples reject. Wall timing includes startup.
The full logs, summaries and partial-progress samples are persisted; any failed
sample leaves a failed result instead of a partial speedup claim.

The host wrapper retains the immutable candidate image, fixed shutdown deadline,
minimum13minutes before compute,12minute outer timeout and10minute internal budget.
The baseline is a hash-verified executable in the public read-only bundle. This
preparation does not launch infrastructure. Nine local tests cover acceptance and
negative accounting, including dummy subprocess success, hit preservation and timeout output capture; they
are not native solver/performance evidence. Operator bundle publication, complete
collection/cleanup preparation and one reviewed bounded launch are still required.
