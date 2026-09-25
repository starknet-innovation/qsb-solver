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
