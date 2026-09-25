# A10G component gates passed

Promotion remains HOLD. The frozen candidate source `43c77084648aa0f4cbcb1589abfcc792c9cc0d9d` was tested on one NVIDIA A10G using controller `29847cdcafb9688065b69c92e5630f0c59c5d9ab`. Numerical candidate binaries were unchanged; the pinned derivative image adds memory tooling.

- Curve diagnostic: 5,628 scalar inputs, 11,256 points, four infinity cases and 504 table checks; zero errors.
- Exceptional recovery: 156 branches matched the independently hash-bound CPU expectations. Synthetic injection is not naturally discovered preimage coverage.
- Seven capacity cases (0, 1, 63, 64, 65, 1024, 1025) passed; overflow fails closed.
- Seven memory checks passed, including the frozen pinning known-hit replay and subset boundary case.
- All 34 reached pinning host calls were individually fault-injected and rejected; overflow/publication checks passed.
- The historical single-pin replay was independently CPU verified. It is not a fresh search or withdrawal.

Diagnostics are distinct executables, built with source and architecture bindings. The pinning rebuild differs from the frozen binary only in one non-allocated symbol-table byte, validated narrowly; exact historical replay and memory testing used the frozen pinning binary. This does not prove exhaustive arithmetic correctness.

The public archive was collected without rerunning compute, checked by length and SHA256, decoded with bounded inventory validation, and persisted before termination. CPU reference, context and expected-branch hashes were checked before CPU verification. See the adjacent public summary and cleanup receipt for identities and final infrastructure state.

Remaining: matched performance, durable fresh-proof coordination, a fresh full-predicate final-image withdrawal accepted by unchanged Core, final release review and separate application enrollment. External miner inclusion remains separate. Mainnet stays disabled. No private recovery material was transferred.

Independent AWS postchecks at 19:49:25 UTC confirmed instance termination, root-volume deletion and removal of all temporary security group, schedule, function, roles and instance profile.
