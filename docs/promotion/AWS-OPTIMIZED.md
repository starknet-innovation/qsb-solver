# Optimized solver on AWS A10G — build preparation

Status: HOLD. The user selected the optimized solver for the mainnet pilot, capped
at USD100 of BTC including transaction fees, with Xverse signing. GPU costs are
separate. This selection does not approve any exact funding or withdrawal bytes.

Candidate2 was compiled for sm_89. The AWS A10G backend targets sm_86. Do not copy
candidate2 into that deployment and assume compatibility. NVIDIA documents that
an sm_89 cubin cannot run on compute8.6 hardware; higher-target PTX is not a
backward-compatibility substitute. See the [Ada compatibility guide](https://docs.nvidia.com/cuda/archive/12.6.0/pdf/Ada_Compatibility_Guide.pdf).

Both optimized subset and repaired pinning builds now accept CUDA_ARCH=86 or89,
defaulting to89. The source-lock remains unchanged: only its single architecture
flag may be replaced. All predicate, arithmetic and geometry flags remain locked.
The subset release and build receipt record the effective architecture and flags,
and the combined binding records actual executable hashes and architecture.
The binding rejects a pinning/subset architecture mismatch before producing an
image identity. CI compiles both
architectures and runs offline image identity/failure tests. Compilation and
no-GPU checks are not A10G execution certification.

A new candidate-sm86-* tag selects86 in the candidate publication workflow; existing
candidate-* tags retain89. Never move an existing tag. Every new build remains a
HOLD prerelease and has new image/binary identities. No tag is created by this
change. The historical release workflow and default remain unchanged.

Next: verify the sm86 native build, compose the merged AWS public-only transport
with the combined candidate (not the historical AWS binary), then validate actual
A10G execution, independent CPU differentials, boundaries, failures and matched
performance for the new artifacts. Preserve source/licensing inputs from merged
main when composing. The fresh proof is not required for this release (user decision,
25 September); obtain the matched A10G performance evidence and final review before
enrollment. Native checks on candidate2 do not certify new binary bytes.

The existing regtest request retains36completed pinning ranges and nextAttempt36,
with no active GPU and no solution. Preserve it as candidate2-scoped evidence;
do not silently attribute that coverage to a new build. A new build needs explicit
coverage provenance/reconciliation or a separately identified fresh proof.
No old spent fixture, regtest private key, or recovery state may become the mainnet
wallet. Mainnet funds remain untouched; exact Xverse funding/fee approval follows
verified deployment and a new mainnet public request.

## AWS transport integration

The promotion branch now includes main's AWS transport and license packaging.
Combined candidates use explicit `aws` and `runpod` Docker targets. The AWS target
starts `aws_entrypoint.py`, uses the same combined handler and release binding,
and keeps the public-only S3 input digest and immutable output protocol. CI runs
an offline fake-S3 transport test through the actual container handler for all
three stages, requiring no-GPU failures to remain failures. It also checks input
tampering produces no output. This is transport integration, not live AWS or GPU
certification. Candidate `candidate-sm86-*` tags now select the AWS transport.
The registry digest binds the complete image including the transport; the pipeline
inventory separately binds the numerical kernels and handler files.
