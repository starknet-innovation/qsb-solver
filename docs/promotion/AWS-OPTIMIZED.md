# Optimized solver on AWS A10G

The exact sm86 combined image is published and its descriptor enrolled in qsb-app;
see [verified status](../README.md). Native correctness and matched per-stage
performance are recorded in [the publication record](2026-09-26-publication.md).
New image identities require their own evidence assessment. This guide grants no
cloud budget, wallet access, deployment or transaction authorization.

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

## AWS transport integration

The combined worker includes main's AWS transport and license packaging.
Combined candidates use the explicit `aws` Docker target (the `runpod` target was
retired on 1 October 2026). The AWS target
starts `aws_entrypoint.py`, uses the same combined handler and release binding,
and keeps the public-only S3 input digest and immutable output protocol. CI runs
an offline fake-S3 transport test through the actual container handler for all
three stages, requiring no-GPU failures to remain failures. It also checks input
tampering produces no output. This is transport integration, not live AWS or GPU
certification. Candidate `candidate-sm86-*` tags now select the AWS transport.
The registry digest binds the complete image including the transport; the pipeline
inventory separately binds the numerical kernels and handler files.
