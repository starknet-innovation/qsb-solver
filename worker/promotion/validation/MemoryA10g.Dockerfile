# Validation tools only; preserve the exact candidate image's solver/runtime files.
FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7 AS tools
FROM ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48
COPY --from=tools /usr/local/cuda-12.8/compute-sanitizer /opt/compute-sanitizer
RUN /opt/compute-sanitizer/compute-sanitizer --version && python3 -c "import handler; b=handler.release_binding(); assert b['files']['pinning']=='cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62'; assert b['files']['subset']=='673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15'"
