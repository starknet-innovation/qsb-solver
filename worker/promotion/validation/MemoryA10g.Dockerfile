# Validation tools only; preserve the exact candidate image's solver/runtime files.
FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7 AS tools
FROM ghcr.io/starknet-innovation/qsb-solver@sha256:e22afc720df17dd280678e610ea0861dcbd297e17baf6b9a5a264782aeb7f32d
COPY --from=tools /usr/local/cuda-12.8/compute-sanitizer /opt/compute-sanitizer
RUN /opt/compute-sanitizer/compute-sanitizer --version && python3 -c "import handler; b=handler.release_binding(); assert b['files']['pinning']=='cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62'; assert b['files']['subset']=='673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15'"
