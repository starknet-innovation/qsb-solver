# Validation tools only; preserve the exact candidate image's solver/runtime files.
FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7 AS tools
FROM ghcr.io/starknet-innovation/qsb-solver@sha256:9e86d94a66d7893e31d8e8d6bec7ddbc9b59f47f09e2f7a6015679fd95ab8b52
COPY --from=tools /usr/local/cuda-12.8/compute-sanitizer /opt/compute-sanitizer
RUN /opt/compute-sanitizer/compute-sanitizer --version && python3 -c "import handler; b=handler.release_binding(); assert b['files']['pinning']=='4602c9845d7db1336b5ad00d67348063dce2c164bed3005ba18624f8c3dc6fa7'; assert b['files']['subset']=='1c7d6b5906e95c12f07faf08f93cfe5ca920974c9cb936909548b81b82dade3a'"
