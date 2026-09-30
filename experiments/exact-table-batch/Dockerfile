# Native build only; no GPU or solver execution during image construction.
FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends python3 libssl-dev && rm -rf /var/lib/apt/lists/*
WORKDIR /src
COPY research/optimized-subset/subset/ research/optimized-subset/subset/
COPY experiments/exact-table-batch/ experiments/exact-table-batch/
RUN python3 experiments/exact-table-batch/prepare.py /results \
 && nvcc --version > /results/compiler.txt \
 && nvcc -O3 -arch=sm_86 -Xptxas=-v /results/table-gate.cu -lcrypto -o /results/table-gate > /results/build.log 2>&1 \
 && cuobjdump --dump-sass /results/table-gate > /results/table-gate.sass \
 && sha256sum /results/table-gate > /results/binary.sha256 \
 && ldd /results/table-gate > /results/ldd.txt
