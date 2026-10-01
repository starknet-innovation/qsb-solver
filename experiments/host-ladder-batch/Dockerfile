FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7
RUN apt-get update && apt-get install -y --no-install-recommends python3 libssl-dev && rm -rf /var/lib/apt/lists/*
WORKDIR /src
COPY . /src
RUN python3 experiments/host-ladder-batch/prepare.py /results && g++ -O3 -std=c++17 /results/ladder.cpp -lcrypto -o /results/host-ladder-gate && sha256sum /results/host-ladder-gate > /results/binary.sha256 && ldd /results/host-ladder-gate > /results/runtime-dependencies.txt && g++ --version > /results/compiler.txt && openssl version -a > /results/openssl-build.txt
ENTRYPOINT ["/results/host-ladder-gate"]
