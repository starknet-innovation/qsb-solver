FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7
RUN apt-get update && apt-get install -y --no-install-recommends python3 && rm -rf /var/lib/apt/lists/*
COPY research/optimized-subset /src/research/optimized-subset
COPY experiments/sha-constant-index /src/experiments/sha-constant-index
RUN python3 /src/experiments/sha-constant-index/build.py
