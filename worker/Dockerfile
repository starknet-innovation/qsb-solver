FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7 AS build
RUN apt-get update && apt-get install -y --no-install-recommends libssl-dev python3 && rm -rf /var/lib/apt/lists/*
ARG CUDA_ARCH=89
WORKDIR /build
COPY vendor/challenge/candidates /src/vendor/challenge/candidates
COPY worker/prepare_kernels.py /src/worker/prepare_kernels.py
RUN python3 /src/worker/prepare_kernels.py
RUN nvcc -O3 -arch=sm_${CUDA_ARCH} -DQSB_SLOTPIPE=0 -o /pinning /src/worker/build/pinning/pinning.cu -lcrypto -lm
RUN nvcc -O3 -arch=sm_${CUDA_ARCH} -DZLAB_TRIM=0 -DZLAB_K2S=0 -o /subset /src/worker/build/subset/subset.cu -lcrypto -lm
FROM nvidia/cuda:12.8.1-runtime-ubuntu22.04@sha256:fcbbd60a5ad3db3a1c7375bf14546b369b54064c513224310b2026df50c7a9bd AS runtime
RUN apt-get update && apt-get install -y --no-install-recommends python3 python3-pip libssl3 && rm -rf /var/lib/apt/lists/*
WORKDIR /opt/qsb
COPY --from=build /pinning /subset ./
COPY --from=build /src/worker/build /opt/qsb/source
COPY worker/handler.py worker/search_ranges.py ./
COPY vendor/challenge/LICENSE /opt/qsb/licenses/challenge-LICENSE
COPY vendor/challenge/candidates/pinning/COPYING /opt/qsb/licenses/pinning-COPYING
COPY vendor/challenge/candidates/subset/COPYING /opt/qsb/licenses/subset-COPYING
COPY LICENSES.md /opt/qsb/licenses/LICENSES.md
# Keep adaptation/build inputs alongside the adapted source and embedded notices.
COPY worker/prepare_kernels.py worker/Dockerfile /opt/qsb/source/build/
COPY vendor/challenge/provenance.json /opt/qsb/source/provenance.json
ENV PYTHONUNBUFFERED=1
FROM runtime AS aws
RUN python3 -m pip install --no-cache-dir boto3==1.42.0
COPY worker/aws/entrypoint.py /opt/qsb/aws_entrypoint.py
CMD ["python3", "aws_entrypoint.py"]
FROM runtime AS runpod
RUN python3 -m pip install --no-cache-dir runpod==1.7.13
CMD ["python3", "handler.py"]
