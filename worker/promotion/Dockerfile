# Native Linux builder stages supplied by the repository's two pinned recipes.
ARG HISTORICAL_IMAGE
ARG OPTIMIZED_IMAGE
FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7 AS repaired-pinning
RUN apt-get update && apt-get install -y --no-install-recommends python3 libssl-dev && rm -rf /var/lib/apt/lists/*
WORKDIR /src
COPY vendor/challenge/candidates /src/vendor/challenge/candidates
COPY worker/prepare_kernels.py /src/worker/prepare_kernels.py
COPY worker/promotion/prepare_pinning.py worker/promotion/pinning_output.h /src/worker/promotion/
RUN python3 worker/promotion/prepare_pinning.py /opt/repaired-pinning && nvcc -O3 -arch=sm_89 -DQSB_SLOTPIPE=0 -o /pinning /opt/repaired-pinning/pinning.cu -lcrypto -lm
FROM ${HISTORICAL_IMAGE} AS historical
FROM ${OPTIMIZED_IMAGE} AS optimized
FROM historical AS candidate
ARG SOLVER_COMMIT
COPY --from=repaired-pinning /pinning /opt/qsb/pinning
COPY --from=repaired-pinning /opt/repaired-pinning /opt/qsb/source/pinning
ENV SOLVER_COMMIT=${SOLVER_COMMIT}
COPY --from=optimized /opt/qsb-validation/candidate/subset /opt/qsb/subset
COPY --from=optimized /opt/qsb-validation/build-receipt.json /opt/qsb/optimized-build-receipt.json
COPY --from=optimized /opt/qsb-validation/candidate/source /opt/qsb/optimized-source
COPY worker/handler.py /opt/qsb/historical_handler.py
COPY worker/promotion/handler.py worker/promotion/bind.py /opt/qsb/
RUN python3 /opt/qsb/bind.py && rm /opt/qsb/bind.py
ENV PYTHONDONTWRITEBYTECODE=1
CMD ["python3", "handler.py"]
