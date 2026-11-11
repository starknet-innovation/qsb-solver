# PQB candidate worker (HOLD). Separate from the historical and combined QSB images: nothing here
# enters those, and no release workflow publishes this target.
FROM nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7 AS build
RUN apt-get update && apt-get install -y --no-install-recommends python3 && rm -rf /var/lib/apt/lists/*
WORKDIR /src
COPY vendor/pqb /src/vendor/pqb
COPY research/pqb-ranked/grind.cu research/pqb-ranked/source-lock.json /src/research/pqb-ranked/
COPY worker/pqb/build.py /src/worker/pqb/build.py
ENV PYTHONDONTWRITEBYTECODE=1
ARG CUDA_ARCH=86
RUN CUDA_ARCH=${CUDA_ARCH} python3 /src/worker/pqb/build.py
# Not a runtime target, and deliberately not the last stage: a build without --target gives the
# worker (aws). Binaries for a native measurement: the ranked grinder exactly as the
# worker gets it, and upstream's unmodified grinder with the same compiler and flags.
FROM build AS measure
ARG CUDA_ARCH=86
RUN mkdir /measure \
 && cp /opt/qsb-pqb/grind /measure/grind-ranked \
 && cp /opt/qsb-pqb/build-receipt.json /measure/build-receipt.json \
 && nvcc -O3 -std=c++17 -arch=sm_${CUDA_ARCH} -I /src/vendor/pqb/grinder -o /measure/grind-upstream /src/vendor/pqb/grinder/grind.cu \
 && cd /measure && sha256sum grind-ranked grind-upstream build-receipt.json > SHA256SUMS
FROM nvidia/cuda:12.8.1-runtime-ubuntu22.04@sha256:fcbbd60a5ad3db3a1c7375bf14546b369b54064c513224310b2026df50c7a9bd AS runtime
# Same Ubuntu-only update as worker/Dockerfile: the pinned CUDA user-space packages stay unchanged.
# Ubuntu's mirrors are briefly inconsistent after a package is superseded (index lists a file
# that is already gone). Refresh the index and try again, at most three times.
RUN for attempt in 1 2 3; do \
      apt-get -o Dir::Etc::SourceParts=/nonexistent update \
   && DEBIAN_FRONTEND=noninteractive apt-get -o Dir::Etc::SourceParts=/nonexistent upgrade -y \
   && apt-get -o Dir::Etc::SourceParts=/nonexistent install -y --no-install-recommends python3 python3-pip \
   && break; \
      [ "$attempt" -lt 3 ] || exit 1; \
      sleep 20; \
    done \
 && rm -rf /var/lib/apt/lists/*
WORKDIR /opt/qsb-pqb
COPY --from=build /opt/qsb-pqb/grind /opt/qsb-pqb/build-receipt.json ./
COPY worker/pqb/pqb_handler.py worker/pqb/pqb_ranges.py worker/pqb/bind.py ./
COPY worker/pqb/aws_handler.py ./handler.py
# Upstream and adapted source, their notices and the build inputs travel with the binary.
COPY vendor/pqb /opt/qsb-pqb/source/vendor/pqb
COPY research/pqb-ranked/grind.cu research/pqb-ranked/source-lock.json /opt/qsb-pqb/source/research/pqb-ranked/
COPY worker/pqb/build.py worker/pqb/Dockerfile /opt/qsb-pqb/source/build/
COPY vendor/pqb/LICENSE /opt/qsb-pqb/licenses/pqb-LICENSE
COPY vendor/pqb/THIRD_PARTY_NOTICES.md /opt/qsb-pqb/licenses/pqb-THIRD_PARTY_NOTICES.md
COPY LICENSES.md /opt/qsb-pqb/licenses/LICENSES.md
ARG SOLVER_COMMIT
ARG CUDA_ARCH=86
RUN SOLVER_COMMIT=${SOLVER_COMMIT} CUDA_ARCH=${CUDA_ARCH} python3 /opt/qsb-pqb/bind.py && rm /opt/qsb-pqb/bind.py
ENV PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
FROM runtime AS aws
RUN python3 -m pip install --no-cache-dir boto3==1.42.0
COPY worker/aws/entrypoint.py /opt/qsb-pqb/aws_entrypoint.py
CMD ["python3", "aws_entrypoint.py"]

