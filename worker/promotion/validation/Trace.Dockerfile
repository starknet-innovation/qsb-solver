ARG OPTIMIZED_BUILD_IMAGE=qsb-optimized-build:audit
FROM ${OPTIMIZED_BUILD_IMAGE} AS audit
COPY worker/promotion/validation/build_trace.py /audit/
RUN python3 /audit/build_trace.py
