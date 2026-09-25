ARG OPTIMIZED_BUILD_IMAGE=qsb-optimized-build:audit
FROM ${OPTIMIZED_BUILD_IMAGE}
COPY worker/promotion/validation/build_edge_audit.py /audit/
RUN python3 /audit/build_edge_audit.py
