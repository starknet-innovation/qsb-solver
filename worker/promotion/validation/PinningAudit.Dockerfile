ARG PINNING_BUILD_IMAGE=qsb-pinning-build:audit
FROM ${PINNING_BUILD_IMAGE}
COPY worker/promotion/validation/build_pinning_audit.py /audit/
RUN python3 /audit/build_pinning_audit.py
