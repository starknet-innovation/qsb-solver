ARG PINNING_BUILD_IMAGE=qsb-pinning-build:audit
FROM ${PINNING_BUILD_IMAGE}
COPY worker/promotion/validation/build_pinning_trace.py worker/promotion/validation/corrected_pinning_trace.py /audit/
RUN python3 /audit/build_pinning_trace.py
