ARG OPTIMIZED_BUILD_IMAGE=qsb-optimized-build:audit
FROM ${OPTIMIZED_BUILD_IMAGE} AS audit
COPY worker/promotion/validation/build_curve.py worker/promotion/validation/curve_vectors.py /audit/
RUN python3 /audit/build_curve.py
