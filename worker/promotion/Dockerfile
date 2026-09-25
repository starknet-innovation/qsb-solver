# Native Linux builder stages supplied by the repository's two pinned recipes.
ARG HISTORICAL_IMAGE
ARG OPTIMIZED_IMAGE
FROM ${HISTORICAL_IMAGE} AS historical
FROM ${OPTIMIZED_IMAGE} AS optimized
FROM historical AS candidate
ARG SOLVER_COMMIT
ENV SOLVER_COMMIT=${SOLVER_COMMIT}
COPY --from=optimized /opt/qsb-validation/candidate/subset /opt/qsb/subset
COPY --from=optimized /opt/qsb-validation/build-receipt.json /opt/qsb/optimized-build-receipt.json
COPY --from=optimized /opt/qsb-validation/candidate/source /opt/qsb/optimized-source
COPY worker/handler.py /opt/qsb/historical_handler.py
COPY worker/promotion/handler.py worker/promotion/bind.py /opt/qsb/
RUN python3 /opt/qsb/bind.py && rm /opt/qsb/bind.py
ENV PYTHONDONTWRITEBYTECODE=1
CMD ["python3", "handler.py"]
