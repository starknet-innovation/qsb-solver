# Built from the runtime target of worker/Dockerfile in this exact checkout.
FROM qsb-solver-runtime:sm86
RUN python3 -m pip install --no-cache-dir boto3==1.42.0
COPY worker/aws/entrypoint.py /opt/qsb/aws_entrypoint.py
CMD ["python3", "aws_entrypoint.py"]
