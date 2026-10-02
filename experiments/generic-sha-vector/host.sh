#!/bin/bash
set -euo pipefail
deadline=$1
[[ "$deadline" =~ ^[0-9]{10}$ ]]
[ -f /run/qsb-shutdown-armed ]
systemctl is-active --quiet qsb-benchmark-expire.timer
[ "$((deadline-$(date -u +%s)))" -ge 780 ]
image=nvidia/cuda:12.8.1-devel-ubuntu22.04@sha256:6617a625f4090c76c545a0e7d63f2e441718ef9af7f4efe7dd1242a29e289fd7
timeout 300 docker pull "$image" >/var/tmp/qsb-sha-pull.log 2>&1
[ "$((deadline-$(date -u +%s)))" -ge 780 ]
mkdir /var/tmp/qsb-sha-results
nvidia-smi --query-gpu=name,driver_version --format=csv,noheader > /var/tmp/qsb-sha-results/gpu.txt
trap 'docker rm -f qsb-sha-vector >/dev/null 2>&1 || true' EXIT
set +e
timeout --signal=TERM --kill-after=10s 720 docker run --name qsb-sha-vector --rm --gpus all --network none --read-only --cap-drop ALL --security-opt no-new-privileges --tmpfs /tmp:rw,exec,nosuid,nodev,size=512m --mount type=bind,src=/opt/qsb-sha-gate,dst=/gate,readonly --mount type=bind,src=/var/tmp/qsb-sha-results,dst=/results --entrypoint bash "$image" -c '
set -euo pipefail
nvcc --version > /results/compiler.txt
timeout 180 nvcc -O3 -arch=sm_86 -std=c++17 -Xptxas=-v /gate/gate.cu -o /tmp/gate
sha256sum /tmp/gate > /results/binary.sha256
timeout 120 /tmp/gate > /results/native.json
timeout 180 compute-sanitizer --tool memcheck --error-exitcode 9 /tmp/gate > /results/memcheck.txt 2>&1
cuobjdump --dump-sass /tmp/gate > /tmp/gate.sass
{ grep -c "LDG.*128" /tmp/gate.sass || true; } > /results/vector-load-count.txt
' > /var/tmp/qsb-sha-results/gate.log 2>&1
status=$?
set -e
docker rm -f qsb-sha-vector >/dev/null 2>&1 || true
printf '%s\n' "$status" > /var/tmp/qsb-sha-results/exit-code.txt
python3 - <<'PY'
import pathlib,json,gzip,base64,hashlib
r=pathlib.Path('/var/tmp/qsb-sha-results')
d={p.name:p.read_text() for p in r.iterdir() if p.is_file()}
b=base64.b64encode(gzip.compress(json.dumps(d).encode()))
assert len(b)<16000
print('RESULT_SHA256='+hashlib.sha256(b).hexdigest())
print('RESULT_BASE64='+b.decode())
PY
exit "$status"
