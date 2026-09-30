#!/bin/bash
# Frozen CI artifact and committed sources must be staged and hash checked first.
set -euo pipefail
image=$1
deadline=$2
[[ "$image" =~ ^ghcr.io/starknet-innovation/qsb-solver@sha256:[0-9a-f]{64}$ ]]
[[ "$deadline" =~ ^[0-9]{10}$ ]]
[ -f /run/qsb-shutdown-armed ]
systemctl is-active --quiet qsb-benchmark-expire.timer
cd /opt/qsb-a10g-gate
sha256sum -c SHA256SUMS
mkdir /var/tmp/qsb-a10g-results
results=/var/tmp/qsb-a10g-results
[ "$((deadline-$(date -u +%s)))" -ge 1080 ]
timeout --signal=TERM --kill-after=10s 300 docker pull "$image" > "$results/pull.log" 2>&1
[ "$((deadline-$(date -u +%s)))" -ge 780 ]
nvidia-smi --query-gpu=name,uuid,driver_version --format=csv,noheader > "$results/gpu.txt"
printf '%s\n' "$deadline" > "$results/deadline.txt"
trap 'docker rm -f qsb-table-gate >/dev/null 2>&1 || true' EXIT
set +e
timeout --signal=TERM --kill-after=10s 720 docker run --rm --name qsb-table-gate --gpus all \
 --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
 --tmpfs /tmp:rw,exec,nosuid,nodev,size=512m \
 --mount type=bind,src=/opt/qsb-a10g-gate,dst=/gate,readonly \
 --mount type=bind,src="$results",dst=/results \
 --entrypoint timeout "$image" --signal=TERM --kill-after=10s 600 bash -c '
set -euo pipefail
/gate/table-gate /results/normal.json > /results/normal.log 2>&1
for tool in memcheck racecheck synccheck; do
 compute-sanitizer --tool "$tool" --error-exitcode 42 /gate/table-gate "/results/$tool.json" --correctness-only > "/results/$tool.log" 2>&1
done
' > "$results/gate.log" 2>&1
status=$?
set -e
docker rm -f qsb-table-gate >/dev/null 2>&1 || true
printf '%s\n' "$status" > "$results/exit-code.txt"
python3 - "$results" <<'QSB_ENVELOPE'
import base64,gzip,hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1]);files={p.name:p.read_text() for p in root.iterdir() if p.is_file()}
raw=json.dumps(files).encode()
if len(raw)>8000000:raise ValueError('result too large')
data=base64.b64encode(gzip.compress(raw))
if len(data)>2000000:raise ValueError('encoded result too large')
with (root/'public-result.b64').open('xb') as f:f.write(data)
print('QSB_PUBLIC_RESULT_META='+json.dumps({'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}))
QSB_ENVELOPE
exit "$status"
