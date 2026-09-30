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
mkdir /var/tmp/qsb-a10g-results
results=/var/tmp/qsb-a10g-results
finish() {
 status=$?
 trap - EXIT
 set +e
 printf '%s\n' "$status" > "$results/exit-code.txt"
 timeout --signal=TERM --kill-after=2s 10 docker rm -f qsb-host-ladder-table-gate > "$results/cleanup.log" 2>&1
 cleanup_status=$?
 printf '%s\n' "$cleanup_status" > "$results/cleanup-exit-code.txt"
timeout --signal=TERM --kill-after=5s 30 python3 - "$results" <<'QSB_ENVELOPE'
import base64,gzip,hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1]);files={p.name:p.read_text() for p in root.iterdir() if p.is_file()}
raw=json.dumps(files).encode()
if len(raw)>8000000:raise ValueError('result too large')
data=base64.b64encode(gzip.compress(raw))
if len(data)>2000000:raise ValueError('encoded result too large')
with (root/'public-result.b64').open('xb') as f:f.write(data)
print('QSB_PUBLIC_RESULT_META='+json.dumps({'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}))
QSB_ENVELOPE
 collection_status=$?
 if [ "$collection_status" -ne 0 ]; then
  printf 'QSB_COLLECTION_ERROR exit=%s gate_exit=%s\n' "$collection_status" "$status" >&2
  [ "$status" -ne 0 ] || status=70
 fi
 exit "$status"
}
trap finish EXIT
sha256sum -c SHA256SUMS > "$results/staging.log" 2>&1
sha256sum table-gate > "$results/binary.sha256"
printf '%s\n' "$image" > "$results/runtime.txt"
[ "$((deadline-$(date -u +%s)))" -ge 1080 ]
timeout --signal=TERM --kill-after=10s 300 docker pull "$image" > "$results/pull.log" 2>&1
[ "$((deadline-$(date -u +%s)))" -ge 780 ]
nvidia-smi --query-gpu=name,uuid,driver_version --format=csv,noheader > "$results/gpu.txt"
printf '%s\n' "$deadline" > "$results/deadline.txt"
set +e
timeout --signal=TERM --kill-after=10s 720 docker run --rm --name qsb-host-ladder-table-gate --gpus all \
 --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
 --tmpfs /tmp:rw,exec,nosuid,nodev,size=512m \
 --mount type=bind,src=/opt/qsb-a10g-gate,dst=/gate,readonly \
 --mount type=bind,src="$results",dst=/results \
 --entrypoint timeout "$image" --signal=TERM --kill-after=10s 600 bash -c '
set -euo pipefail
for tool in memcheck racecheck synccheck; do
 compute-sanitizer --tool "$tool" --error-exitcode 42 /gate/table-gate "/results/$tool.json" --correctness-only > "/results/$tool.log" 2>&1
done
/gate/table-gate /results/normal.json > /results/normal.log 2>&1' > "$results/gate.log" 2>&1
status=$?
exit "$status"
