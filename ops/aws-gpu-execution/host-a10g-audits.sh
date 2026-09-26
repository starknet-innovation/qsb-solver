#!/bin/bash
# Hash-verified public gate bundle is staged by the operator before invocation.
set -euo pipefail
bundle=$1
results=$2
deadline=$3
manifest_sha=$4
[[ "$manifest_sha" =~ ^[0-9a-f]{64}$ ]]
[[ "$bundle" = /opt/qsb-a10g-gate && "$results" = /var/tmp/qsb-a10g-results ]]
[[ "$deadline" =~ ^[0-9]{10}$ ]]
[ -f /run/qsb-shutdown-armed ]
systemctl is-active --quiet qsb-benchmark-expire.timer
cd "$bundle"
sha256sum -c SHA256SUMS
mkdir "$results"
# Persist before image setup; never repeat this host operation after uncertainty.
printf '%s\n' "$deadline" > "$results/deadline.txt"
image=ghcr.io/starknet-innovation/qsb-solver@sha256:c05d39a303971baaca6908b19427158d0428963f16b57c5e823432b50ddf307b
timeout --signal=TERM --kill-after=10s 300 docker pull "$image"
[ "$((deadline-$(date -u +%s)))" -ge 780 ]
nvidia-smi --query-gpu=name,uuid,driver_version --format=csv,noheader > "$results/gpu.txt"
set +e
timeout --signal=TERM --kill-after=10s 720 docker run --name qsb-a10g-gate --rm --gpus all \
  --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
  --tmpfs /tmp:rw,exec,nosuid,nodev,size=256m \
  --mount "type=bind,src=$bundle,dst=/gate,readonly" \
  --mount "type=bind,src=$results,dst=/results" \
  --entrypoint python3 "$image" /gate/run_a10g_audits.py /gate /results/result.json "$manifest_sha" > "$results/gate.log" 2>&1
status=$?
set -e
# Killing the Docker client does not reliably stop its container.
docker rm --force qsb-a10g-gate >/dev/null 2>&1 || true
printf '%s\n' "$status" > "$results/exit-code.txt"
python3 - "$results" <<'PY'
import base64,gzip,hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1])
files={p.name:p.read_text() for p in root.iterdir() if p.is_file()}
encoded=base64.b64encode(gzip.compress(json.dumps(files).encode()))
(root/'public-result.b64').write_bytes(encoded)
print('QSB_PUBLIC_RESULT_META='+json.dumps(dict(bytes=len(encoded),sha256=hashlib.sha256(encoded).hexdigest())))
PY
exit "$status"
