#!/bin/bash
# Native correctness and matched timing of the ranked PQB grinder. One-shot per host.
# The hash-verified public bundle (scripts/prepare_pqb_measure_bundle.py) is staged by the
# operator before invocation. The published combined image is used only as a CUDA runtime with
# python3; the binaries under test are the bundle's. This script launches no instance and grants
# no authorization: it runs on a host an authorized session already started.
set -euo pipefail
bundle=$1
results=$2
deadline=$3
bundle_sha=$4
[[ "$bundle_sha" =~ ^[0-9a-f]{64}$ ]]
[[ "$bundle" = /opt/qsb-pqb-measure && "$results" = /var/tmp/qsb-pqb-measure-results ]]
[[ "$deadline" =~ ^[0-9]{10}$ ]]
[ -f /run/qsb-shutdown-armed ]
systemctl is-active --quiet qsb-benchmark-expire.timer
cd "$bundle"
[ "$(sha256sum SHA256SUMS | cut -d' ' -f1)" = "$bundle_sha" ]
sha256sum -c SHA256SUMS
[ -x "$bundle/grind-ranked" ] && [ -x "$bundle/grind-upstream" ]
mkdir "$results"
# Persist before image setup; never repeat this host operation after uncertainty.
printf '%s\n' "$deadline" > "$results/deadline.txt"
image=ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48
timeout --signal=TERM --kill-after=10s 300 docker pull "$image"
[ "$((deadline-$(date -u +%s)))" -ge 780 ]
nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader > "$results/gpu.txt"
set +e
timeout --signal=TERM --kill-after=10s 720 docker run --name qsb-pqb-measure --rm --gpus all \
  --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
  --tmpfs /tmp:rw,nosuid,nodev,size=256m \
  --mount "type=bind,src=$bundle,dst=/gate,readonly" \
  --mount "type=bind,src=$results,dst=/results" \
  --env QSB_MEASURE_DEADLINE=600 \
  --entrypoint python3 "$image" /gate/run_measure.py /gate /results/result.json > "$results/gate.log" 2>&1
status=$?
set -e
# Killing the Docker client does not reliably stop its container.
docker rm --force qsb-pqb-measure >/dev/null 2>&1 || true
printf '%s\n' "$status" > "$results/exit-code.txt"
python3 - "$results" <<'PY'
import base64,gzip,hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1])
files={str(p.relative_to(root)):p.read_text() for p in root.rglob('*') if p.is_file()}
encoded=base64.b64encode(gzip.compress(json.dumps(files).encode()))
(root/'public-result.b64').write_bytes(encoded)
print('QSB_PUBLIC_RESULT_META='+json.dumps(dict(bytes=len(encoded),sha256=hashlib.sha256(encoded).hexdigest())))
PY
exit "$status"
