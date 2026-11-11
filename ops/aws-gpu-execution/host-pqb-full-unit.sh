#!/bin/bash
# One stage per separately authorized 25-minute session. Launches nothing, extends no deadline.
set -euo pipefail
bundle=$1
results=$2
deadline=$3
bundle_sha=$4
stage=$5
[[ "$bundle_sha" =~ ^[0-9a-f]{64}$ ]]
[[ "$bundle" = /opt/qsb-pqb-full-unit && "$results" = /var/tmp/qsb-pqb-full-unit-results ]]
[[ "$deadline" =~ ^[0-9]{10}$ ]]
[[ "$stage" = pinning || "$stage" = round0 || "$stage" = round1 ]]
[ -f /run/qsb-shutdown-armed ]
systemctl is-active --quiet qsb-benchmark-expire.timer
cd "$bundle"
[ "$(sha256sum SHA256SUMS | cut -d' ' -f1)" = "$bundle_sha" ]
sha256sum -c SHA256SUMS
[ -x "$bundle/worker/grind" ]
mkdir "$results"                            # persist before image setup; never repeat after uncertainty
printf '%s\n' "$deadline" > "$results/deadline.txt"
printf '%s\n' "$bundle_sha" > "$results/bundle-sha256.txt"
printf '%s\n' "$stage" > "$results/stage.txt"
image=ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48
status=1
collect() {
  # Killing a Docker client does not reliably stop its container.
  docker rm --force qsb-pqb-full-unit >/dev/null 2>&1 || true
  printf '%s\n' "$status" > "$results/exit-code.txt"
  python3 - "$results" <<'PY'
import base64,gzip,hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1])
files={str(p.relative_to(root)):p.read_text() for p in root.rglob('*') if p.is_file()}
encoded=base64.b64encode(gzip.compress(json.dumps(files).encode()))
(root/'public-result.b64').write_bytes(encoded)
print('QSB_PUBLIC_RESULT_META='+json.dumps(dict(bytes=len(encoded),sha256=hashlib.sha256(encoded).hexdigest())))
PY
}
trap collect EXIT
timeout --signal=TERM --kill-after=10s 300 docker pull "$image" > "$results/image-pull.log" 2>&1
# 1,000 s container bound plus collection/termination margin. Refuse, never extend, a short session.
[ "$((deadline-$(date -u +%s)))" -ge 1100 ]
nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader > "$results/gpu.txt"
set +e
timeout --signal=TERM --kill-after=10s 1000 docker run --name qsb-pqb-full-unit --rm --gpus all \
  --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
  --tmpfs /tmp:rw,nosuid,nodev,size=256m \
  --mount "type=bind,src=$bundle,dst=/gate,readonly" \
  --mount "type=bind,src=$results,dst=/results" \
  --env PYTHONDONTWRITEBYTECODE=1 \
  --entrypoint python3 "$image" /gate/run_full_unit.py /gate /results/unit "$stage" > "$results/gate.log" 2>&1
status=$?
set -e
exit "$status"
