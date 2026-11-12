#!/bin/bash
# Final-image qualification: one stage, one already armed 25-minute session.
set -euo pipefail
bundle=$1
results=$2
deadline=$3
bundle_sha=$4
stage=$5
[[ "$bundle" = /opt/qsb-pqb-final && "$results" = /var/tmp/qsb-pqb-final-results ]]
[[ "$deadline" =~ ^[0-9]{10}$ && "$bundle_sha" =~ ^[0-9a-f]{64}$ ]]
[[ "$stage" = pinning || "$stage" = round0 || "$stage" = round1 ]]
[ -f /run/qsb-shutdown-armed ]
systemctl is-active --quiet qsb-benchmark-expire.timer
cd "$bundle"
[ "$(sha256sum SHA256SUMS | cut -d' ' -f1)" = "$bundle_sha" ]
sha256sum -c SHA256SUMS
mkdir "$results"
collect() {
  status=$?
  trap - EXIT
  docker rm --force qsb-pqb-final > "$results/container-cleanup.log" 2>&1 || true
  printf '%s\n' "$status" > "$results/exit-code.txt"
  python3 - "$results" <<'PY'
import gzip,hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1])
files={str(p.relative_to(root)):p.read_text() for p in root.rglob('*') if p.is_file()}
raw=gzip.compress(json.dumps(files).encode())
(root/'public-result.json.gz').write_bytes(raw)
print('QSB_PUBLIC_RESULT_META='+json.dumps(dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())))
PY
  return "$status"
}
trap collect EXIT
printf '%s\n' "$deadline" > "$results/deadline.txt"
printf '%s\n' "$bundle_sha" > "$results/bundle-sha256.txt"
printf '%s\n' "$stage" > "$results/stage.txt"
timeout 120 apt-get update > "$results/apt-update.log" 2>&1
timeout 120 apt-get install -y skopeo > "$results/apt-install.log" 2>&1
skopeo --version > "$results/skopeo-version.txt"
timeout 180 skopeo copy "oci-archive:$bundle/image.oci.tar" docker-daemon:qsb-pqb:final > "$results/image-import.log" 2>&1
docker inspect qsb-pqb:final > "$results/image.json"
python3 - "$bundle" "$results" <<'PY'
import json,pathlib,sys
bundle,results=map(pathlib.Path,sys.argv[1:])
identity=json.loads((bundle/'gate/oci-identity.json').read_text())
config=json.loads((bundle/'image-config.json').read_text())
image=json.loads((results/'image.json').read_text())[0]
# Docker's containerd store can label .Id with an index/manifest digest. Compare the
# actual rootfs diff IDs and every recorded runtime config field instead of guessing
# that .Id must name the config blob. Import may transcode manifest media types.
assert image['Architecture']==config['architecture'] and image['Os']==config['os']
assert image['RootFS']['Layers']==config['rootfs']['diff_ids'], 'Imported rootfs differs'
for key,value in config['config'].items():
    assert image['Config'].get(key)==value, 'Imported runtime config differs: '+key
assert image['Config']['WorkingDir']=='/opt/qsb-pqb'
assert image['Config']['Cmd']==['python3','aws_entrypoint.py']
(results/'runtime-identity-check.json').write_text(json.dumps(dict(status='passed',
    imageDigest=identity['imageDigest'],configDigest=identity['configDigest'],
    dockerInspectId=image['Id'],rootfsDiffIdsMatched=True,runtimeConfigMatched=True),indent=2)+'\n')
PY
[ "$((deadline-$(date -u +%s)))" -ge 1100 ]
nvidia-smi --query-gpu=name,uuid,driver_version,memory.total --format=csv,noheader > "$results/gpu.txt"
timeout --signal=TERM --kill-after=10s 1000 docker run --name qsb-pqb-final --rm --gpus all \
  --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
  --tmpfs /tmp:rw,nosuid,nodev,size=256m \
  --mount "type=bind,src=$bundle/gate,dst=/gate,readonly" \
  --mount "type=bind,src=$results,dst=/results" \
  --env PYTHONDONTWRITEBYTECODE=1 \
  --entrypoint python3 qsb-pqb:final /gate/qualify_image.py /gate /results/unit "$stage" > "$results/gate.log" 2>&1
