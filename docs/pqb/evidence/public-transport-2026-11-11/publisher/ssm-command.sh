set -euo pipefail
DEADLINE=1794430309
bash -s -- "$DEADLINE" <<'QSB_READY'
#!/bin/bash
# SSM Online is not cloud-init completion. Call before staging or compute.
set -euo pipefail
deadline=$1
[[ "$deadline" =~ ^[0-9]{10}$ ]]
# Leave at least 13 minutes for the existing gate and five minutes for pull/setup.
end=$(( $(date -u +%s) + 180 ))
while true; do
  now=$(date -u +%s)
  [ "$((deadline-now))" -ge 1080 ] || exit 2
  if [ -f /run/qsb-shutdown-armed ] && systemctl is-active --quiet qsb-benchmark-expire.timer && systemctl is-active --quiet cloud-final.service; then
    echo QSB_HOST_READY
    exit 0
  fi
  [ "$now" -lt "$end" ] || exit 3
  sleep 2
done

QSB_READY
mkdir /opt/qsb-private-publisher
mkdir /var/tmp/qsb-publisher-results
collect() {
 status=$?
 trap - EXIT
 docker rm --force qsb-pqb-private-publisher > /var/tmp/qsb-publisher-results/container-cleanup.log 2>&1 || true
 printf '%s\n' "$status" > /var/tmp/qsb-publisher-results/exit-code.txt
 python3 - <<'QSB_COLLECT'
import pathlib,json,base64,gzip,hashlib
root=pathlib.Path('/var/tmp/qsb-publisher-results')
files={str(p.relative_to(root)):p.read_text() for p in root.rglob('*') if p.is_file()}
raw=base64.b64encode(gzip.compress(json.dumps(files).encode()))
(root/'public-result.b64').write_bytes(raw)
print('QSB_PUBLIC_RESULT_META='+json.dumps({'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}))
QSB_COLLECT
 return "$status"
}
trap collect EXIT
timeout --kill-after=10s 300 docker pull ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48 > /var/tmp/qsb-publisher-results/runtime-pull.log 2>&1
[ "$((DEADLINE-$(date -u +%s)))" -ge 1050 ]
timeout --kill-after=10s 800 bash -c 'set -euo pipefail
mkdir /opt/qsb-private-publisher/source
cd /opt/qsb-private-publisher/source
git init -q
git remote add origin https://github.com/starknet-innovation/qsb-solver.git
git fetch --depth 1 origin 4bfd8f1f7011331979f33b60bb8c6e379227ca16
git checkout --detach FETCH_HEAD
test "$(git rev-parse HEAD)" = 4bfd8f1f7011331979f33b60bb8c6e379227ca16
test -z "$(git status --porcelain)"
git rev-parse HEAD > /var/tmp/qsb-publisher-results/source-commit.txt
docker version > /var/tmp/qsb-publisher-results/docker-version.txt
docker build --platform linux/amd64 --target aws --build-arg CUDA_ARCH=86 --build-arg SOLVER_COMMIT=4bfd8f1f7011331979f33b60bb8c6e379227ca16 -f worker/pqb/Dockerfile -t qsb-pqb:ci .
python3 worker/pqb/test_image.py qsb-pqb:ci
python3 scripts/image_scan.py docker:qsb-pqb:ci /var/tmp/qsb-publisher-results/pqb-image-scan
mkdir /opt/qsb-private-publisher/artifact
docker inspect qsb-pqb:ci > /opt/qsb-private-publisher/artifact/image.json
docker run --rm --network none --read-only --entrypoint cat qsb-pqb:ci /opt/qsb-pqb/binding.json > /opt/qsb-private-publisher/artifact/binding.json
docker run --rm --network none --read-only --entrypoint cat qsb-pqb:ci /opt/qsb-pqb/build-receipt.json > /var/tmp/qsb-publisher-results/build-receipt.json
python3 - <<'"'"'QSB_BINARY'"'"'
import json
r=json.load(open('"'"'/var/tmp/qsb-publisher-results/build-receipt.json'"'"'))
assert r['"'"'binarySha256'"'"']=='"'"'0e811c59de2d36f66142a6f65393c55a64e0e37c7eb40df4251f86b713ef3d82'"'"'
assert r['"'"'cudaArchitecture'"'"']=='"'"'86'"'"'
QSB_BINARY
printf '"'"'%s\n'"'"' 4bfd8f1f7011331979f33b60bb8c6e379227ca16 > /opt/qsb-private-publisher/artifact/source-commit
docker save qsb-pqb:ci | gzip -1 > /opt/qsb-private-publisher/artifact/image.tar.gz
(cd /opt/qsb-private-publisher/artifact && sha256sum image.json binding.json source-commit image.tar.gz > SHA256SUMS)
cp /opt/qsb-private-publisher/artifact/SHA256SUMS /opt/qsb-private-publisher/artifact/image.json /opt/qsb-private-publisher/artifact/binding.json /var/tmp/qsb-publisher-results/
test -z "$(git status --porcelain)"
docker run --name qsb-pqb-private-publisher --rm --network host --read-only --cap-drop ALL --security-opt no-new-privileges --tmpfs /tmp:rw,nosuid,nodev,size=256m --mount type=bind,src=/opt/qsb-private-publisher,dst=/gate,readonly --mount type=bind,src=/var/tmp/qsb-publisher-results,dst=/results --mount type=bind,src=/var/run/docker.sock,dst=/var/run/docker.sock --mount type=bind,src=/usr/bin/docker,dst=/usr/local/bin/docker,readonly --env AWS_DEFAULT_REGION=eu-west-1 --entrypoint python3 ghcr.io/starknet-innovation/qsb-solver@sha256:6b4ac63b897cd5a78223d7e14dc333b002dc50a1db75a5615b0734d2be6fbf48 /gate/source/ops/pqb-public-solve/publish_private.py /gate/artifact 905846953990.dkr.ecr.eu-west-1.amazonaws.com/qsb-pqb-solve-726c33ad eu-west-1 /results/private-image.json
' > /var/tmp/qsb-publisher-results/native-build.log 2>&1
