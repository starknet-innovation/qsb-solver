#!/bin/bash
# Staging and SHA256SUMS are prepared and checked before this one-shot gate.
set -euo pipefail
stage=$1
image=$2
deadline=$3
receipt_sha=$4
[[ "$image" =~ ^ghcr.io/starknet-innovation/qsb-solver@sha256:[0-9a-f]{64}$ ]]
[[ "$deadline" =~ ^[0-9]{10}$ && "$receipt_sha" =~ ^[0-9a-f]{64}$ ]]
case "$stage" in
  ranges) runner=run_ranges.py ;;
  trace) runner=run_trace.py ;;
  timing) runner=run_pair.py ;;
  *) exit 2 ;;
esac
[ -f /run/qsb-shutdown-armed ]
systemctl is-active --quiet qsb-benchmark-expire.timer
cd /opt/qsb-a10g-gate
sha256sum -c SHA256SUMS
mkdir /var/tmp/qsb-a10g-results
results=/var/tmp/qsb-a10g-results
printf '%s\n' "$deadline" > "$results/deadline.txt"
# No compute can begin before the pinned image is present and time is rechecked.
# After the pull: the 720 s gate, 60 s to package, collection of the largest permitted result
# (600,000 encoded bytes is 34 chunks, budgeted at 8 s each) and the collector's 120 s reserve.
# Before it: that plus the 300 s pull.
[ "$((deadline-$(date -u +%s)))" -ge 1500 ]
timeout --signal=TERM --kill-after=10s 300 docker pull "$image" > "$results/pull.log" 2>&1
[ "$((deadline-$(date -u +%s)))" -ge 1200 ]
nvidia-smi --query-gpu=name,uuid,driver_version --format=csv,noheader > "$results/gpu.txt"
trap 'docker rm -f qsb-full-gate >/dev/null 2>&1 || true' EXIT
args=(/gate/bundle /results/result.json)
if [ "$stage" = trace ]; then args+=("$receipt_sha"); fi
if [ "$stage" = timing ]; then args+=("e7975d3061ccd7246c0d4548eeab201710a93959b63a2fcbd3a602e9790b99b9"); fi
set +e
timeout --signal=TERM --kill-after=10s 720 docker run --name qsb-full-gate --rm --gpus all \
 --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
 --tmpfs /tmp:rw,exec,nosuid,nodev,size=512m \
 --mount type=bind,src=/opt/qsb-a10g-gate,dst=/gate,readonly \
 --mount type=bind,src="$results",dst=/results \
 --entrypoint python3 "$image" "/gate/tools/$runner" "${args[@]}" > "$results/gate.log" 2>&1
status=$?
set -e
docker rm -f qsb-full-gate >/dev/null 2>&1 || true
printf '%s\n' "$status" > "$results/exit-code.txt"
python3 - "$results" <<'PY'
import base64,gzip,hashlib,json,os,pathlib,stat,sys
root=pathlib.Path(sys.argv[1]);files={}
# The container could write here. Never follow a link out of the results directory: accept
# regular files only, and open them without following symlinks.
for p in sorted(root.iterdir()):
    if not stat.S_ISREG(os.lstat(p).st_mode):raise ValueError('non-regular result entry: '+p.name)
    fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
    with os.fdopen(fd,'rb') as f:
        if not stat.S_ISREG(os.fstat(f.fileno()).st_mode):raise ValueError('non-regular result entry: '+p.name)
        files[p.name]=f.read(8000001).decode()
raw=json.dumps(files).encode()
if len(raw)>8000000:raise ValueError('result too large')
data=base64.b64encode(gzip.compress(raw))
# Bounded so collection fits the time reserved above.
if len(data)>600000:raise ValueError('encoded result too large')
with (root/'public-result.b64').open('xb') as f:f.write(data)
print('QSB_PUBLIC_RESULT_META='+json.dumps({'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}))
PY
exit "$status"
