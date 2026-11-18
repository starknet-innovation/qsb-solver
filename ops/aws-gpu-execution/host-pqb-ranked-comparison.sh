#!/bin/bash
# Run after successful three-stage qualification on the same host and fixed deadline.
set -euo pipefail
cd /opt/qsb-pqb-final
deadline=$(cat /var/tmp/qsb-pqb-final-results/deadline.txt)
[[ "$deadline" =~ ^[0-9]{10}$ ]]
test "$(cat /var/tmp/qsb-pqb-final-results/exit-code.txt)" = 0
test -f /run/qsb-shutdown-armed
systemctl is-active --quiet qsb-benchmark-expire.timer
sha256sum -c SHA256SUMS --quiet
remaining=$((deadline - $(date -u +%s) - 90))
test "$remaining" -ge 180
results=/var/tmp/qsb-pqb-ranked-timings
mkdir "$results"
timeout --signal=TERM --kill-after=5s "$remaining" docker run --rm --name qsb-pqb-compare \
  --gpus all --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
  --tmpfs /tmp:rw,nosuid,nodev,size=256m --env PYTHONDONTWRITEBYTECODE=1 --env PYTHONPATH=/gate \
  --mount type=bind,src=/opt/qsb-pqb-final/gate,dst=/gate,readonly \
  --mount type=bind,src=/opt/qsb-pqb-final/comparison,dst=/comparison,readonly \
  --mount "type=bind,src=$results,dst=/results" \
  --entrypoint python3 qsb-pqb:final /comparison/compare_ranked.py /gate /comparison/baseline-grind /results/samples "$deadline"
