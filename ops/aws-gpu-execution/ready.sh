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
