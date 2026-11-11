# Native A10G measurement of the ranked PQB grinder, 11 November 2026

Status: **executed and passed.** A component measurement on public synthetic fixtures. It is
not a full solve, a whole-spend time, range credit, or a bill.

## What ran

- **Source:** `266f4a0d…` (PR 18 head at the time). Binaries from CI run 43019767928, target
  `measure` of `worker/pqb/Dockerfile`, nvcc 12.8.93, `-O3 -std=c++17 -arch=sm_86`:
  ranked `3f816a00d5e314315aca33e4f2ec2647462bd6243e09ff257ec7b20c445a7594`, upstream's
  unmodified grinder `0a5de7e0faca7dfdf27b788bc6a4c33f42c77d0015a6c8edd69fb3fdffb0da74`. CI
  checked that the ranked binary is the one in the worker image. They are CI artifacts, not
  attested release binaries; three CI runs produced byte-identical files.
- **Host:** one on-demand `g5.xlarge` (NVIDIA A10G, driver 595.91.07) in eu-west-1b, launched by
  `ops/aws-gpu-execution/control.py` with its fixed 25-minute deadline and independent cleanup.
- **Execution:** `host-pqb-measure.sh`, one shot, no network, read-only root, dropped
  capabilities. The published combined image served only as a CUDA runtime.
- **Runner:** `research/pqb-ranked/measure/run_measure.py`, 194 s in total.

## Correctness: 11 of 11

Each case is a small ranked range whose complete hit set was computed beforehand by the
independent reference. On the GPU every case returned exactly that set, the exact z-block count,
the exact gate-hit count and `complete`.

| Case | z-blocks | Hits | Note |
|---|---|---|---|
| pin-first, pin-last | 3,000 / 1,500 | 48 / 31 | both ends of the usable nonce space |
| pin-batches | 2,700 | 44 | many batches, two in flight |
| pin-der-filter | 64 | 0 shaped | gate count exact at a 1-bit gate |
| pin-planted-exceptional | 48 | 415 | a menu point equal to a sighash point: the device reported the one thread (4 z-blocks) and the host recomputed it |
| round0-first, -last, -interior-batches | 975 / 431 / 313 | 43 / 18 / 10 | |
| round1-first, -last, -interior-batches | 885 / 402 / 1,387 | 16 / 5 / 16 | |

This is the first native evidence for the ranked walk, the DER-shape filter and the
exceptional-case path. It covers these ranges on this GPU and compiler. It does not cover every
range, and the branch where the sighash point itself is infinity still has no test of its own.

## Timing: ranked walk against upstream's random search

Three samples per mode per stage, alternating on the same GPU, about ten seconds each, at the
production 24-bit gate. Steady state excludes the first three batches of each process. Every
sample's gate-hit count was consistent with its trial count, and every ranked sample reported
its range complete.

| Stage | Upstream random, steady (G trials/s) | Ranked, steady (G trials/s) | Ranked / upstream |
|---|---|---|---|
| pin | 2.439 – 2.458, median 2.453 | 2.480 – 2.488, median 2.487 | 1.014 |
| round 0 | 2.694 – 2.697, median 2.694 | 2.727 – 2.729, median 2.729 | 1.013 |
| round 1 | 2.004 – 2.008, median 2.005 | 2.012 – 2.015, median 2.014 | 1.004 |

- **The ranked walk is not slower.** The cost model's assumption that an exhaustive sweep runs
  at upstream's trial rate holds on this card, for these samples. The added exceptional-case
  checks and host-listed prefixes show no measurable cost.
- **Start-up.** Whole-process rates are lower: upstream 2.39–2.41 / 2.63–2.64 / 1.95–1.96, ranked
  pin 2.43–2.44. A ranked round sample here is six processes of about two seconds each, so its
  whole-process figures (2.33–2.35 and 1.67–1.70) mostly show process start-up, about one second
  on this host. Production units run for minutes.
- **Against an RTX 4090.** pqb's published 4090 rates are 5.93 / 6.37 / 4.70 G trials/s, so the
  A10G ran at 0.42 / 0.43 / 0.43 of them. That is one A10G host against one 4090 host measured
  by other people with another compiler version, not a matched comparison.

## What it means for cost (model with measured rates)

pqb's cost model with these A10G rates gives **19.6 A10G-hours per spend with exhaustive sweeps**
and 28.8 with random draws and upstream's cut-offs. At the on-demand prices read on the day
that is about $22 in eu-west-1 ($1.123/h) or $25 in eu-west-2 ($1.277/h), against about $32 and
$37 for random draws. The expected hours are still a model; only the rates are measured.

Unit durations at these rates: a pinning unit about 9.3 minutes, a round-0 unit 17 minutes on
average and up to 21, a round-1 unit up to 8. Round-0 units are too long for qsb-app's current
900-second Batch timeout, so the provisional round-0 unit size has to shrink before a contract
freeze.

## Limits

- One host, one session, three samples per mode. No second host, no other card.
- A ranked round sample is six equal prefix ranges spread over the prefix space; prefixes inside
  a range are consecutive. It approximates upstream's uniform draw.
- Component timing. Job start-up, interrupted units, units overtaken by another's solution and
  storage are not in the cost figure.

## Launch attempts, cost and cleanup

Seven launches were refused by EC2 with `InsufficientInstanceCapacity` before this one: eu-west-1c,
1a, 1b (12:03–12:07 UTC), eu-west-2a, 2b (12:17–12:18), then eu-west-1c and 1a again
(13:23–13:25). None allocated an instance and none was retried within its session. The eighth,
eu-west-1b at 13:26:31 UTC, launched; the driver requested termination at 13:33:15.

Estimated compute: about **$0.13** (6.7 minutes at $1.123/h), plus negligible storage. This is an
estimate, not provider billing. The user's cap was $5.

Cleanup is verified: at 13:40:51 UTC an independent check found no instance, volume, security
group, schedule, function, role, instance profile or staging bucket of the session, and nothing
running in eu-west-1 or eu-west-2. One irregularity: the job orchestrating the retry pass was
stopped from the operator session after the instance had terminated and before the controller's
cleanup. The committed controller was then run; it removed the schedule, function and instance
profile and failed on a network timeout, and the session's three roles and security group were
deleted by name. Earlier sessions' cleanups were verified by the unmodified postcheck.

## Evidence

[evidence/a10g-measure-2026-11-11](evidence/a10g-measure-2026-11-11): `result.json` (every
sample and case), `gate.log`, `gpu.txt`, `exit-code.txt`, `deadline.txt`, and `manifest.json`
with their hashes, the bundle identity and the attempt list. Private operational receipts stay
outside Git.
