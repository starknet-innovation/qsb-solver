# Native measurement run (prepared, not executed)

Everything here is preparation. No instance has been launched for it, and nothing in this
directory authorizes one: a launch needs the user's explicit go-ahead on account, region,
instance type and a budget cap, under `ops/aws-gpu-execution`.

## Questions

1. Does the compiled ranked grinder produce exactly the expected hits on a real GPU? Until now
   that is shown only under CPU emulation.
2. Is the ranked walk as fast per trial as upstream's random search? The modelled saving
   (12.1 → 8.3 RTX 4090-hours per spend) assumes it is.
3. What is the absolute rate on the card? This replaces the assumed A10G speed in the
   assessment's AWS cost table.

## Pieces

| File | Role |
|---|---|
| `make_expected.py`, `expected.json` | 11 small ranked ranges and their complete hit sets, computed by the independent reference. Includes multi-batch ranges, the DER-shape filter, and a planted exceptional point (`fixtures/pin-planted.txt`). |
| `run_measure.py` | The one-shot runner: correctness first, then interleaved upstream/ranked timing per stage. Timing is skipped if any correctness case fails. |
| `worker/pqb/Dockerfile`, target `measure` | Compiles upstream's unmodified grinder with the ranked grinder's compiler and flags. CI uploads both as `pqb-measure-binaries-sm86` and checks the ranked one is the worker image's binary. |
| `scripts/prepare_pqb_measure_bundle.py` | Builds the hash-verified bundle from that artifact and a clean checkout at the same commit. |
| `ops/aws-gpu-execution/host-pqb-measure.sh` | Runs the bundle on an already-authorized host: no network, read-only root, dropped capabilities. The published combined image is used only as a CUDA runtime. |
| `tests/test_pqb_measure.py` | Dry-runs the bundle and runner on emulated binaries, including a wrong answer and the one-shot marker. |

## What a result will and will not show

- Rates are z-blocks per second in steady state and, separately, per whole process with
  start-up. Three samples per mode per stage, alternating, about ten seconds each.
- A ranked round sample is six equal prefix ranges spread evenly over the prefix space, since
  the work per z-block depends on where a prefix sits and upstream draws prefixes uniformly.
  Prefixes inside one range are still consecutive: an approximation of a uniform draw.
- The binaries are CI build artifacts, not attested release binaries.
- It is a component measurement on public synthetic fixtures. It grants no range credit and is
  not a full solve, a whole-spend time, or a bill.

## Attempts so far

11 November 2026, authorized by the user, one `g5.xlarge` each, $5 cap in total. EC2 refused all
five launches with `InsufficientInstanceCapacity`:

| Zone | Launch (UTC) |
|---|---|
| eu-west-1c | 12:03 |
| eu-west-1a | 12:05 |
| eu-west-1b | 12:07 |
| eu-west-2a | 12:17 |
| eu-west-2b | 12:18 |

No instance was allocated, no measurement ran and no GPU time was billed. Each session's
temporary resources and staging bucket were removed and independently verified. Nothing was
retried within a session. Receipts are kept outside Git. The user asked for a later retry.

## Not prepared

- The controller launches one `g5.xlarge`, in Ireland or London. Measuring an L40S
  (`g6e.xlarge`) needs a further controller change; eu-west-1 does not offer `g6` or `g6e`.
- Staging the bundle and collecting `public-result.b64` follow the September procedure; no new
  operator tooling was written.
