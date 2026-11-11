# Native measurement run

**Executed on 11 November 2026 on one A10G and passed:** see
[the record](../../../docs/pqb/2026-11-11-a10g-measurement.md). The rest of this page describes
how the run is built and what it can show.

For the completed full-unit gate see [the plan and results](../../../docs/pqb/FULL-UNIT.md). `run_full_unit.py`
executes one production unit through the bound worker, retains native logs and checks emitted
candidates independently. It does not repeat this short matched-throughput experiment.

Nothing in this directory authorizes a launch: each one needs the user's explicit go-ahead on
account, region, instance type and a budget cap, under `ops/aws-gpu-execution`.

## Correctness-only profile

Use `run_measure.py BUNDLE RESULT.json --correctness-only` to execute the complete committed
correctness suite without repeating timing. The result uses `qsb-pqb-correctness-result-v1`,
records `mode: correctness-only` and `timing: null`, and cannot be used as performance evidence.
Empty suites, incorrect hits/reports and failed invocations fail this profile as well.

The host wrapper accepts an explicit fifth argument `correctness`. It retains the fixed host
deadline but uses a 120-second runner budget, 180-second outer container bound and 240-second
minimum remaining time after image setup. Omitting it retains the original full measurement
profile and its 780-second remaining-time guard. Neither profile extends an active deadline.
All exits after the one-shot marker, including image-pull/time/device-query setup failures,
write `exit-code.txt` and the hash-described `public-result.b64`. Setup diagnostics and attempted
container cleanup are retained. Simulated host tests cover these failure paths without AWS.

## Questions

1. Does the compiled ranked grinder produce exactly the expected hits on a real GPU? Until now
   that was shown only under CPU emulation before the recorded native run.
2. Is the ranked walk as fast per trial as upstream's random search? The modelled saving
   (12.1 → 8.3 RTX 4090-hours per spend) assumes it is.
3. What is the absolute rate on the card? This replaces the assumed A10G speed in the
   assessment's AWS cost table.

## Pieces

| File | Role |
|---|---|
| `make_expected.py`, `expected.json` | 13 small ranked ranges and their complete hit sets, computed by the independent reference. Includes multi-batch ranges, the DER-shape filter both counting and emitting candidates, and a planted exceptional point (`fixtures/pin-planted.txt`). The 11 November run had the first 11; the two filtered cases that must emit a candidate were added afterwards and have not run on a GPU. |
| `run_measure.py` | The one-shot runner: correctness first, then interleaved upstream/ranked timing per stage. Timing is skipped if any correctness case fails. A failed grinder invocation's problem, arguments and whole output are kept under `failed-invocations/` beside the result and collected with it. |
| `worker/pqb/Dockerfile`, target `measure` | Compiles upstream's unmodified grinder with the ranked grinder's compiler and flags. CI uploads both as `pqb-measure-binaries-sm86` and checks the ranked one is the worker image's binary. |
| `scripts/prepare_pqb_measure_bundle.py` | Builds the hash-verified bundle from that artifact and a clean checkout at the same commit. |
| `ops/aws-gpu-execution/host-pqb-measure.sh` | Runs the bundle on an already-authorized host: no network, read-only root, dropped capabilities. The published combined image is used only as a CUDA runtime. |
| `tests/test_pqb_measure.py` | Dry-runs the bundle and runner on emulated binaries, including a wrong answer and the one-shot marker. |

## What a result will and will not show

- A run passes only if every correctness case matches and every timing sample reached steady
  state; a stage without one is listed in `stagesWithoutSteadyState` and fails the run. The
  emulated dry run turns that requirement off explicitly, and the result records the setting.
- A grinder process must print one `@range` and one `@done` line; a duplicate fails it.

- Rates are z-blocks per second in steady state and, separately, per whole process with
  start-up. Three samples per mode per stage, alternating, about ten seconds each.
- A ranked round sample is six equal prefix ranges spread evenly over the prefix space, since
  the work per z-block depends on where a prefix sits and upstream draws prefixes uniformly.
  Prefixes inside one range are still consecutive: an approximation of a uniform draw.
- The binaries are CI build artifacts, not attested release binaries.
- It is a component measurement on public synthetic fixtures. It grants no range credit and is
  not a full solve, a whole-spend time, or a bill.

## Attempts

11 November 2026, authorized by the user, one `g5.xlarge` each, $5 cap in total. EC2 refused
seven launches with `InsufficientInstanceCapacity` (eu-west-1c, 1a, 1b, eu-west-2a, 2b, then
eu-west-1c and 1a again); none allocated an instance. The eighth, eu-west-1b at 13:26 UTC,
launched and the run completed. Details, cost and cleanup are in the record.

## Remaining hardware scope

- The controller launches one `g5.xlarge`, in Ireland or London. Measuring an L40S
  (`g6e.xlarge`) needs a further controller change; eu-west-1 does not offer `g6` or `g6e`.
- Staging and collection use the committed controller's external AWS MCP handoff. The later
  [13-case correctness-only campaign](../../../docs/pqb/2026-11-11-correctness-consumer-validation.md)
  retained and hash-verified its archive, then independently verified complete cleanup. It
  collected no timing samples and does not replace the original matched measurement.
