# PQB candidate worker (HOLD)

A separate worker for [PQB](https://github.com/fireblocks-labs/pqb) vaults. PQB is a different
lock construction from QSB with different puzzles, so this is not a new version of the `ranked-v2`
worker and shares no binary with it. Status, evidence and limits:
[docs/pqb/ASSESSMENT.md](../../docs/pqb/ASSESSMENT.md).

It solves one unit of one stage per request (`pinning`, `round0`, `round1`) under the
[`pqb-ranked-v2`](../../contracts/pqb-ranked-v2.json) range contract, on a compiled copy of
[research/pqb-ranked/grind.cu](../../research/pqb-ranked/grind.cu): PQB's CUDA grinder at
`eccdd09`, adapted to walk a stated range exhaustively instead of drawing at random.

```sh
python3 -m unittest tests.test_pqb_contract tests.test_pqb_handler tests.test_pqb_ranked_emulation -v
docker build --platform linux/amd64 -f worker/pqb/Dockerfile --target aws \
  --build-arg CUDA_ARCH=86 --build-arg SOLVER_COMMIT="$(git rev-parse HEAD)" -t qsb-pqb:local .
python3 worker/pqb/test_image.py qsb-pqb:local
```

The unit tests need a C++ compiler, not a GPU: they build the grinder as plain C++ (`-DQG_EMU`).
The image build needs a native x86_64 Linux host (see `worker/optimized/README.md`).

The [full-unit validation harness](../../docs/pqb/FULL-UNIT.md) uses the bound handler
and current CI binary on public synthetic problems. Its optional local evidence-directory
argument retains native logs/hits, including failed work, and cannot be enabled by a request.
The [three largest units passed natively](../../docs/pqb/2026-11-11-full-unit-validation.md).
The harness is outside the image; this grants no release or deployment status.

A separate [supplemental assessment](../../docs/pqb/2026-11-11-correctness-consumer-validation.md)
passed all 13 native correctness cases, checked the pinned qsb-app consumer and scanned the
actual PQB CI image. The repeatable CPU compatibility command is
`python3 scripts/check_pqb_consumer.py APP_CHECKOUT APP_COMMIT NEW_EXTERNAL_OUTPUT_DIR`;
install the consumer's locked dependencies first and keep both checkouts clean.

The image also exposes `/opt/qsb` as an alias of `/opt/qsb-pqb`, matching the consumer's
shared hardened Batch command. Offline CI executes that path under `setpriv`; the
[completed public solve](../../docs/pqb/2026-11-11-public-transport-solve.md) verified all three
stages through real private Batch/S3 transport with the pinned consumer and upstream native
libsecp256k1 checker. Its [development harness](../../ops/pqb-public-solve/README.md) remains
separate from an enrolled release or the served application coordinator.
The [final image assessment](../../docs/pqb/2026-11-12-final-image-qualification.md) binds the
parser-fixed artifact to verified signed build provenance, three fresh largest native units,
13 correctness cases before each unit and the pinned consumer replay. Its HOLD descriptor and
publication/adoption handoff are ready for review. The image remains unpublished and unenrolled.

## Request and result

```json
{"input": {"protocol": "pqb-v1", "searchVersion": "pqb-ranked-v2", "stage": "round0", "attempt": 3,
           "problemBase64": "...", "problemSha256": "...", "manifestHash": "...", "kernelCommit": "..."}}
```

`problemBase64` is pqb's line-format problem (`pqb grind gpu-problem` writes it as `P.txt`): the
legacy-sighash preimage, the menu as curve points, `B = -r⁻¹G`, and for a round the table slot
offsets. Everything in it is public. The handler refuses unknown request fields and unknown
problem lines, a problem whose shape is not the stage's, and any gate other than the 24-bit
`30 1D 02`. It cannot tell whether a well-formed problem describes the caller's transaction: the
caller must check that itself, as `pqb.gpu.check_problem` does.

The result has the `ranked-v2` fields plus `trials` and `gateHits`. `candidates` are grinder hit
lines (`seq lt j recid enc level` for pinning, `i0,..,it j recid enc level` for a round, table
positions counted among the live slots) whose digest passes the gate **and** has the shape of a
32-byte DER signature. That shape is a necessary condition only. The consumer re-derives every
candidate and applies the full check: strict DER, the `SIGHASH_SINGLE` filter, key recovery for a
verify-form stage, and its policy on hybrid-encoded keys. `gateHits` should be near
`trials / 2^24`; a worker that silently skipped trials would report too few.

A unit is credited (`range-complete`) only when the grinder exits 0 and its own completion line
names exactly that unit with the z-block count the contract gives it. A repeated candidate line, a hit-buffer overflow, more
than 32 candidates, a timeout (840 s) or any other exit is `failed` or `interrupted`, never a
partial credit. Deterministic failures must not be blindly retried.

## What differs from upstream

Listed at the top of `grind.cu` and in `research/pqb-ranked/source-lock.json`. In short: ranked
flags, host-listed round prefixes, fail-closed completion accounting, the DER-shape filter with a
gate-hit counter, detection of exceptional curve cases with an exact host recomputation, strict
option parsing. The SHA-256 and secp256k1 arithmetic (`common.cuh`,
`ptx_field.cuh`, and the group formulas in `grind.cu`) are upstream's.
