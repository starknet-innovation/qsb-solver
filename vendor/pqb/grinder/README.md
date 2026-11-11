# grinder: the CUDA puzzle grinder

The GPU search that `pqb cloud grind` uploads to each rented NVIDIA box and builds there:

| file | what |
|---|---|
| `grind.cu` | the kernels and the host loop: pin and round tracks of a PQB spend |
| `common.cuh` | secp256k1 field arithmetic and an unrolled SHA-256 compression (generated) |
| `ptx_field.cuh` | `fe_mul` / `fe_sqr` as PTX carry chains (generated) |

pqb uploads every `*.cu` / `*.cuh` file in this directory (`fleet.grinder_sources()`), so keep
nothing else with those extensions here.

## How pqb finds it

In a checkout of this repository, `pqb` finds `../grinder` relative to its own package. Elsewhere
(for example after `pip install` from a wheel), point it here:

```console
$ export PQB_CUDA_GRINDER=/path/to/pqb/grinder     # or: pqb cloud grind --grinder DIR
```

## Build and run by hand

On a box with CUDA 12.x (pqb's default image is `nvidia/cuda:12.6.3-devel-ubuntu22.04`):

```console
$ nvcc -O3 -std=c++17 -arch=native -o grind grind.cu
$ ./grind --problem P.json --hits hits.txt --seconds S --candidate-dir DIR
```

It reads the line-format `P.txt` beside `P.json` (pqb writes both). `--candidate-dir` is
accepted and ignored by this build; pqb passes it because other grinder builds take it.

A *problem* (`P.json`) holds no secret: only the legacy-sighash preimage, the menu as curve
points and the digest prefix to report. pqb writes it with `pqb grind gpu-problem`, and
re-derives every reported hit on your own machine (`gpu.HitChecker`) before it trusts a box.
The ECDSA co-signature of PQB's hybrid signature is not part of the search: pqb signs it on your
machine after the grind, and the co-signing key never reaches a box.

`-DQG_EMU` builds the same file as plain C++ that runs every kernel on the CPU, which is how the
kernels were validated against the Python reference without an NVIDIA GPU.

## Measured rates

Steady-state trials per second, one card, measured on vast.ai on 2026-09-26 (the RTX 4090 row is
pqb's reference rate, `fleet.REFERENCE_RATE`; `pqb/src/pqb/gpus.py` has the full table
from the 2026-09-27 sweep):

| card | pin | round 0 | round 1 |
|---|---|---|---|
| RTX 4090 | 5.93 G | 6.37 G | 4.70 G |
| RTX 5090 | 7.39 G | 8.25 G | 5.62 G |
| H100 SXM | 3.33 G | 3.85 G | 2.53 G |

The workload is bound by 32-bit integer throughput, so consumer cards beat datacenter cards per
dollar. The search is memoryless: any number of cards can work on a stage with no coordination,
and an interrupted card loses only its start-up time. Section 6 and Appendices B and C of the
[whitepaper](../whitepaper/PQB.pdf) give the cost model and the GPU table.

This is research code: see [SECURITY.md](../SECURITY.md).
