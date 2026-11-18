# grinder: the CUDA puzzle grinder

The GPU search that `pqb cloud grind` runs on each rented NVIDIA box:

| file | what |
|---|---|
| `grind.cu` | the kernels and the host loop: pin and round tracks of a PQB spend |
| `common.cuh` | secp256k1 field arithmetic and an unrolled SHA-256 compression (generated) |
| `ptx_field.cuh` | `fe_mul` / `fe_sqr` as PTX carry chains (generated) |
| `bin/grind-cuda12.6-<digest>.gz` | the same sources built once, for every card pqb rents |
| `metal/` | the same grinder for an Apple-silicon Mac's GPU (Metal): `pqb grind local` |

The source digest (`pqb.grinderbin.source_digest`) covers every `*.cu` / `*.cuh` file in this
directory, so keep nothing else with those extensions here. `metal/` is not part of it.

## The Metal grinder

`metal/` is a port of `grind.cu` for Apple silicon: the same problem files, flags (`--queue`,
`--done`, `--candidate-dir`), stdout records and hits format, and the same search, z-block for
z-block (`kernels.metal`; the field, inversion and SHA-256 code `common.cuh` was generated from).
Its EC is laid out for the M1 rather than ported kernel for kernel: W = z*B as a tree of batched
affine additions, the menu and the hashing in kernels of their own, and one inversion shared by
16 threads. SHA-256 blocks whose message is fixed run over message schedules computed once on the
host: a round's tail blocks, and the 256 possible second blocks of an uncompressed or hybrid key. `grind.mm` is grind.cu's host loop on Metal: one command buffer per batch, two in
flight, the kernels compiled when it starts with the problem's shape as macros. It needs only the
Xcode command-line tools (`make -C metal`); pqb builds it into `~/.cache/pqb/grinder/` by itself.
`grind --bench S --problem P.json [...]` prints steady-state trials/s per problem, and
`pqb grind local --bench` runs it on all three stage kinds. `QG_PROFILE=1` adds each kernel's GPU
time per z-block (`@profile` lines), `QG_STAGE=k` runs only the first k stages of each batch.

## The binary pqb uploads

Boxes do not compile anything. `pqb cloud` uploads one fat binary (sm_75/80/86/89/90 cubins plus
compute_89 PTX; static cudart, libstdc++ and libgcc, so it needs only glibc 2.35+ and the driver)
and rents the ~90 MB `nvidia/cuda:12.6.3-base-ubuntu22.04` image instead of the 4 GB `-devel` one.
Each box checks the binary's sha256 and runs the known-answer self-test before it gets work. Where
the binary comes from, in order (`pqb/src/pqb/grinderbin.py`):

1. `bin/` here, when its sha256 matches the one pinned in `grinderbin.PREBUILT` for these exact
   sources;
2. `~/.cache/pqb/grinder/` (`$PQB_GRINDER_CACHE`), from an earlier build;
3. otherwise the fleet rents the `-devel` image, the first box builds and self-tests it, and its
   binary comes back to the cache and goes to every other box;
4. if that build fails, each box builds its own, as all of them used to.

Until 2026-11-14 every box built it: 60-100 s of billed time per box, and nvcc's `--threads 0`
race failed one build in three (22 of 98 boxes in that day's mainnet run).

### Rebuilding it

The build is reproducible: the same sources, recipe and image give the same bytes.

```console
$ cd pqb && make grinder-bin       # Docker, linux/amd64 (emulated on an ARM Mac, ~2.5 min)
```

runs `nvcc` (`grinderbin.nvcc_command`) in `nvidia/cuda:12.6.3-devel-ubuntu22.04` with no network,
writes `bin/grind-cuda12.6-<digest>.gz`, caches the binary and prints the `PREBUILT` entry to pin.
After any change to `grind.cu`, rebuild and pin, or the fleet falls back to building on its first
box. To check the shipped file, rebuild and compare: the printed sha256 must equal the pinned one.
Docker is only needed for this; `pqb` never requires it.

## How pqb finds it

In a checkout of this repository, `pqb` finds `../grinder` relative to its own package. Elsewhere
(for example after a non-editable `pip install`), point it here:

```console
$ export PQB_CUDA_GRINDER=/path/to/pqb/grinder     # or: pqb cloud grind --grinder DIR
```

## Build and run by hand

On a box with CUDA 12.x, the line `make grinder-bin` runs (`grinderbin.nvcc_command`). Not
`-arch=native`: without a GPU it knows, nvcc falls back to sm_52 + PTX. No `--threads`: its
parallel per-architecture compile races on its own temp files. With CUDA 12.8+ pqb adds sm_120
(Blackwell).

```console
$ nvcc -O3 -std=c++17 -gencode arch=compute_75,code=sm_75 \
    -gencode arch=compute_80,code=sm_80 -gencode arch=compute_86,code=sm_86 \
    -gencode arch=compute_89,code=sm_89 -gencode arch=compute_90,code=sm_90 \
    -gencode arch=compute_89,code=compute_89 \
    -Xcompiler -static-libgcc -Xcompiler -static-libstdc++ -o grind grind.cu
$ ./grind --problem P.json --hits hits.txt --seconds S --candidate-dir DIR
```

It reads the line-format `P.txt` beside `P.json` (pqb writes both). `--candidate-dir` is
accepted and ignored by this build; pqb passes it because other grinder builds take it.

### Round stages: `--queue` and `--done`

```console
$ ./grind --problem P.json --hits hits.txt --seconds S --queue Q.txt --done D.txt
```

A round searches the t-subsets of its n live slots. With `--queue` the grinder searches exactly
the ranges listed in `Q.txt`, each subset once, instead of drawing random subsets with
replacement. The work unit is a *prefix*: a (t-1)-subset of the first n-1 slots, numbered by
lexicographic rank (`pqb.grind.unrank_subset(rank, n - 1, t - 1)`), which covers its completions
by every later slot. Prefix ranks therefore partition the round, and prefix ranks `[lo, hi)` are
the contiguous subset ranks (the nonces in hit lines) from the first subset of `lo` to the
first of `hi`. It prints `@space {"prefixes": N}` with N = C(n-1, t-1).

- `Q.txt` holds `lo hi` lines (prefix ranks, half-open). The controller appends to it while the
  grinder runs; only complete lines are read, and an empty queue is polled every 250 ms until
  `--seconds` runs out.
- Each batch is consecutive prefixes from one queued range; its `@batch` line carries `"lo"` and
  `"hi"`, and the same `lo hi` is appended to `D.txt`. Both come after the batch's hits are
  written and flushed, so a range reported done never lost its hits to a crash.
- On start the grinder subtracts every range in `D.txt` from the queue, so a restart does not
  redo work.
- A batch whose hits did not all reach the hits file (the hit buffer overflowed, or a write or
  flush failed) gets an `@lost` line instead of `@batch`, and no `D.txt` record: it is never
  credited, and pqb retires the box. `-DQG_HIT_CAP=k` shrinks the buffer to test this.

Without `--queue` (and always in the pinning stage, whose ~2^61 space is never exhausted) the
search draws at random. `pqb cloud` uses the queue for rounds: see `fleet.RoundLedger`.

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
dollar. The pinning search is memoryless: any number of cards can work on it with no
coordination. A round is shared out by `pqb cloud` as ranges of its space, so every subset is
searched once and an empty round is known to be empty when the last range is done; an interrupted
card's unfinished ranges go to the others. Section 6 and Appendices B and C of the
[whitepaper](../whitepaper/PQB.pdf) give the cost model and the GPU table.

This is research code: see [SECURITY.md](../SECURITY.md).
