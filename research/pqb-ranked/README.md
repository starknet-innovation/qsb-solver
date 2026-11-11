# pqb-ranked: PQB's grinder with deterministic ranges

`grind.cu` is an adaptation of `grinder/grind.cu` from
[fireblocks-labs/pqb](https://github.com/fireblocks-labs/pqb) at
`eccdd09772edf14ab37fc63992b0626ad7ff2221` (MIT, Copyright (c) 2026 Fireblocks Ltd.). The
unchanged upstream files, licence and notices are under [vendor/pqb](../../vendor/pqb); this
build includes `common.cuh` and `ptx_field.cuh` from there. `source-lock.json` binds the bytes.
It is **not** the upstream grinder and upstream's measurements do not describe it.

- `tests/reference.py`: a slow, independent enumeration (plain integers and hashlib) used to
  compare complete hit sets. Development only; not a verifier and not in any image.
- `tests/fixtures/`: public problems and pqb work packets of a synthetic vault whose seed is
  published in `tools/make_fixture.py`. Never fund it.
- `tools/make_fixture.py`, `tools/pqb_crosscheck.py`, `tools/cost_model.py`: need a pqb checkout
  (`PQB_ROOT`) and its dependencies; they are not run by CI.

Status and evidence: [docs/pqb/ASSESSMENT.md](../../docs/pqb/ASSESSMENT.md).
