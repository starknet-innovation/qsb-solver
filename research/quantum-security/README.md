# QSB conditional security research

This is an ongoing security analysis of the pinned Config A construction, with a
Lean foundation and offline Bitcoin Core experiments. It is **not a proof that
QSB is quantum safe**. No real funds, wallet files, or private recovery state are
used by the experiments.

The first material finding is that the first digest round ends in
`OP_CHECKMULTISIG`, and its Boolean result is not enforced. Core accepted an
invalid first-round multisignature in a modified-lock experiment; equivalent
second-round and HORS-preimage mutations were rejected. The experiment relaxes
three hash-to-signature puzzle checks, explicitly, so it does not establish an
unauthorized spend of the real lock. See `evidence/round-results.json`.

Read:

- [Security game and attack table](SPECIFICATION.md)
- [Proof status and source mapping](PROOF-STATUS.md)
- [Research sources and applicability](RESEARCH.md)

## Reproduce the Lean results

Install elan, then run from this directory:

```sh
lake update
lake exe cache get
lake build
lake env lean QSB.lean
```

`lean-toolchain` pins Lean 4.30.0. The mathlib commit and transitive dependencies
are pinned in `lakefile.toml` and `lake-manifest.json`. No local checkout is a
dependency. The initial build prints the axiom dependencies of each reported
theorem. No project axiom, `sorry`, `admit`, or native decision oracle is used.
The generated `QSB/Layout.lean` checks an 880-instruction symbolic stack trace
from the exact Config A builder. Signature outcomes are explicit and hashes are
symbolic. Regenerate it with `analysis/generate_layout.py` after a source change
and inspect the change before citing it.

The probability lemmas use arbitrary measures, not rational approximations of
quantum terminal distributions. They are mathematical union bounds, with
extraction and primitive bounds supplied as explicit premises. They do not
supply the missing quantum primitive bounds or Bitcoin execution refinement.
`QSB/Reduction.lean` carries this through to the unauthorized-spend game while
retaining a separately measured extraction gap. Its source-extraction premise
requires a seven-signed, two-bonus final round from the actual attacker output;
neither that premise nor a small gap probability has been established.

## Reproduce the Core experiments

The analysis requires an explicit qsb-app source checkout and a Linux/arm64
directory containing its `qsb-consensus` executable and official Core 27.2
`libbitcoinconsensus.so.0`. Build those using qsb-app's documented
`consensus/build.mjs` if they are unavailable. Use a pinned compatible local
container image; all experiment containers run without networking, read-only,
and without capabilities. No node or funded transaction is required.

```sh
python3 analysis/source_inventory.py --app-root /path/to/qsb-app --output evidence/source-inventory.json
python3 analysis/check_round_results.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/round-results.json
python3 analysis/check_core_semantics.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/core-semantics.json
```

The recorded source inventory identifies exactly the files analyzed. The app
checkout was clean at capture. The solver baseline was
`8fe127790397b6903640f8949219c1ef34a92db2`; the app inventory and Core
experiment use `3eef7c39ecbe897ac55251841e9f2ec3764e04ad`. The app advanced
from the initially inspected `231973b0b7187416f25cc755d1c2abf5f1a954fd`
only in custody documentation; all inspected executable source-file hashes are
unchanged. The solver was not modified to alter
spending or GPU behavior. This directory adds research artifacts only.

The recorded Core library SHA-256 is
`5d7874783dc4989357600b3f273a44627d8ca6ac037f63d851572ff64a756983`.
It matched `bitcoin-27.2/lib/libbitcoinconsensus.so.0.0.0` extracted from the
official arm64 archive, whose SHA-256 is
`154c9b9e6e17136edc8f20fda5d252fb339e727e4a85ef49e7d8facb9085f2d3`.
That archive hash also matched the official HTTPS checksum list. No release
signature verification is claimed. The wrapper's hash and container identity
are recorded with the experiment.

## Immediate remaining work

1. Mechanize the actual selection-loop invariant for arbitrary witness stacks,
   including bonus selections and the final `NULLDUMMY` condition. The Lean
   without-replacement lemma covers the abstract pool traversal only.
2. Extend the generated opcode trace from one canonical witness to arbitrary
   Bitcoin witnesses and actual ScriptNum/encoding semantics, while keeping
   cryptographic checks explicit.
3. Connect the final enforced round and pinning checks to a precise fresh-message
   puzzle-search problem, including all accepted key encodings and FindAndDelete.
4. Prove or find a counterexample to the quantum bound for that problem. Standard
   HORS and ordinary unstructured-search bounds do not establish it by themselves.

These obligations are unresolved. The goal remains active.
