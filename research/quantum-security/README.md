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

A separate malformed-witness probe makes the first signed-pool `OP_ROLL` reach
an attacker-supplied cell. Lean checks that a self-chosen commitment can pass
the first HASH160 comparison, and Core confirms both local steps on truncated
test locks. This particular complete symbolic probe fails at the next index
parse, and the Core tests do not execute the complete lock. See
`evidence/selection-prefix.json`.

A later bonus-index probe reaches a locking-script HORS commitment. In a
deliberately altered, puzzle-relaxed lock, Core accepts that 20-byte value as
a bonus signature when it is DER-shaped and paired with a recovered public key.
The crafted value was not generated from a HORS secret, so this is a concrete
source-extraction edge case rather than a valid production-vault forgery. See
`evidence/bonus-overshoot.json`.

The last final-round bonus index has an exact local stack-role map when the
preceding eight selections are canonical. Lean's `QSB/Bonus.lean` checks that
indices 0–7 revisit gathered signatures, 8 selects the fixed nonce signature,
9 selects the zero CHECKMULTISIG dummy, 10–151 select unused dummy signatures,
and 152 selects a HORS commitment. It also checks that indices 0–9 move a
nonzero generated dummy into the prospective NULLDUMMY slot. Core boundary
tests on a puzzle-relaxed full lock accept sampled fresh choices 10, 11 and
151, reject sampled nonfresh choices and the natural index-152 commitment,
and accept the crafted DER-shaped index-152 commitment. These facts depend on
the canonical preceding stack region; arbitrary-witness extraction remains
open. The same adapter accepts nonminimal byte encodings of indices 10 and
152. `QSB/ByteIndex.lean` models the pinned Core source's four-byte signed
ScriptNum rule for these cases; complete compiled-Core equivalence remains
unproved. See `evidence/bonus-indices.json`.

The final key-roll suffix has a stronger arbitrary-stack result. Lean checks
that its ten fixed rolls preserve the lock-pushed signature count at the exact
position read by final CHECKMULTISIG. Thus both final count operands are 10
whenever that suffix completes. A Core-shaped matching-loop theorem then says
success with those equal counts requires every corresponding signature/key
pair to verify. These results still need byte-level source identification and
an exact Core checker refinement. See `QSB/KeyRolls.lean` and
`QSB/Multisig.lean`.

`QSB/ByteLayout.lean` is a second generated view of the same exact lock. It
retains literal push bytes for all 880 instructions; Lean checks that each of
its 15 `OP_EQUALVERIFY` instructions immediately follows `OP_HASH160`.
`QSB/ByteMachine.lean` models these byte comparisons with arbitrary hash
functions and a source-shaped ScriptNum parser. It proves that if an arbitrary
stack reaches a `HASH160; EQUALVERIFY` pair and the remaining program succeeds,
the actual opening bytes hash to the compared commitment bytes. This local
result does not identify where the commitment came from. `QSB/ByteTrace.lean`
records equality pairs and proves that erasing the record recovers the modeled
execution; the whole-lock arbitrary-witness source invariant is still open.

Read:

- [Final report](FINAL-REPORT.md)
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
python3 analysis/check_axioms.py
```

`lean-toolchain` pins Lean 4.30.0. The mathlib commit and transitive dependencies
are pinned in `lakefile.toml` and `lake-manifest.json`. No local checkout is a
dependency. The initial build prints the axiom dependencies of each reported
theorem. No project axiom, `sorry`, `admit`, or native decision oracle is used.
The generated `QSB/Layout.lean` checks an 880-instruction symbolic stack trace
from the exact Config A builder. Signature outcomes are explicit and hashes are
symbolic. Regenerate it with `analysis/generate_layout.py` after a source change
and inspect the change before citing it. The byte fixture is generated from the
same pinned builder and checked with:

```sh
python3 analysis/generate_byte_layout.py --app-root /path/to/qsb-app --check
```

Omit `--check` to regenerate `QSB/ByteLayout.lean` and
`evidence/byte-layout-map.json` after deliberately updating the pinned source.
Both generators cross-check the existing script hash in `evidence/layout-map.json`.

The probability lemmas use arbitrary measures, not rational approximations of
quantum terminal distributions. They are mathematical union bounds, with
extraction and primitive bounds supplied as explicit premises. They do not
supply the missing quantum primitive bounds or Bitcoin execution refinement.
`QSB/Reduction.lean` carries this through to the unauthorized-spend game while
retaining a separately measured extraction gap. Its source-extraction premise
requires a seven-signed, two-bonus final round from the actual attacker output;
neither that premise nor a small gap probability has been established.
The primitive failure events target owner-forbidden transaction projections;
ordinary authorized replays are outside them. They do not assume Script
acceptance, and their quantum query bounds remain open.

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
python3 analysis/check_selection_prefix.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/selection-prefix.json
python3 analysis/check_sighash_types.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/sighash-types.json
python3 analysis/check_bonus_overshoot.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/bonus-overshoot.json
python3 analysis/check_bonus_indices.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/bonus-indices.json
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
   including bonus selections, DER-shaped commitments and the final `NULLDUMMY`
   condition. The Lean without-replacement lemma covers the abstract pool
   traversal only.
2. Extend the generated opcode trace from one canonical witness to arbitrary
   Bitcoin witnesses and actual ScriptNum/encoding semantics, while keeping
   cryptographic checks explicit.
3. Connect the final enforced round and pinning checks to a precise fresh-message
   puzzle-search problem, including all accepted key encodings and FindAndDelete.
4. Prove or find a counterexample to the quantum bound for that problem. Standard
   HORS and ordinary unstructured-search bounds do not establish it by themselves.

These obligations are unresolved. The goal remains active.
