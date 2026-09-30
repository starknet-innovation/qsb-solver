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
the first HASH160 comparison. `QSB/FirstOvershoot.lean` proves a stronger
byte-level result for the full generated program and this top-stack family:
with any parsed first-index value at least 152, including nonminimal encodings
accepted by the model, arbitrary pinning-key bytes, and any lower stack, the
program rejects. An empty continuation fails at the first external-cell roll.
Fewer than eight cells after an external marker fail at the opening roll. Otherwise a
mismatched marker fails the first hash comparison; a matching one reaches a
20-byte lock commitment at the next fixed roll and fails the following numeric
parse. Large stacks fail the modeled 1000-cell limit even earlier. The byte
model also rejects unparsable first indices at the first `OP_MIN`. A successful
run with this top-stack layout therefore has a parsed first-index value below
152. The byte model grants both pinning checks true and leaves later
signature outcomes arbitrary. Pinned Core tests accept truncated locks
immediately before that `OP_MIN` and reject when it is added for canonical
152, nonminimal `980000`, and four-byte `ffffff7f`. The initial-stack
shape is explicit; the Core tests do not execute the complete lock. See
`evidence/selection-prefix.json`.
`QSB/FirstIndexMap.lean` checks the complementary lock-owned lookup window:
the 150 cells at depths 152–301 are 20-byte commitments, and every shallower
lock cell has another length. For a first signed roll at depth `153 + i`,
`0 ≤ i < 150`, the selected cell comes from that fixed commitment window,
independent of the lower witness stack. The parser-to-roll-index link is
proved below within the byte model; later selection obligations remain open.
`QSB/FirstNumericRange.lean` closes that parser-to-roll-index link for all
nonnegative first-index values below 152 in the byte model: `OP_ADD` produces
offset `151+n`, and a matching `HASH160` result from the first signed roll
implies `n=2+i` and lock commitment `152+i` for some `i<150`. The first-index
prefix theorem allows arbitrary lower cells within the modeled stack limit.
`QSB/FirstNegativeRange.lean` additionally covers parsed values −1 through
−151: their computed roll depths are 150 down to 0, and none can produce a
matching `HASH160` output. `QSB/ByteIndexSign.lean` and
`QSB/FirstNegativeAll.lean` extend the local exclusion to every negative
parsed first index, conditional on the actual `OP_MIN`, `OP_ADD`, and
`OP_ROLL` steps succeeding. Arbitrary-scriptSig extraction, later
selections, and Core refinement remain open.
Together, the byte-model local-step theorem says that any parsed first index
below 152 whose first signed roll leaves an opening's `HASH160` value on top
must equal `2+i` for a fixed commitment `152+i`, with `i<150`.
`QSB/FirstAcceptedOrigin.lean` derives these steps and the first hash
comparison from every successful run of the full 880-op byte program under
the specified top-stack layout and granted pinning outcomes. Arbitrary
`scriptSig` extraction, later selections, and Core refinement remain open.
`QSB/PinningShape.lean` removes that layout premise within the byte model:
success from any initial byte stack and Boolean outcome list forces the top
three cells and two true pinning outcomes, then the same first lock commitment
origin. This says nothing about how a real `scriptSig` produces the initial
stack or how Core decides the signature outcomes.
`QSB/BareBoundary.lean` composes that theorem with an arbitrary partial
`scriptSig` evaluator. For the bare output, Core runs `scriptSig` and the lock
sequentially on one main stack, resetting the opcode counter between calls;
isolated native checks confirm non-push-only stack handoff and independent
201-op budgets. See [the boundary note](CORE-BARE-BOUNDARY.md) and
`evidence/bare-script-boundary.json`. The formal composition still assumes
Core's lock execution refines the byte model.

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
`QSB/ByteFinalCounts.lean` additionally checks the generated *byte* suffix:
success from any underlying byte stack preserves both raw 10 counts; a truthy
whole-program result requires the supplied final CHECKMULTISIG outcome true.
Its Boolean outcome is still external to Core's signature checker.

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
`QSB/ByteWitness.lean` executes one disposable 57-cell witness through all 880
byte opcodes, records 15 successful comparisons, and checks the final modeled
truth, 201-op count and 569-cell stack. It also confirms that the first-round
multisignature Boolean does not affect final truth in this byte fixture. Its
HASH160 is a lookup table for the 15 generated opening/commitment pairs, its
SHA256 is an arbitrary 32-byte function, and signature results are supplied
Boolean values. This is a model consistency check, not Core acceptance or a
hash/puzzle solution.
For stack-origin diagnostics against the same disposable setup, run
`python3 analysis/explore_origins.py --app-root /path/to/qsb-app --probe external`.
This Python trace supplies signature outcomes and is not a consensus test.

Read:

- [Final report](FINAL-REPORT.md)
- [Security game and attack table](SPECIFICATION.md)
- [Proof status and source mapping](PROOF-STATUS.md)
- [Bare-script Core boundary](CORE-BARE-BOUNDARY.md)
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
python3 analysis/generate_byte_witness.py --app-root /path/to/qsb-app --check
```

Omit `--check` to regenerate their respective Lean fixtures after deliberately
updating the pinned source. The byte layout generator also writes
`evidence/byte-layout-map.json`. Both byte generators cross-check the pinned
source hash; the layout generator also checks the exact script hash in
`evidence/layout-map.json`.

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
python3 analysis/check_bare_script_boundary.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/bare-script-boundary.json
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
