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

Either final-round bonus index can reach a locking-script HORS commitment
after canonical signed selections. `QSB/FirstBonus.lean` checks the first
bonus symbolic path. In a deliberately altered, puzzle-relaxed lock, Core
accepts that 20-byte value in either bonus signature slot when it is DER-shaped
and paired with a recovered public key.
The crafted value was not generated from a HORS secret, so this is a concrete
source-extraction edge case rather than a valid production-vault forgery. See
`evidence/bonus-overshoot.json`.

`QSB/RandomOracleSetup.lean` now checks a finite random-function setup fact:
when the whole R160 function is uniform and independent of material selecting
its inputs, each `R160(H256(secret))` hits a fixed 20-byte target set at the
target's exact density. A union bound covers all 300 commitments using the
same R160, even if inputs collide. The DER-20 arithmetic remains conditional
on a formal correspondence between that target set and Core's parser. This
does not bound adaptive quantum searches or the chance of an unauthorized
spend.

`QSB/Nonce.lean` models fixed-signature ECDSA recovery targets, including the
possibility that opposite recovery points admit different message scalars for
one signature and key. `QSB/RecoveryCandidates.lean` proves `p < 2n` for
secp256k1 and a conditional four-target bound when each x-coordinate admits
at most two parsed curve points. The curve/parser and Core digest bridges,
plus any joint quantum hash success bound, remain open. A public algebraic
fixture is in `evidence/ecdsa-replay-targets.json`.
The pinned app recovery helper reconstructs only x=`r`; its choice does not
restrict the recovery points relevant to a consensus attacker model. The same
fixture file records an x=`r+n` algebraic verification that this helper omits;
the test uses message scalar zero and supplies no Bitcoin transaction preimage.

`QSB/SighashBinding.lean` isolates the legacy `SIGHASH_ALL` output-binding
step under an explicit wire-encoding or output-parser premise and maps a
changed-output same-key verification to an admissible ECDSA message target.
`QSB/OutputCodec.lean`, `QSB/WireIntegers.lean`, and `QSB/WireOutputs.lean`
prove concrete CompactSize, nonnegative eight-byte amount, and ordered-output
round trips on their valid wire domains. A pinned 13-case Core probe checks
selected output, input, and `scriptSig` changes;
see [the sighash boundary](CORE-SIGHASH-ALL.md). The general transaction
Core refinement and quantum target-hit bounds are still open.
`QSB/SighashAllWire.lean` now proves that a complete source-shaped ALL
preimage reveals ordered outputs even with varying prepared input scripts,
version, input count, and locktime. One 139-byte Lean fixture matches the
pinned app's baseline preimage used in the Core probe.

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
For a pre-suffix stack `first :: rest`, the ten signature slots retain
`rest[0..9]`; successful modeled execution also forces the next source cell
`rest[10]` to exist and be empty under NULLDUMMY. This locates the final
signature and dummy bytes within the pre-suffix stack, but does not identify
their earlier selection sources. The Boolean outcome remains external to
Core's signature checker.
`QSB/ByteLatePuzzle.lean` now carries that result back across the exact seven
opcodes after the final bonus roll. Any post-bonus byte stack that completes
the generated suffix supplies its cells 0–9 as the final signatures and its
empty cell 10 as NULLDUMMY. This is independent of the earlier witness stack
shape, but it does not classify the signed/bonus selections that filled those
slots or prove Core's signature-verification result.
`QSB/FinalBonusBoundary.lean` then identifies the only two possible pre-roll
sources of that empty dummy: depth 10 when the last bonus index is below 10,
and depth 9 otherwise. `QSB/ByteBonusBetween.lean` transports shallow cells
through the fixed deep roll and cap between bonus choices. If the two relevant
pre-first-bonus source cells are nonempty, it proves that a first bonus index
below 9 or a last index below 10 cannot complete the modeled suffix.
`QSB/PoolRollInvariant.lean` checks that the generated second-round pushes
establish 150 nonempty dummy bytes, and that any seven pool-only signed rolls
leave those two source cells nonempty. The full-program byte-model theorem in
`QSB/FinalSignedChain.lean` now proves pool-only behavior for all seven signed
rolls from any initial byte stack and supplied signature outcomes; Core
refinement remains open.
`QSB/FinalSignedBoundary.lean` maps the first final-round signed lookup over
the exact generated commitment and dummy pushes: indices 0–1 select 9-byte
dummies, 2–151 select 20-byte commitments, and capped 152 selects the prior
round's Boolean CHECKMULTISIG result. Lean checks that the generated five-op
comparison tail rejects that capped case and shallow non-20-byte targets.
`QSB/FinalSignedAccepted.lean` derives that stack from any successful full
byte-model run, so the first final-round signed index must parse as `2+i`
for some `i<150`, and commitment `i` matches HASH160 of the actual opening.
`QSB/FinalSignedLoop.lean` checks the literal opcode schema for all seven
blocks. For any one reached block with the stated current pool shape and
original-index alignment, successful byte-model execution forces an in-range
current commitment, a matching actual opening, and removal of that commitment
and its paired dummy; both invariants survive for the next block. This includes
negative and nonminimal raw ScriptNum encodings.
`QSB/FinalSignedChain.lean` composes all seven blocks and proves that every
successful full generated byte-model run matches seven actual openings to
seven distinct original second-round commitments. It starts from an arbitrary
initial byte stack and supplied signature outcomes.
`QSB/FinalBonusAccepted.lean` carries the resulting nonempty shallow dummy
cells through the exact bonus prefix and final NULLDUMMY check. Every
successful full byte-model run therefore has decoded bonus depths in 9–152
and 10–152. Refining the model to Core remains open.
The reached first-bonus roll has a checked source map: depths 9–151 move an
unused 9-byte dummy, while depth 152 moves the first surviving 20-byte HORS
commitment. This is the commitment-as-signature setup exception in the byte
model. `QSB/FinalBonusSecond.lean` classifies the reached second roll: after a
dummy first choice, only second depth 152 reaches a commitment; after a
commitment first choice, every reachable second source is a dummy. It also
tracks the actual second moved byte. Its full-program theorem reaches both
post-bonus states from any initial byte stack and supplied signature outcomes
and records their selected-byte equations alongside the seven signed HORS
openings. Its final-witness theorem carries those bytes through the late
puzzle and key rolls: the ten pre-CHECKMULTISIG signature-source slots are
second bonus, first bonus, seven gathered dummy bytes, and the fixed nonce,
followed by the empty dummy. The only possible bonus commitment is the first
survivor from an original second-round HORS position not among the seven
matched openings; either overshoot puts it in a specific final signature slot.
Core signature validity and the DER-shaped setup
event remain open.
An additional conditional theorem excludes both commitment overshoots when
the reached bonus signature slots satisfy a supplied signature-syntax predicate
and every generated second-round commitment fails that predicate. Connecting
the syntax premise to Core's CHECKMULTISIG and bounding the setup event remain
separate obligations.
The checked final-bonus setup union bound charges only the 150 second-round
commitments, conditional on an actual parser-syntax marginal of
`390405/2^65` per commitment. It does not supply that marginal or bound a spend.
The conditional matching-loop theorem also derives bonus-slot syntax from a
successful ten-pair scan when each successful pair check implies that syntax.
Equating this scan and verifier with Core execution is still required.
`QSB/DERSyntax.lean` adds a source-shaped strict DER byte predicate and proves
the 20-byte R/S length and header constraints. Its equivalence to compiled
Core and exact accepted-set cardinality remain open.
It separately models the pinned `VERIFY_ALL` encoding gate's empty-signature
exception and proves that nonempty inputs reduce to strict DER. A 73-case
isolated parser differential test matched the pinned Core adapter throughout;
it does not prove full-lock signature verification.
`QSB/DERHeaderBound.lean` now proves a conservative target bound without that
exact count: at most `12·256^14` out of `256^20` twenty-byte outputs match the
Lean predicate. The generic independent random-function setup theorem gives a
150-target union bound of `150·12/256^6` for this syntax exception under its
explicit independence premise. This is not a spend or quantum-query bound.
`QSB/FinalBonusDER.lean` additionally checks that none of the 150 literal
second-round commitments in the disposable generated lock matches that
predicate. Its no-overshoot consequence still assumes a successful DER-sound
ten-pair final scan and does not cover other vault setups.
`QSB/FinalBonusIndices.lean` composes that conditional no-overshoot result
with the accepted full byte-model run. It identifies both reached bonus
signature bytes as generated dummies and proves that their original HORS
positions and the seven signed opening positions are nine distinct indices.
It also maps the seven gathered signature slots to those traced positions in
reverse draw order and identifies the fixed nonce and empty dummy slots.
The final scan and DER-sound verifier are explicit premises; Core refinement
and a quantum bound remain open.
`QSB/FinalRoundWitness.lean` converts the seven recorded opening pairs and
two bonus positions into the abstract `RoundWitness` shape. An executable
lookup supplies opening bytes, and Lean proves their HASH160 equalities. The
earlier bridge's witness key was a caller input; the reached-key theorem below
removes that freedom inside the byte model. Transaction-bound nonce semantics,
a transaction-byte extractor, and Core refinement are still open.

`QSB/ByteLayout.lean` is a second generated view of the same exact lock. It
retains literal push bytes for all 880 instructions; Lean checks that each of
its 15 `OP_EQUALVERIFY` instructions immediately follows `OP_HASH160`.
`QSB/EncodedLayout.lean` retains each instruction's original serialized bytes.
`QSB/EncodedScript.lean` parses those 9,923 bytes into 880 chunks, decodes
them back to `ByteLayout.program`, and checks the 151 final signature-push
patterns. This proves internal fixture alignment, not equivalence with Core's
`GetOp` or `FindAndDelete`.
`QSB/FindAndDelete.lean` proves the sequential deletion result for the
source-shaped Lean byte loop and every selected final-signature list. It does
the same for the fixed pinning signature's one serialized push. It does not
replace a Core C++ refinement or transaction-level extraction proof.
`QSB/FinalScriptCode.lean` derives that modeled scriptCode from the ten
signature bytes actually reached in a conditional successful final byte-model
run. The Core final-scan premise remains external.
`QSB/ByteLatePuzzle.lean` and `QSB/FinalRoundWitness.lean` further identify the
last reached multisignature key with the key SHA256-hashed into the late puzzle
signature. A conditional theorem derives strict-DER syntax of that hash from
an encoding-sound reached puzzle check. Core verifier and sighash refinement
are still required.
`QSB/PinningScriptCode.lean` extracts the reached pinning nonce and puzzle key
bytes from any successful arbitrary-stack byte-model run. With explicit
verification premises it proves strict DER for SHA256 of the reached pin key.
`QSB/SourceWitness.lean` combines that result with the final-round extraction
in the same run; the Core verifier bridge and quantum bound remain open.
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
`QSB/EncodedLayout.lean` and `evidence/byte-layout-map.json`. Both byte
generators cross-check the pinned source hash; the layout generator also
checks the exact script hash in
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
python3 analysis/check_der20_parser.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/der20-parser.json
python3 analysis/check_find_and_delete_boundary.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/find-and-delete-boundary.json
python3 analysis/check_ten_signature_findanddelete.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/ten-signature-find-and-delete.json
python3 analysis/check_literal_findanddelete.py --app-root /path/to/qsb-app --output evidence/literal-find-and-delete.json
python3 analysis/check_bonus_overshoot.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/bonus-overshoot.json
python3 analysis/check_bonus_indices.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/bonus-indices.json
python3 analysis/check_scriptnum_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/scriptnum-core.json
python3 analysis/check_roll_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/roll-core.json
python3 analysis/check_final_signed_boundary.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/final-signed-boundary.json
python3 analysis/check_ecdsa_replay_targets.py --app-root /path/to/qsb-app --output evidence/ecdsa-replay-targets.json
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
