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

The parameterized final-round byte-model proof now carries seven distinct
second-round openings through both bonus draws and the final signature-source
slots. Under an explicit matched DER-sound scan, an overshooting bonus draw
requires an unopened DER-shaped commitment. With no such commitment, Lean
extracts nine distinct original positions from the same run. For a shared
uniform twenty-byte-output setup function independent of its 150 input choices,
the excluded setup probability is at most `150·12/256^6` under the uniform
finite-space measure; later modeled witnesses may depend on the sampled
function. See `QSB/DynamicBonusSetup.lean` and
`QSB/DynamicBonusProbability.lean`. `QSB/DynamicSerializedRound.lean` proves
that canonical serialization of arbitrary 20-byte final commitments and a
short nonce parses to this parameterized byte program under the Lean
Core-shaped GetOp model. `QSB/DynamicSourceGate.lean` derives the matched DER
gate from a successful source-shaped final ten-pair evaluator. A four-run
disposable builder check includes a crafted DER-shaped commitment, but
universal Python-builder and compiled-Core refinement remain open. The joint
quantum unauthorized-spend bound remains open.
`QSB/DynamicWholeSource.lean` composes any modeled initial stack and
first-round opcode prefix with the parameterized final round. It derives the
prior result's short width from the first `CHECKMULTISIG` transition and
proves the good-setup nine-position consequence with an executable opening
trace under a successful
source-shaped final evaluator. Its full-program form specializes to the
literal fixture; real builder and Core acceptance links remain open.
`QSB/DynamicWireSource.lean` extends the source-shaped result to full
serialized script bytes under an explicit, well-formed prior-chunk contract.
The separately written GetOp parser recovers the exact modeled opcode list;
the builder-output and compiled-Core links are still unproved.
`QSB/DynamicCoreStructural.lean` derives the required byte execution from a
single successful bottom-first source-shaped run of those parsed opcodes and
checks the final source evaluator at that run's reached pre-check stack.
Its signature Booleans and ECDSA/sighash checker remain external inputs.
`QSB/DynamicFullSerialized.lean` supplies the earlier chunks for arbitrary
20-byte commitments in both rounds and short pin/nonce pushes, so the complete
Lean wire lock parses without an arbitrary-prior-chunk premise. Its first
446 chunks match the literal fixture. `analysis/check_dynamic_full_data.py`
checks four complete pinned-builder outputs against that parameterized layout;
the Python-to-Lean universal equality remains open.
`QSB/DynamicCheckedCertificate.lean` searches the two first-round Boolean
cases and checks source-shaped signature evaluations at the reached stacks.
A returned certificate implies the good-setup nine-position result, while
compiled-Core acceptance and the verifier implementation remain unproved.
The reached-slot theorem also identifies all nine source-addressed dummy
signatures under that good-setup premise. `QSB/DynamicJointTransaction.lean`
splits their external ECDSA calls by the actual selected input and output
count: in-range SINGLE hashes its transaction preimage twice, while
out-of-range SINGLE uses the raw constant bug digest. All nine dummy pairs
share one digest in either branch. The tenth nonce call remains separate.
`analysis/audit_builder_parametric.py` checks the pinned Python source's
byte-value flow: variable commitments, dummies, and nonce bytes enter
`_emit_round` only through data pushes, while suffix depths use stack labels.
It is a source audit, not a formal Python-to-Lean refinement.
`QSB/DynamicSetupReduction.lean` gives the resulting conditional game
inequality: `Pr[Unauthorized] ≤ εfresh + εdistinct + εsame + 150·12/256^6`.
The fresh-opening and two puzzle-search terms are unproved joint-QROM event
bounds. The theorem also requires actual transaction/Core extraction on every
good setup and a uniform setup marginal, so it is not a deployed-security
claim. `QSB/JointOracleReduction.lean` also gives a world-indexed interface:
the same sampled `H` and `R` determine commitments and puzzles, while the
attacker output and disclosures depend on that world. Its one-event bound is
`Pr[Unauthorized] ≤ εjoint + εgap`, or `εjoint + 150·12/256^6` under the
good-setup extraction and uniform setup premises. No nontrivial `εjoint` or
shared coherent-query theorem is proved.

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
`evidence/four-recovery-points-core.json` separately records a disposable
bare-script SHA256d transaction for which pinned Core accepts all four
recovery-point keys for one fixed DER signature. It is not a QSB spend.

`QSB/SighashBinding.lean` isolates the legacy `SIGHASH_ALL` binding
step and maps a same-key verification on an owner-forbidden semantic
projection to an admissible ECDSA message target. The source-shaped preimage
is distinct from each approved release under a fixed ledger-resolution
function, even when scriptSig bytes, selected input, or scriptCode vary.
`QSB/OutputCodec.lean`, `QSB/WireIntegers.lean`, and `QSB/WireOutputs.lean`
prove concrete CompactSize, nonnegative eight-byte amount, and ordered-output
round trips on their valid wire domains. A pinned 13-case Core probe checks
selected output, input, and `scriptSig` changes;
see [the sighash boundary](CORE-SIGHASH-ALL.md). The general transaction
Core refinement and quantum target-hit bounds are still open.
`QSB/SighashAllWire.lean` now proves that a complete source-shaped ALL
preimage determines version, ordered outpoints and sequences, ordered
outputs, and locktime. It also proves that input-script preparation preserves
those committed input fields. One 139-byte Lean fixture matches the pinned
app's baseline preimage used in the Core probe. The actual Core serializer
and ledger resolution remain separate refinement obligations.
`QSB/ScriptSigSighash.lean` separates original scriptSig erasure at fixed
scriptCode from witness-dependent final FindAndDelete. Two complete candidate
final-signature selections of the literal lock produce distinct source-shaped
ALL preimages even with identical transaction fields. Neither selection is
proved accepted by the unmodified lock, and SHA256d collision resistance is
not inferred from preimage inequality.
`QSB/FinalSubsetInjective.lean` proves the general literal-lock version:
selected dummy-position sets and source-shaped final ALL preimages have the
same equality classes for fixed valid transaction fields and selected input.
The result does not count reachable Core-accepted subsets or quantum queries.
A [pinned full-lock differential](evidence/full-subset-switch-core.json) tests
two final subsets on a synthetic two-output transaction. The puzzle-relaxed
lock accepts each with its recovered keys but rejects reuse of the first
subset's final nonce key for the second. Three puzzle checks are disabled, so
this is not an accepted spend of the unmodified lock.
`QSB/JointSourceChecks.lean` also proves that an out-of-range SINGLE checker
call keeps the raw constant digest after any output-list replacement that
leaves the selected input past the last output. A cross-checked test adapter
using the same pinned Core library accepts a three-input, two-output
puzzle-relaxed full lock with QSB at input 2. That layout reuses its final nine
dummy keys after both outputs change, provided the fixed ALL keys are
rederived. See `evidence/full-two-outputs-core.json`; this is finite evidence,
not an unmodified-lock spend or a Core-to-Lean proof.
The same adapter accepts the puzzle-relaxed QSB input alongside a P2WSH
companion input in SegWit transaction serialization. `QSB/SegwitTxWire.lean`
parses and round-trips that canonical envelope and proves its source-shaped
legacy digest ignores witness-only changes. Complete Core transaction parsing
and arbitrary-witness extraction remain open.
`QSB/WireIntegers.lean` additionally proves that every successful CompactSize
parse consumed the shortest encoding; the SegWit envelope parser now rejects
all-empty witness records. Nine pinned Core framing cases are recorded in
`evidence/tx-framing-core.json`. The source model still lacks Core's complete
parser, resource bounds, and transaction-consensus validation.
The generic prefix-codec converse proofs now show that **every successful
Lean parse** of a raw legacy or SegWit transaction re-encodes to exactly its
returned fields and any trailing bytes. This does not establish that all
Core-accepted raw transactions are parsed by Lean.
`QSB/TransactionEnvelopeWire.lean` adds the initial-input-count branch and a
strict combined parser for nonempty-input spends. A successful modeled raw
legacy digest yields one canonical envelope and the shared-H SHA256d preimage
or SINGLE-bug case. Compiled-Core parser and checker correspondence remain
open.

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
`QSB/ScriptNumExtensional.lean` proves that numeric opcode transitions and
their remaining byte-model suffixes depend on parsed ScriptNum values rather
than canonical encodings. In the complete puzzle-relaxed native lock, all 18
witness indices can be changed to nonminimal four-byte values or PUSHDATA1
pushes of those values without losing acceptance; a five-byte first index
rejects. A truncated-lock pair accepts that five-byte value just before the
first `OP_MIN` and rejects with the opcode included. See
`evidence/full-two-outputs-core.json` and `evidence/selection-prefix.json`.
This is finite Core evidence, not a compiled-interpreter proof or an
unmodified-lock spend.

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
removes that freedom inside the byte model. The later raw-byte frontend is
conditional on an external scriptSig evaluator and checked-source run;
consensus-bound extraction and Core refinement remain open.

`QSB/ByteLayout.lean` is a second generated view of the same exact lock. It
retains literal push bytes for all 880 instructions; Lean checks that each of
its 15 `OP_EQUALVERIFY` instructions immediately follows `OP_HASH160`.
`QSB/EncodedLayout.lean` retains each instruction's original serialized bytes.
`QSB/EncodedScript.lean` parses those 9,923 bytes into 880 chunks, decodes
them back to `ByteLayout.program`, and checks the 151 final signature-push
patterns. Separate source-shaped Lean `GetOp` and `FindAndDelete` loops now
agree with the parsed fixture; compiled Core equivalence is still open.
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
`QSB/CoreChecksigEval.lean` models the BASE `CHECKSIGVERIFY` success path under
the pinned `VERIFY_ALL` flags. Its conditional theorems expose the fixed
pinning signature's `SIGHASH_ALL` checker call and the two reached
SHA256-derived puzzles' actual trailing sighash bytes. Both puzzles use the
unmodified literal lock as source-shaped scriptCode. The external checker
and Core refinement premises remain explicit.
`QSB/CoreFinalChecksigEval.lean` similarly exposes each reached final
multisignature pair's actual hash-type byte, parsed-key condition, and
external ECDSA/sighash call on the one selected scriptCode, conditional on a
successful source-shaped final ten-pair evaluation.
`QSB/CoreStructuralRun.lean` composes source-shaped structural transitions
for all generated opcodes. A successful bottom-first run of the literal lock
from any post-scriptSig stack projects to the byte-model run, including
signature-site count parsing and stack cleanup. `QSB/CoreMultisigStep.lean`
and `QSB/CoreChecksigStep.lean` provide those signature-site transitions;
their cryptographic outcomes remain supplied Booleans. Compiled Core and
real checker/sighash refinement remain open.
`QSB/CoreSourceExtraction.lean` combines one truthy source-shaped run with
source-shaped checks of all six reached signature sites, including the
first-round multisignature at its actual stack. `QSB/CoreMultisigSourceScan.lean`
computes that site's source-shaped Boolean after shared FindAndDelete and
requires it to match the supplied structural outcome, which may be false.
`QSB/CorePushSerialize.lean` supplies Core's direct/PUSHDATA1/PUSHDATA2
signature-push encoding for this arbitrary-witness scan; the direct-only
pattern used by the final fixture is invalid at 76 bytes and above.
`QSB/CorePushFindAndDelete.lean` proves that any such canonical pattern
deletes only whole original chunks of the fixed lock, so 880 source-loop
steps suffice after any sequence of reached-signature deletions.
The checked theorem extracts the pin key and a
seven-plus-two final-round witness, then exposes both fixed signatures'
`SIGHASH_ALL` checker calls and their reached scriptCodes. The first-round
multisignature is still allowed to return false. This is a source-model
certificate, not a theorem from compiled Core acceptance or a QROM bound.
`QSB/CoreCheckedStep.lean` computes each reached signature result instead of
accepting a caller-supplied Boolean. For a truthy full run of the literal
lock, `QSB/CoreCheckedRunCertificate.lean` proves that its six computed
results satisfy the source certificate and have shape
`[true, true, true, firstRound, true, true]`. The two-candidate search finds
a certificate, and the pin/final extraction theorem exposes the fixed
`SIGHASH_ALL` checker calls. The key parser, ECDSA and transaction digest
remain external functions; compiled-Core refinement and the shared-budget
quantum bound are still open.
`QSB/CoreCheckedDynamic.lean` extends the checker-derived final result to
every parameterized Lean Config A lock. A truthy checked run reaches the
ten-key, ten-signature, empty-NULLDUMMY layout and passes the actual final
ten-pair source scan. With 20-byte second-round commitments, it either exposes
a DER-shaped commitment in the setup or extracts seven matching openings and
nine distinct second-round positions. The external checker and the missing
compiled-Core and builder refinements still prevent a consensus-level claim.
The same checked run now has exactly six computed signature records and passes
the parameterized two-candidate certificate search. In
`QSB/CoreCheckedJointTransaction.lean`, specializing its checker to one
transaction yields both DER key puzzles and fixed `SIGHASH_ALL` calls under the
shared `H`; on a good setup it also yields seven `R(H(opening))` equations and
the final ALL call. This remains a deterministic modeled event, without a
shared-query probability bound.
`QSB/CoreCheckedWire.lean` accepts supplied locking-script bytes and checks
exact equality against a claimed parameterized Lean lock. For 20-byte
commitments and short fixed signatures, its source-shaped parser recovers the
opcode program, and the same joint event follows from a truthy checked run.
This validates an individual script without assuming universal Python-builder
equality. The spent-output-byte connection, compiled-Core refinement, and
real ECDSA/key parsing remain open; the pinned builder audit and four finite
byte comparisons are only corroboration.
`QSB/DynamicRoundWitness.lean` computes a good-setup final-round witness from
the returned checked-source certificate, including seven reached openings,
two bonus positions, and the reached final key. The validated supplied-wire
theorem keeps both strict-DER puzzle hits and both fixed ALL checker calls in
the same hash world. This remains conditional on the source-model run and
external checker functions; it is not a Core-acceptance or quantum bound.
`QSB/DynamicSourceGame.lean` uses that executable witness and the reached pin
key to discharge the abstract game extraction interface for truthy checked
source attempts on a good setup. Its resulting fresh-opening-or-two-puzzle
event has no source-model extraction gap. A raw transaction-to-model
refinement and a shared-query quantum bound are still required.
`QSB/DynamicRawSource.lean` begins with a complete raw transaction and selects
the scriptSig of the stated input through the Lean legacy/SegWit envelope
parser. Given an explicit evaluator for that arbitrary scriptSig, it computes
the checked-source attempt and proves the same game event. Core parser and
execution correspondence, actual spent-output lookup, and the quantum bound
remain unproved.
`QSB/ByteMachine.lean` models these byte comparisons with arbitrary hash
functions and a source-shaped ScriptNum parser. It proves that if an arbitrary
stack reaches a `HASH160; EQUALVERIFY` pair and the remaining program succeeds,
the actual opening bytes hash to the compared commitment bytes. This local
result does not identify where the commitment came from. `QSB/ByteTrace.lean`
records equality pairs and proves that erasing the record recovers the modeled
execution; the compiled-Core arbitrary-witness bridge is still open.
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
python3 analysis/check_nonce20_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/nonce20-core.json
python3 analysis/check_multisig_early_exit.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/multisig-early-exit.json
python3 analysis/check_multisig_push_serialization.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/multisig-push-serialization.json
python3 analysis/check_find_and_delete_boundary.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/find-and-delete-boundary.json
python3 analysis/check_pin_puzzle_scriptcode_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/pin-puzzle-scriptcode-core.json
python3 analysis/check_ten_signature_findanddelete.py --app-root /path/to/qsb-app --native-root /path/to/native --image ubuntu@sha256:b1066385161d28ddf6bc7e7b28a9170eec11484c821d1a5150d176cbde41d7f7 --output evidence/ten-signature-find-and-delete.json
python3 analysis/check_literal_findanddelete.py --app-root /path/to/qsb-app --output evidence/literal-find-and-delete.json
python3 analysis/check_bonus_overshoot.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/bonus-overshoot.json
python3 analysis/check_bonus_indices.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/bonus-indices.json
python3 analysis/check_dynamic_final_data.py --app-root /path/to/qsb-app --output evidence/dynamic-final-data.json
python3 analysis/check_dynamic_full_data.py --app-root /path/to/qsb-app --output evidence/dynamic-full-data.json
python3 analysis/audit_builder_parametric.py --app-root /path/to/qsb-app --output evidence/builder-parametric-audit.json
python3 analysis/check_scriptnum_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/scriptnum-core.json
python3 analysis/check_min_add_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/min-add-core.json
python3 analysis/check_roll_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/roll-core.json
python3 analysis/check_final_signed_boundary.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/final-signed-boundary.json
python3 analysis/check_full_two_outputs_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/full-two-outputs-core.json
python3 analysis/check_ecdsa_replay_targets.py --app-root /path/to/qsb-app --output evidence/ecdsa-replay-targets.json
python3 analysis/check_four_recovery_points_core.py --app-root /path/to/qsb-app --native-root /path/to/native --image sha256:IMAGE_DIGEST --output evidence/four-recovery-points-core.json
```

The full-lock command also runs `analysis/core_variable_inputs_adapter.py`
inside the same pinned container to call Core's API for every spent output in
the three-input cases. Its two-input positive and negative controls are
cross-checked against the original native wrapper; the evidence records the
adapter source hash and per-input Core results.

The recorded source inventory identifies exactly the files analyzed. The app
checkout was clean at capture. The solver baseline was
`8fe127790397b6903640f8949219c1ef34a92db2`; the app inventory and Core
experiment use `3eef7c39ecbe897ac55251841e9f2ec3764e04ad`. The app advanced
from the initially inspected `231973b0b7187416f25cc755d1c2abf5f1a954fd`
only in custody documentation; all inspected executable source-file hashes are
unchanged. The later eight-case bare-script boundary rerun records app checkout
`4389e25077d48354dd85347391b6ca6a47888bd5` and asserts the same pinned
`worker/cpu/bitcoin_tx.py` SHA-256. It uses the recorded Core library and
adapter hashes. The solver was not modified to alter
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

1. Refine the source-shaped opcode, signature-check, scriptSig, and
   transaction-sighash models to every consensus-accepted arbitrary witness
   on the pinned output. Handle DER-shaped setup/commitment exceptions in the
   resulting extractor.
2. Derive a precise fresh-message event from the reached pinning and final
   ECDSA checks, including accepted key encodings, sighash collisions, and
   the signature's actual hash-type byte.
3. Prove or find a counterexample to a joint quantum query bound for
   SHA-256/SHA256d/HASH160 after adaptive disclosures and multiple vaults.
   Standard HORS and ordinary unstructured-search bounds do not establish it.

These obligations are unresolved. The goal remains active.
