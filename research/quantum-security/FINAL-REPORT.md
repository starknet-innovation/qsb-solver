# QSB conditional quantum-security analysis: report

## Result

No nontrivial upper bound on unauthorized-spend probability for the inspected
QSB Config A output has been established. The Lean project proves structural
facts and a conditional reduction, but the actual arbitrary-witness Bitcoin
Script extraction and the joint quantum hash-search bound remain open. It
would be unsound to report a quantum security level from the DER target
density, a solver benchmark, or the current Lean build.

The app source is pinned by `evidence/source-inventory.json` at
`3eef7c39ecbe897ac55251841e9f2ec3764e04ad`. This work changed only the
solver repository's `research/quantum-security/` directory. No wallet secrets,
funds, transactions on a network, paid infrastructure, or deployed code were
used.

## Material construction findings

1. The first digest round's `OP_CHECKMULTISIG` Boolean is left on the stack
   and is not verified. The final round's result controls the stack top. A
   modified-lock Core test accepts an invalid first-round multisignature but
   rejects an invalid final-round one. Earlier first-round HORS comparisons
   remain enforced. Three hash-to-signature puzzle checks were replaced with
   `OP_2DROP` in that test, so it is not a real-lock unauthorized spend.
2. Fixed-signature ECDSA public-key recovery works for a new message without
   discrete-log secrecy. Lean checks the field equation for a fixed recovery
   point, and isolated Core tests accept recovered keys after destination
   changes. The security game grants the adversary all exposed EC discrete
   logarithms. The first-round Boolean finding makes reuse of released
   first-round material a concrete attack route, conditional on solving the
   remaining pinning/final puzzles.
3. `OP_MIN` alone does not confine selection to intended pools. A generated
   Lean trace and truncated Core tests show the first signed roll can select
   an external cell and pass a self-chosen `HASH160` comparison. A new byte
   theorem covers any marker bytes and any parsed first-index value
   at least 152 (including nonminimal encodings in the byte model), and any
   post-index continuation stack, including an empty one. An
   empty continuation fails the external-cell roll; fewer than eight cells
   after a marker fail the opening roll. Otherwise a marker mismatch fails the first `HASH160` comparison;
   with a match, the next fixed roll selects a 20-byte lock commitment as a
   numeric index, so `OP_MIN` fails. Longer stacks reject at the modeled
   1000-cell limit during pinning, lock pushes, or early selection.
   Unparsable first-index bytes also fail at the first `OP_MIN`. Lean now
   connects these failures to the full byte-model program from an initial
   stack of two pinning keys followed by the first index and arbitrary cells,
   granting true outcomes for both pinning checks and arbitrary later
   signature outcomes. A successful modeled run with this layout has a parsed
   first-index value below 152. This is one family of arbitrary byte values, not a
   complete arbitrary-scriptSig extraction. Pinned Core prefixes for canonical
   152, nonminimal `980000`, and four-byte `ffffff7f` accept immediately
   before that `OP_MIN` and reject when it is added. These are
   truncated, puzzle-relaxed tests, not full-lock acceptance.
   A separate Lean lookup map proves that the 150 fixed cells at depths
   152–301 are 20-byte commitments and a roll at depth `153+i`, `i<150`,
   selects exactly one of them regardless of the lower witness stack. The
   152 shallower fixed cells cannot equal a HASH160 output by length. This
   narrows the first-selection provenance question without proving which
   indices every accepted scriptSig can supply. A further Lean lemma says that
   any matching HASH160 lookup with a roll index at most 302 and a retained
   cell no longer than four bytes must identify one of those 150 commitments.
   For every nonnegative first-index value below 152, Lean now checks the
   ScriptNum encodings and proves that the byte-model `OP_ADD` yields roll
   depth `151+n`. A modeled hash-matching first roll therefore requires
   `n=2+i` and selects fixed commitment `152+i`, for `i<150`.
   The 151 negative values from −1 through −151 are also checked: their
   computed roll depths are 150 down to 0, and none can select a matching
   HASH160 cell. A general sign-preservation proof extends this local
   exclusion to every negative parsed first index when the generated
   `OP_MIN`, `OP_ADD`, and `OP_ROLL` steps succeed. The arbitrary
   accepted-scriptSig path remains open. Combining the cases, any parsed
   first index below 152 whose reached byte-model `OP_MIN`, `OP_ADD`, and
   signed `OP_ROLL` leave an opening's HASH160 output on top must be `2+i`
   and identify fixed commitment `152+i`, for `i<150`. Lean now derives those
   local steps and the first `HASH160; EQUALVERIFY` from every successful
   full 880-op byte-model run with the stated top-stack layout and granted
   pinning outcomes. Arbitrary `scriptSig` extraction, later selections,
   signature semantics, and Core refinement remain open.
   A further Lean theorem removes that starting-layout premise *inside the
   byte model*: any successful run from an arbitrary initial byte stack and
   Boolean outcome list forces three top cells and two true pinning outcomes,
   then the same first lock-commitment origin. It does not justify those
   outcomes against Core. A separate Lean composition permits any partial
   `scriptSig` evaluator to produce that initial stack. Core 27.2 source and
   five isolated native tests confirm that the bare lock receives the
   `scriptSig` stack with a fresh opcode counter, even when `scriptSig` is not
   push-only. This removes a canonical scriptSig-shape premise from the
   modeled first-origin statement, but does not prove Core's lock execution
   refines the byte model or settle later selections.
4. Either final-round bonus index can select a locking-script HORS commitment
   at 152 rather than a dummy signature after canonical signed selections.
   Lean checks both symbolic paths. On a deliberately altered 20-byte
   DER-shaped commitment, the puzzle-relaxed full lock passes Core's actual
   final `CHECKMULTISIG` with a recovered public key in either slot; the natural
   commitment rejects both overshoots. The crafted commitment does **not**
   equal `HASH160` of its generated HORS secret. This is a source-extraction
   edge case and a possible bad-setup condition, not a production-vault
   forgery or a solved real hash puzzle. The six recorded Core 27.2 cases were
   reproduced byte-for-byte with the rebuilt pinned adapter.
5. Under the canonical preceding stack, Lean classifies all 153 cells reachable
   by the last final-round bonus roll: eight gathered signatures, the fixed
   nonce signature, the zero dummy, 142 unused dummy signatures, then one HORS
   commitment. A local Lean theorem shows indices 0–9 shift a nonzero generated
   dummy into the prospective NULLDUMMY slot. Boundary Core tests on the
   puzzle-relaxed full lock accept sampled fresh dummy choices 10, 11 and 151,
   reject sampled nonfresh choices, and reproduce the index-152 commitment
   exception. This narrows the canonical-prefix case but does not prove an
   arbitrary-witness invariant. Nonminimal index encodings of numeric 10 and
   152 also pass the same Core adapter. Lean checks those byte examples and
   now proves for every byte list that OR-ing disjoint eight-bit lanes equals
   arithmetic little-endian assembly, with the assembled word below
   `256^length`. Lean also proves sign-bit subtraction equals keeping the
   lower bits for every negative one- to four-byte encoding; all successfully
   parsed operands lie in Core's unsaturated `getint` range. The pinned
   adapter accepted a finite `OP_1ADD` differential
   probe of 2,384 encodings (including every canonical integer from −1023
   through 1023) and rejected one five-byte operand. A source-shaped
   Lean conversion using Core's bitwise sign test and 64-bit complement mask
   now equals the parser for every allowed byte string. Compiled-Core
   whole-interpreter refinement remains open. A separate Lean range theorem
   shows that the modeled serializer cannot fail on `OP_ADD` or `OP_MIN`
   results from two successfully parsed operands. A source-shaped
   bottom-first `OP_ROLL` model also agrees with the top-first Lean byte step
   for every raw index and stack, subject to its opcode budget. Eleven isolated
   pinned-Core cases corroborate the modeled depth and parsing boundaries;
   compiled-Core trace refinement is still required.
   A source-shaped Core magnitude-byte loop now has a universal decode and
   fuel-stability proof. The byte model was revised to use the same low-byte
   loop; Lean proves the two source-shaped serializers agree for every integer,
   including their common five-byte magnitude guard.
   Every parsed four-byte operand pair has a defined `OP_MIN` and `OP_ADD`
   result, and the source-shaped numeric transitions match `ByteMachine.step`
   under its opcode budget. Lean also excludes signed 64-bit overflow when
   adding two parsed operands. A 17-case pinned-Core bare-script differential
   includes negative, nonminimal, and overshoot inputs, with a wrong-byte
   control and five-byte rejection. `QSB/ScriptNumExtensional.lean` additionally
   proves that all raw operands with equal parsed ScriptNum values induce
   identical modeled `OP_MIN`, `OP_ADD`, and `OP_ROLL` transitions and every
   subsequent byte-model suffix. It proves that every positive value below
   `2^24` parses unchanged in the deliberately nonminimal four-byte encoding,
   while appending a fifth byte fails the parser. Source-shaped roll and
   numeric substeps have the same extensionality. On one complete disposable
   puzzle-relaxed lock, pinned Core accepted replacing all 18 witness indices
   by those four-byte encodings or by PUSHDATA1 pushes of the same bytes; a
   five-byte first index rejected. A separate pinned-Core truncated-lock pair
   with the same five-byte index accepts immediately before the first
   `OP_MIN` and rejects when that opcode is added. This isolates the first
   numeric parse in that one witness. These are finite tests, not a universal
   Core interpreter refinement or real-lock spend.
   A bottom-first source-shaped Lean interpreter now agrees with the existing
   top-first byte interpreter over every non-signature segment of the exact
   880-opcode lock, for arbitrary starting stacks and modeled resource limits.
   Lean checks the six intervening signature-opcode positions and that the
   partition reconstructs the whole program. This still needs a compiled-Core
   interpreter relation and actual signature-checker refinement before it can
   support arbitrary-witness extraction.
   A rebuild of the pinned Core 27.2 adapter reproduced the recorded 13
   boundary cases byte-for-byte, including the NULLDUMMY-slot rejection. The
   separate six-case overshoot report had mislabeled the canonical first
   bonus index as 10; the witness bytes actually use 9. Its metadata is now
   derived from the builder, and all six native outcomes and transaction
   hashes were reproduced unchanged.

The complete spend-path and attack table is in `SPECIFICATION.md`. It covers
funding, pinning, both rounds, index and scriptSig manipulation, disclosure,
recovery, alternate transaction layouts, policy, and chain inclusion.

## Reuse of the released first-round puzzle

The paper's Config A second-preimage estimate in Section 4.5 charges a fresh
first-round hash-to-signature hit for each new pinned transaction. The emitted
lock does not enforce the first-round `CHECKMULTISIG` result, so that factor
cannot be charged after a valid spend has disclosed its first-round witness.
The attacker can retain the released first-round HORS openings, indices, and
nonce key. In the pinned Config A builder, its `SHA256(nonce key)` remains the
same DER-shaped signature; the paper instead describes RIPEMD160 puzzles.
For a changed transaction with an admissible recovered key, the attacker can
use a new public key for that fixed puzzle signature and the new puzzle
sighash. The fixed first-round `SIGHASH_ALL` nonce signature and dummy
signatures may then fail inside the
unchecked multisignature. Pinning and the final-round multisignature still
have to pass. `QSB/Layout.lean` checks the discarded-Boolean stack behavior,
`QSB/Nonce.lean` checks public-key recovery algebra for any new message under
an admissible recovery point. The disposable pinned-Core case
`changed_destination_reused_round1_nonce` accepts a changed destination even
though the retained nonce key fails its new first-round `SIGHASH_ALL` message;
that older fixture relaxes all three hash-to-signature checks. A sharper
four-case Core probe in `evidence/first-round-replay-core.json` keeps the
first-round puzzle's real `CHECKSIGVERIFY`, inserts one fixed DER puzzle
signature in place of `OP_DUP; OP_SHA256`, and relaxes only the pin/final
puzzle checks. It accepts the changed destination with the old, valid SEC
first-round nonce key and a newly recovered puzzle verification key, and
rejects the same changed transaction with either the stale puzzle key or a
stale final-round nonce key. The old first-round nonce key independently fails
its new ALL digest. The substituted constant signature bypasses the first
hash search, so these are finite control-flow and ECDSA observations, not an
unmodified-lock spend.

Using **only an independent-hit work heuristic** for comparison, a fresh
first-round search with one bonus index contributes roughly `142p` per pinned
attempt, and the final round with two bonus indices contributes roughly
`C(143,2)p = 10153p`. Reusing the disclosed first-round puzzle removes the
`142p` factor. With the paper's 20-byte RIPEMD160 target expression
`p20 = 390405/2^65 ≈ 2^-46.425`, illustrative pin-plus-final work is
`1/(p20 · 10153p20) ≈ 2^79.54`, compared with about `2^118.82` if all
three hits were renewed. For the pinned builder's 32-byte SHA256 puzzles,
the syntax-count expression `p32 = 780555/2^65 ≈ 2^-45.426` instead gives
about `2^77.54` versus `2^115.82` under the same heuristic.
These are comparisons within a simplified classical heuristic, **not** a
proved attack complexity, a full-lock unauthorized spend, or a QROM success
bound. In particular, Core extraction, shared-oracle correlations, adaptive
disclosure, and the exact DER-parser density remain open. The checked
reduction therefore targets pinning plus the *final* round, not three
independent puzzle hits.

## What Lean proves

The pinned Lean 4.30.0/mathlib build checks every project theorem dependency list with
no project axioms, `sorry`, `admit`, or native decision oracle. The reported
dependencies are only the standard Lean foundations listed in
`evidence/axiom-audit.json`. The proved statements include disclosure-union
and cardinality accounting, fixed-recovery-point ECDSA algebra, abstract
without-replacement selection, concrete generated stack traces, owner-forbidden
message classification, and measure union bounds. Witness and disclosure
records expose HORS values only at opened positions.

An arbitrary-underlying-stack theorem covers the final key-roll suffix: if
its ten constant-index rolls complete, the two final CHECKMULTISIG count
operands are both 10. A separate Lean model of Core's key-scanning loop proves
that a successful equal-count match verifies every corresponding signature/key
pair. This fixes the count and matching obligations. The full-program
byte-model provenance of those cells is now established below; refinement
from the abstract pair predicate to Core's byte parser, FindAndDelete
scriptCode and ECDSA checker remains open.
`QSB/CoreMultisigStack.lean` now proves the source indexing behind that
statement: Core's bottom-first `stacktop(-i)` reads count cells at top-first
offsets 0 and 11, ten keys at 1–10, ten signatures at 12–21, and NULLDUMMY
at 22. A truthy successful full byte-model run reaches those cells; under an
externally justified successful ten-pair scan, each source-addressed pair
satisfies the supplied verifier. This does not establish Core's actual
signature outcomes.
The exact generated byte suffix now has the analogous arbitrary-stack result:
every successful, truthy full byte-model run reaches the final CHECKMULTISIG
with both count operands encoded as 10, and its externally supplied outcome
must be true. A further arbitrary-stack theorem identifies its ten signature
slots as the first ten cells following the shallow key in the pre-suffix
stack; the next cell is the NULLDUMMY source and must exist and be empty on a
successful modeled run. The full-program byte-model source theorem below now
connects those cells to the earlier selections; Core signature outcomes remain
unjustified.
The exact seven-opcode segment after the last bonus roll preserves its first
eleven shallow cells through the late puzzle check and moves a deep key above
them. Consequently, for *any* post-bonus byte stack on which the remaining
generated program succeeds, cells 0–9 are the final signature bytes and cell
10 exists and is empty under the modeled NULLDUMMY rule. The full-program
byte-model theorem below now supplies earlier signed/bonus provenance. Core
refinement and ECDSA outcomes remain open.
The next two local results carry that constraint backward through both bonus
rolls. For any byte stack before the last roll, a shallow last index needs an
empty cell at source depth 10; a deep last index needs an empty cell at source
depth 9. The exact four instructions between the bonus rolls preserve shallow
cells from the first roll. Thus, if pre-first-bonus source cells 9 and 10 are
both nonempty, successful modeled execution requires first index at least 9
and last index at least 10. The generated second-round initialization is now
checked to put a fixed nonce and empty dummy above 150 nonempty dummy bytes
over any earlier stack that fits the resource limits. A generic list-roll
theorem shows that seven selections confined to those 150 bytes, in any order,
leave the needed two nonempty cells. The seven-block byte-model theorem below
now establishes that pool-only signed-selection premise for every successful
generated byte run. A further checked full-program theorem carries those
cells through the exact bonus prefix and NULLDUMMY-enforcing suffix: the
decoded first bonus roll depth is in 9–152, and the second in 10–152.
This does not identify the bonus bytes as dummy signatures. Refining byte
execution and signature outcomes to Core remains open.
For the first signed selection of that second round, Lean now identifies the
lookup source for every capped nonnegative index: 0 and 1 reach 9-byte dummy
signatures, 2–151 reach one of the 150 20-byte commitments, and 152 reaches
the previous round's Boolean CHECKMULTISIG result. In the stated post-ADD
stack shape, the exact generated preimage roll and HASH160 comparison reject
the low 0–1 and capped-152 cases for any 20-byte-output hash function. The
shallow depths reachable from negative raw values contain only a short retained
ScriptNum, a 55-byte nonce, an empty cell, or 9-byte dummies, so those paths
also fail the modeled comparison. A successful-run bridge derives the stack
shape from *every* successful full generated byte-model run: it inverts the
previous round's CHECKMULTISIG result, all 302 second-round pushes, the fixed
586-roll, and the MIN/ADD/ROLL and hash-comparison sequence. Consequently, the
first final-round signed raw index must parse as `2+i` for some `i<150`, and
the generated commitment at `i` equals the HASH160 of the actual opening.
This holds for arbitrary initial byte stacks and supplied signature outcomes.
The seven-block composition below extends the original-position and opening
conclusion to every final-round signed selection in the byte model.

Lean also checks the literal 13-opcode blocks, including each fixed raw-index
pair, for all seven final-round signed selections. For any block number `k`,
if its input has the stated current gathered/dummy/commitment pool shape and
original-index alignment, *successful execution of that block* forces the raw
index to parse as `2+k+j` for a current pool position `j`, matches the actual
opening's HASH160 to that pool commitment, and removes the matching dummy and
commitment. The theorem preserves pool shape and alignment for the next block;
it identifies the raw source at earlier tail offset 283 and the opening source
at tail-after-raw offset `291-k`. It includes negative and nonminimal raw
ScriptNum encodings in its successful-execution analysis. A checked induction
now establishes the input invariant at each successive block, records its
actual opening and original commitment position, and proves the seven
positions distinct. The full-program theorem starts from any initial byte
stack and supplied signature outcomes; it inverts the preceding CHECKMULTISIG
and all 302 initialization pushes before applying that induction. It proves
that every successful 880-opcode generated *byte-model* run consumes seven
openings matching seven distinct original second-round commitments. This is
not yet a Core consensus theorem: scriptSig execution, signature validity,
FindAndDelete/sighash behavior, bonus selections, and final signature roles
still need their corresponding source and refinement arguments. The checked
post-signed pool shape also exposes nonempty generated dummy bytes at source
depths 9 and 10 immediately before the bonus prefix. The bonus theorem carries
those bytes through the fixed deep roll and cap to establish both lower
bounds. It also proves the two upper bounds from the generated `OP_MIN` caps.
The next local reached-roll theorem identifies the first bonus source within
that range. Depths 9–151 select a surviving 9-byte generated dummy; capped
depth 152 selects the first surviving 20-byte HORS commitment, with no access
to the arbitrary earlier tail. The theorem also identifies the selected byte
on top after the actual modeled roll. This makes the commitment-as-signature
setup exception explicit. A second reached-roll theorem now tracks the actual
second selected byte through the intervening fixed roll and cap. If the first
bonus takes a dummy, second depths 10–151 take remaining dummies and depth
152 takes the first surviving commitment. If the first bonus takes that
commitment, every second depth 10–152 takes a dummy. Thus the local pool
geometry permits a commitment in at most one bonus slot. A checked full-run
theorem now reaches and records both post-bonus states from any initial byte
stack and supplied signature outcomes, proves the index intervals, and gives
these exact source equations for the moved top bytes. This still does not
prove Core accepts the bytes as signatures: scriptSig execution, FindAndDelete,
sighash, ECDSA validation, and the DER-shaped setup event remain to be
connected to the byte model.

The final byte-model composition carries that provenance through the late
puzzle and key-roll suffix to the actual pre-CHECKMULTISIG state. Its ten
signature-source slots are, in order: the second bonus byte, the first bonus
byte, seven gathered generated dummy bytes, and the fixed nonce byte. The
following NULLDUMMY slot is empty. The same theorem retains the seven
distinct final-round HORS opening matches and both bonus source branches for
an arbitrary initial byte stack. It identifies the sole possible bonus
commitment as an original second-round HORS position absent from those seven
opening matches; either overshoot places that same commitment in a specified
final signature slot. These are byte-model source identities with
supplied signature outcomes, not Bitcoin Core ECDSA-validity results.
The checked conditional syntax theorem says that if both reached final bonus
signature slots satisfy a supplied signature-syntax predicate, and no
generated second-round HORS commitment satisfies it, both bonus depths are
strictly below 152. Its syntax premise must still be derived from Core's
actual parser and `CHECKMULTISIG`; the model's supplied Boolean outcome alone
does not imply it. The no-commitment premise is the setup exception to bound
under a stated hash distribution.
For this final-round bonus exception alone, the checked measure union bound
uses 150 second-round commitments: if each has actual parser-syntax marginal
at most `390405/2^65`, the probability that any is syntax-valid is at most
`150·390405/2^65`. The marginal and exact Core parser/count correspondence
remain external. This term does not bound the other extraction or puzzle gaps.
The Core-shaped matching-loop composition sharpens the syntax premise: if the
reached final ten-signature/ten-key scan succeeds under a pair verifier whose
success implies `sigSyntax`, then each bonus signature slot satisfies that
predicate. The checked theorem combines this with the unopened-commitment
origin to exclude bonus overshoots under the no-commitment condition. Matching
the pair verifier and scan result to actual Core execution remains open.
The exception is now also stated constructively: under the same matched-scan
premise, if either bonus depth reaches the commitment boundary, Lean identifies
an original HORS position absent from the seven computed signed openings whose
generated commitment passes `sigSyntax`. With strict DER syntax, this gives
an explicit dummy-bonus-or-unopened-DER-commitment disjunction. It is a
deterministic result for the literal generated byte model. The parameterized
byte-model version below now covers arbitrary 20-byte commitment values and
nonce bytes; the Core acceptance implication remains unproved.
The underlying aligned-pool lemma is now parameterized by an arbitrary
commitment map. When a dynamic setup is represented as one shared sampled
twenty-byte-output function `R` applied to sources selected independently of
`R`, the same local overshoot branch implies a hit in that setup's DER target.
Lean's finite-function count bounds the probability of **any** of 150 such
hits by `150·12/256^6`, without treating the outputs as independent. An
arbitrary bad event covered by this hit event inherits the count. The required
universal builder-to-model correspondence, compiled-Core scan refinement,
and the assumed setup distribution are still premises; this setup term is
not a bound on unauthorized spending.
`QSB/DynamicFinalInit.lean` now models the actual second-round data-push block
with arbitrary commitment and nonce bytes. Lean proves its successful stack
effect, 150-position initial alignment, paired-erasure preservation, and
equality with the literal block when specialized to the disposable fixture.
Three disposable executions of the pinned builder confirm that the commitment
pushes reverse the original indices, the second-round dummy signatures are
identical across two setups, and the suffix after instruction 749 is
byte-identical even when the final nonce signature is 20 bytes
(`evidence/dynamic-final-data.json`). The Lean byte-model signed and bonus
transitions below now go beyond that finite evidence. Universal
builder-to-model correspondence remains unproved; this evidence does not
establish Core acceptance or a spend bound.
The local dynamic signed-source theorem now classifies any reached, bounded
20-byte comparison under explicit aligned-pool and retained-width premises.
Its source is a current commitment at a known original position, except that
a 20-byte final nonce signature may itself be selected and match the HASH160
output. This now follows from a successful generated five-opcode comparison,
conditional on its reached dynamic post-ADD stack and roll cap. The literal
55-byte nonce excludes that branch; an arbitrary setup
cannot inherit this exclusion. In an isolated bare `CHECKSIG` experiment,
pinned Core 27.2 accepted a 20-byte strict-DER `SIGHASH_ALL` signature with a
message-specific recovered key and rejected both a wrong key and an altered
ALL-signed output (`evidence/nonce20-core.json`). This confirms that Core
signature validity alone does not remove the source exception. No matching
HASH160 opening or QSB-lock spend was produced. The comparison-prefix nonce
case is excluded by the now-checked *complete signed-block* theorem below;
the bare signature probe alone could not establish that exclusion.
The first comparison is now derived from one successful parameterized prefix
run, beginning with arbitrary nonce/commitment data pushes above a prior-round
result and adversarial tail. The fixed raw roll fetches tail cell 283; the
actual capped MIN/ADD depth and comparison yield a nonce hit or an
original-position commitment opening. Lean checks that this prefix is the
first 314 instructions of the literal final round. The model now carries that
run through the following dummy roll: the comparison preserves the retained
raw bytes, so a successful final roll parses them nonnegative. The earlier
comparison depth is therefore at least 145 in all seven generated signed
rounds. Every shallow cell at that depth is a nine-byte dummy, regardless of
nonce width, forcing any 20-byte match to be a current commitment. The first
complete dynamic block, including its data pushes, is checked as the first
315 literal final-round instructions and yields an original-position HORS
opening. `QSB/DynamicSignedTransition.lean` now proves the exact next stack
and paired pool erasures for each generated block with arbitrary nonce and
commitment bytes. `QSB/DynamicSignedChain.lean` composes all seven blocks:
from the parameterized data pushes through the signed suffix, every successful
byte-model run yields seven distinct original-position openings and an aligned
residual pool, with the same executable raw-index/opening extractors used by
the literal proof. Specialization to the fixture is exactly the first 393
instructions of the literal final round. `QSB/DynamicBonusFirst.lean`,
`DynamicBonusSecond.lean`, `DynamicBonusTrace.lean`, and
`DynamicBonusChain.lean` carry the same aligned pool through both reached
bonus draws and the late-puzzle stack rearrangement. For every successful
parameterized byte-model suffix, the first bonus depth is 9–152, the second
10–152, and the final multisignature source slots contain the two selected
bonus bytes, seven gathered dummy signatures, the arbitrary nonce, and the
empty dummy in exact order. A capped bonus draw selects the first surviving
commitment at an original position outside the seven openings.
`QSB/DynamicBonusDER.accepted_dynamic_bonus_der_alternative` adds an explicit
matched ten-pair verifier whose successful pair checks imply strict DER
syntax. Under that premise, a successful parameterized run either keeps both
bonus draws in the dummy pool or exhibits an unopened original commitment
whose bytes pass DER syntax. This is a deterministic setup exception, not a
quantum probability bound. Universal builder-to-model correspondence,
compiled-Core acceptance and final checker refinement, transaction-level
extraction, and the joint quantum-oracle bound remain open.
`QSB/DynamicBonusIndices.matched_dynamic_nine_positions` discharges the
good-setup branch: if no second-round commitment is DER-shaped, the seven
signed openings and two reached bonus dummy signatures occupy nine distinct
original positions. `QSB/DynamicBonusSetup.good_setup_nine_positions` states
this pointwise for an entire sampled twenty-byte-output setup function,
allowing the modeled witness to depend on that function. Its companion
`bad_der_setup_count` proves that the excluded setup fraction is at most
`150·12/256^6` when that function is uniform and independent of the material
selecting its 150 inputs. `QSB/DynamicBonusProbability.lean` converts the
finite count to the same bound for the uniform probability measure on a
nonempty finite setup space. This is a setup-event guarantee under a modeled
matched scan; it is not an unauthorized-spend or quantum-query bound.

`QSB/DynamicSerializedRound.serialized_final_round_core_decodes` now gives a
byte-to-opcode bridge for arbitrary 20-byte second-round commitments and a
nonce shorter than 76 bytes. It serializes the 302 varying data pushes with
the canonical push-prefix model, appends the fixed generated suffix, and
proves that the separate Core-shaped GetOp parser decodes precisely the
parameterized final-round program. A fourth disposable execution of the
pinned Python builder inserts a deliberately DER-shaped, non-HORS commitment
and checks the exact final-segment bytes, including a 20-byte nonce. This is
finite builder corroboration, not a universal theorem about the Python source
or compiled Core. `QSB/DynamicSourceGate.nine_positions_of_source_eval` also
discharges the abstract matched-scan/DER-sound premises when the separate
source-shaped `finalTenEval` succeeds at the reached stack; its checker and
the compiled-Core-to-evaluator link are still unproved.
`QSB/DynamicWholeSource.accepted_whole_good_setup_nine_positions` now starts
from any initial byte stack and any preceding opcode program whose last
instruction is the first `CHECKMULTISIG`. The modeled first multisignature
leaves `[]` or `[1]`, so the earlier non-20-byte prior-result premise follows
from the run. On a good setup, a successful parameterized final round and
successful source-shaped `finalTenEval` then give seven actual opening/hash
equations and nine distinct original positions. The seven opening pairs are
the result of executable `extractTrace`, computed from the modeled first-round
post-check stack rather than selected existentially. Lean also proves that this
full-program form specializes to the literal 880-op fixture. This removes a
starting-stack restriction in the source-shaped model; it does not prove that
every Python-built lock has that program or that consensus acceptance implies
the modeled run and evaluator result.
`QSB/DynamicWireSource.full_wire_decodes` extends the parser bridge to the
whole serialized script: any well-formed earlier opcode chunks decoding to a
stated prior program, followed by the first `CHECKMULTISIG` and parameterized
final segment, parse to exactly the full program above. Its companion
`accepted_wire_good_setup_nine_positions` applies the nine-position theorem
to a successful source-shaped run of those parsed opcodes, with the final
evaluator checking the same full wire bytes. The explicit prior-chunk contract
has not been proved for every Python builder execution, and the premise is a
Lean source-shaped run rather than compiled Core's consensus result.
`QSB/DynamicCoreStructural.accepted_structural_wire_good_setup_nine_positions`
uses one bottom-first Core-shaped structural run of that parsed full program.
The existing source-to-byte simulation supplies its byte-model execution, and
the final ten-pair evaluator is applied to the pre-CHECKMULTISIG stack reached
by the same structural run. The resulting seven opening pairs are still
computed by `extractTrace`. This removes a separate byte-run premise from
that source-level statement. The structural run still takes signature-scan
Booleans as inputs, and the evaluator still delegates actual sighash/ECDSA
verification to a supplied checker. No compiled-Core acceptance implication
follows.
`QSB/DynamicFullSerialized.lean` now constructs the entire 880-chunk Lean
wire lock from arbitrary 20-byte commitment pools in both rounds and arbitrary
short pin/nonce pushes. Lean proves that the full Core-shaped parser model
recovers its intended opcode program, that strict-DER source syntax supplies
the short-push conditions, and that its first 446 chunks specialize to the
literal fixture. This discharges the earlier arbitrary-prior-chunk contract
for the **Lean serialization** and feeds its full wire bytes to the structural
nine-position extraction theorem. The expanded pinned AST audit checks the pin
argument's only data use and all three signature arguments' call sites. Four
disposable full-lock builder runs match the parameterized chunk fixture,
including empty and 75-byte pushes. These are source audit and finite
differential evidence, not a formal theorem about every Python execution or
compiled Core.
`QSB/DynamicCheckedCertificate.search` now tries both legal first-round
`CHECKMULTISIG` results for that parameterized lock. A returned certificate
contains a truthy structural run, checks the six signature-opcode positions,
four reached source-shaped `CHECKSIGVERIFY` results, the actual first-round
source scan against its Boolean, and the final ten-pair source scan at the
same reached pre-check stack. Lean proves that such a certificate yields the
seven-opening, nine-position result on a good setup. The certificate's key
parser and ECDSA/sighash verifier are supplied functions, and neither the
certificate nor a Core-accepted transaction is known to imply the other.
The pinned Python source audit in `analysis/audit_builder_parametric.py`
checks that `_emit_round` reads commitment, dummy-signature and nonce byte
values only as three `push_data` arguments; its later stack-depth calculations
use token labels, while `push_data` branches on length alone. This supports
value independence of the emitted suffix for fixed Config A parameters and
short pushes. The audit is tied to the exact source hash and disposable
builder outputs. It is not a formal Python-semantics theorem equating every
builder output to the Lean serialization or a Core consensus refinement.
`QSB/DynamicSetupReduction.unauthorized_measure_bound_uniform_setup_key_cases`
now composes that setup probability with the transaction-game reduction:
`Pr[Unauthorized] ≤ εfresh + εdistinct + εsame + 150·12/256^6`.
Its type explicitly requires a uniform setup marginal, owner-honest release,
fresh-opening and distinct/same-key puzzle event bounds for the *same* terminal
distribution, and source/transaction/Core extraction on every good setup.
Those last three event bounds and the good-setup extraction implication are
not established by this work. The displayed inequality is therefore a
conditional proof interface, not a numerical security claim for deployed QSB.
`QSB/JointOracleReduction.lean` gives a second, world-indexed interface:
each sample carries one `H` and one `R`, setup secret bytes, commitments
defined as `R(H(secret))`, adaptive releases, and an attacker output. Its
strict-DER target is fixed by the source-shaped predicate. Lean proves
`Pr[Unauthorized] ≤ εjoint + εgap`, or
`Pr[Unauthorized] ≤ εjoint + 150·12/256^6` if every good setup has actual
transaction/Core extraction and the stated product-uniform setup marginal.
Here `εjoint` bounds the *union* of the fresh-opening and pin/final puzzle
events in that one sampled world. No coherent-query algorithm, shared query
budget theorem, nontrivial `εjoint`, or Core extraction is supplied; the
source ECDSA relations remain external. This interface avoids accidentally
treating sampled oracle functions as constants of the terminal measure.
`QSB/OracleDependentSelection.lean` isolates a further limit of that
interface. Across four equally likely Boolean functions, a fixed input hits
the target in two worlds, but an input selected after seeing one oracle value
hits in three, even though the observed bit is uniform. The world-indexed
selector has no query accounting; a causal implementation must charge the
observation as a query or model it as correlated advice. This finite result
does not refute the conditional reduction, attack QSB, or establish a quantum
bound. It rules out substituting a fixed-input random-function density for
the still-unknown adaptive `εjoint`.
The same file proves a second four-world warning: every fixed key has a
singleton digest target, yet a fixed key hits in two worlds and a key chosen
from a disclosed oracle digest hits in all four. The per-key target count
alone therefore supplies no adaptive probability bound. This world-indexed
toy does not model ECDSA recovery or charge the disclosure's query cost.
`QSB/DERSyntax.lean` now gives an executable source-shaped translation of
[Core 27.2's strict signature-encoding checks](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp). Lean proves that any accepted
20-byte value has positive R/S byte lengths summing to 13 and the required
six-byte header/length shape. `QSB/CoreDEREncoding.lean` separately lists
Core's 14 checks in early-return order with bitwise sign tests. Lean proves
the two source-shaped predicates agree on every byte list and that accepted
checks read only in-bounds bytes. The crafted overshoot signature is accepted by
this predicate. A proof that this Lean predicate equals Core's compiled parser
for every byte string, and a count of its entire 20-byte accepted set, remain
open; the earlier `390405/2^65` figure is still conditional on that count
correspondence.
`QSB/DERIntegerCount.lean` now proves the integer-field part of that count:
the one-byte case has 128 encodings, and every longer length has exactly the
positive-first-byte and sign-protected-leading-zero counts used by
`derIntegerCount`. It also derives the corresponding R/S prefix constraints
from `DERSyntax.valid`. The remaining step is a dependent length-pair
decomposition of complete 20-byte signatures; the exact target-set count is
still unproved.
Core's `CheckSignatureEncoding` permits the empty signature as an invalid-check
placeholder under the pinned `VERIFY_ALL` flags. Lean now models that encoding
gate separately and proves that it equals strict DER on nonempty inputs.
A 73-case isolated `CHECKSIG; DROP; TRUE` differential corpus matched the
pinned Core library on all cases, including the empty exception and malformed
20-byte boundaries. The `DROP` removes the ECDSA result, isolating the parser
gate for this test. `QSB/FinalBonusIndices.lean` now states a more precise
conditional interface: successful pair verification must imply both nonempty
signature bytes and acceptance by that gate before it concludes strict DER and
the nine-position shape. The corpus does not prove the interface for Core's
full final multisignature scan or all possible signature bytes.
Nine further isolated `FindAndDelete` cases each pass with a public key
recovered for the app's opcode-boundary scriptCode and fail with a key
recovered for a deliberately wrong scriptCode. They cover separated and
adjacent repeated canonical
signature pushes, an embedded byte pattern, noncanonical `PUSHDATA1/2/4`, the
literal 56-byte pinning signature, and two copies of one valid 20-byte
`SIGHASH_ALL` signature push. The last case is an isolated analogue of a
nonce/commitment alias, not a valid QSB HORS commitment.
An additional six-pair pinned-Core differential uses valid 32-byte DER
signatures with trailing sighash bytes `0x01`, `0x03`, and `0xff`: a lock
without a push-32 opcode accepts the key recovered for its unchanged
scriptCode, while an exact-push control accepts the key recovered after
deletion; every wrong-code control fails. For the exact QSB fixture,
Lean proves no opcode chunk starts with push-32, so the source-shaped legacy
FindAndDelete loop leaves the whole lock unchanged for SHA256 of **either**
reached hash-puzzle key in the same arbitrary-stack byte-model run. The final
key is also traced to its later CHECKMULTISIG slot. This removes a
witness-dependent scriptCode choice from both hash puzzles. A new
source-shaped BASE `CHECKSIGVERIFY` theorem exposes the actual hash-type byte,
DER gate, key-validity result, and external ECDSA/sighash checker call for
both reached puzzle sites and the fixed pinning check. In particular, the
hash-derived signatures are **not** assumed to end in `SIGHASH_ALL`.
The successful-checker premises, actual Core-to-Lean equivalence, and
transaction sighash/ECDSA refinement remain open.
`QSB/ScriptSigSighash.lean` proves a more precise ALL distinction. Erasing
original scriptSig bytes leaves the source-shaped preimage unchanged when the
selected input and scriptCode are held fixed. For a valid selected input, the
same preimage is injective in the supplied scriptCode. Two complete candidate
final-signature lists, differing in one generated dummy and sharing the other
eight dummies and fixed nonce, delete different chunks from the literal lock
and therefore produce different ALL preimages with all transaction fields
held fixed. These are source-model preimages, not a claim that their SHA256d
digests differ or that both candidate lists are reachable in accepted QSB
spends. The witness-dependent scriptCode remains part of the joint hash event.
`QSB/FinalSubsetInjective.lean` strengthens the literal-lock result from one
example to every list of generated dummy positions. Source-shaped deletion
removes complete opcode chunks, and reparsing the residual bytes recovers those
chunks. Each generated dummy has one unique serialized push, so two selected
lists yield the same final scriptCode **if and only if** they contain the same
positions, regardless of order or repeated entries. For a valid selected
input and fixed transaction fields, their source-shaped ALL preimages have
exactly those same equality classes. This does not prove that every subset is
reachable by an accepted witness, that actual Core computes these bytes for
every witness, or that SHA256d outputs are distinct. The number of possible
preimages must not be read as independent quantum search trials.
`QSB/ParameterizedFindAndDelete.lean` extends whole-chunk deletion to the
parameterized Config A serializer: with 20-byte commitments and short fixed
pin/nonce signatures, its 880 chunks are simple direct pushes or one-byte
opcodes. Arbitrary reached signature bytes, including long and malformed
ones, delete exactly the matching original chunks in the source-shaped loop.
`QSB/ParameterizedFinalSubset.lean` then proves that candidate final lists
have equal scriptCodes and, at a fixed valid selected input, equal source ALL
preimages exactly when their selected dummy-position sets agree. It also
covers transactions equal after original scriptSig erasure. The fixed final
nonce's `SIGHASH_ALL` byte prevents aliasing with generated `SIGHASH_SINGLE`
dummies. These results do not determine Core-accepted subsets or refine
compiled Core, and preimage inequality does not rule out SHA256d collisions.
The pin/final separation is now checked too. On the literal lock, the final
nonce push survives pin-signature deletion but is removed from every final
candidate scriptCode, even for an empty or repeated index list. On a
parameterized lock, the same result holds whenever the pin and final nonce
have different serialized push patterns. For any valid selected source input,
the two modeled ALL preimage byte strings are therefore distinct. Applying
this to the actual fixed signature checks also requires their `0x01` hash-type
flags and the Core-to-source sighash refinement. This is a prerequisite for
reasoning about two hash evaluations, not a claim
that their SHA256d values or recovered keys differ: one key can still verify
two different fixed signatures/messages under the recovery equations. The
universal compiled-Core and shared-query quantum arguments remain open.
The separation also survives adversarial changes to the modeled transaction:
`ScriptSigSighash.sourceAllPreimage_identifies_selected_scriptCode` proves
that equal valid ALL preimage bytes with a nonempty selected scriptCode force
both the selected input index and selected scriptCode to agree, even when the
two transactions have different original scriptSigs. The literal and
parameterized pin/final theorems compose this with their distinct scriptCodes,
so no pin/final preimage alias exists across any two valid source transactions
or selected inputs under the stated push inequality. The pin code is proved
nonempty by the surviving final nonce push. These are equality facts about
source byte strings, not independence of adaptive quantum oracle evaluations
or a Core-to-Lean verifier theorem.
`ParameterizedFinalSubset.nonce_alias_counterexample` checks the ALL-flag
boundary of the arbitrary-list theorem: if the final nonce bytes instead
equal one generated `SIGHASH_SINGLE` dummy, selecting that dummy or omitting
it gives the same source scriptCode despite different selected-position sets.
This is outside the stated final-nonce premise and is not an accepted QSB
spend.
`QSB/ParameterizedAliasDeletion.lean` checks a different alias boundary:
when a 20-byte final nonce equals a second-round commitment, the full
parameterized source wire contains at least two copies of that canonical
push, and final FindAndDelete removes all copies. If the nonce passes the
source DER predicate, the commitment necessarily belongs to the explicit
bad-setup event. This does not construct a HORS preimage for that commitment.
`QSB/ParameterizedReachedSubsetSighash.lean` now takes the actual ten
signature bytes at a parameterized checked-source search's reached final
stack. Under the good-setup no-DER-commitment premise, it constructs nine
distinct selected dummy indices and proves that the reached final ALL
preimages of two successful source searches have the same equality classes,
for supplied valid transactions equal after scriptSig erasure. Both searches
share the lock and hash functions; their external key/ECDSA checkers may
differ. The source transaction fields are not yet derived from each search's
raw input, and actual Core acceptance and SHA256d collision resistance remain
unproved.
`QSB/ParameterizedRawReachedSubsetSighash.lean` composes that theorem with
two raw-byte source attempts. Each attempt's transaction fields, selected
input and initial lock stack come from its own successful strict Lean parse
and supplied arbitrary-scriptSig evaluator; the supplied lock bytes pass an
exact wire equality check. If both source runs accept, select the same input,
and their decoded fields agree after scriptSig erasure, their reached final
source ALL preimages agree exactly when their nine selected dummy sets agree.
This removes independent transaction-field choice inside the raw source
model. The parser, scriptSig evaluator, checker and execution are still not
proved equivalent to compiled Bitcoin Core.
On a good setup, a further raw-source theorem obtains the final signature
slots from a successful checked search on one parsed raw attempt. Its reached
final ALL preimage cannot equal any valid pin ALL preimage, even for another
source transaction or selected input. This removes a caller-chosen final
subset from the cross-role byte separation. It still assumes the validated
parameterized lock, a nonaliasing pin/final push pair, and the source checker;
compiled-Core acceptance and the one-budget quantum bound remain open.
Lean also proves that each valid source-shaped ALL preimage is longer than a
32-byte SHA-256 output. Combining that length fact with the reached pin/final
preimage separation gives an exact shared-H input classification: either the
two first SHA-256 outputs collide, or the four inputs used by the two SHA256d
calls are pairwise distinct. The raw-source theorem obtains its final
scriptCode from the checked reached stack. This is a statement about which
oracle inputs can alias, not independence of adaptive calls or a quantum
query-success bound.
`QSB/ReachedSubsetSighash.lean` now applies that classification to the ten
signature bytes in two reached final CHECKMULTISIG stacks. A successful full
literal byte-model run with an explicit nonempty, DER-sound successful
ten-pair scan yields nine distinct original dummy positions. For any two such
runs and the same valid source-shaped transaction fields and selected input,
the reached final ALL preimages are equal exactly when the position sets are
equal. The theorem derives the deletion list from reached slots; it still
assumes the modeled scan and does not refine compiled Core or show that
distinct preimages have distinct SHA256d digests.
The stronger `checked_runs_reached_all_preimage_classification` theorem takes
two truthy checked-source interpreter runs. That interpreter computes the
final multisignature result from its reached stack, so this theorem no longer
supplies a successful scan separately. It remains conditional on the model's
external key parser and ECDSA/transaction checker and does not turn compiled
Core acceptance into a checked run.
`literal_validated_run_eq_static` checks that supplied bytes matching the
literal wire fixture decode to the exact 880-opcode checked-source program.
The resulting `validated_runs_reached_all_preimage_classification` theorem
starts from two truthy validated-byte source runs, with no separate opcode,
signature-list, or scan-result premise. It does not establish that those
supplied bytes are a real spent output or that compiled Core accepts the
same transactions.
`validated_runs_erased_scriptSig_classification` now permits two distinct
source transactions whose original scriptSig bytes differ, provided erasing
those scripts makes all other transaction fields equal. Under the same
selected input and valid source wire fields, equality of their reached final
ALL preimages is still equivalent to equality of the selected dummy-position
sets. The arbitrary scriptSig evaluator and compiled-Core refinement remain
outside the theorem. A fourth pinned-Core case in
`evidence/full-subset-switch-core.json` prepends non-push `OP_1 OP_DROP` to an
accepted puzzle-relaxed witness; it remains accepted with the same recovered
keys, and the app's ALL digest is unchanged. The experiment is finite and
does not execute the three real puzzle checks.
The full-lock differential now repeats the subset switch with a second
public disposable parameter set: both HORS commitment pools and all three
fixed signatures differ from the literal fixture. The app's repeated
FindAndDelete bytes equal an independent whole-original-chunk filter for
both selections in both parameter sets. Pinned Core accepts each second-set
selection with newly recovered keys, accepts an `OP_1 OP_DROP` scriptSig
prefix with the same keys, and rejects reuse of the first selection's final
nonce key for the second. All eight cases are synthetic, unfunded and
puzzle-relaxed; this is finite corroboration, not universal Core refinement.
The final ten-pair source model now also exposes each reached signature's
actual last-byte hash type and external ECDSA/sighash checker call on the
same selected scriptCode. This is conditional on successful source-shaped
final evaluation; the checker and compiled-Core bridge remain external.
Lean now additionally composes source-shaped bottom-first structural steps
for every generated opcode, including arbitrary-count multisignature parsing,
the false first-round result, NULLDUMMY cleanup, and CHECKSIGVERIFY stack
pops. A successful source-shaped run of the whole 880-opcode lock from any
post-scriptSig stack projects to the byte-model run. This narrows the
remaining bridge to the compiled interpreter, actual signature outcomes,
transaction sighashes, and consensus context. The isolated ten-signature
Core differential also passed three nonminimal-count positives and four
count/dummy negatives, plus three subset-switch controls, for 25 cases total.
This corroborates the selected source behavior but does not compute the final
QSB scriptCode for arbitrary Core-accepted witnesses. `CORE-FINAL-MATCH.md` records the exact
remaining Core-to-Lean final-checker bridge.
An additional isolated 10-of-10 multisignature experiment places all 151
fixture signature pushes in a nonexecuted branch. Core accepts keys recovered
against the shared scriptCode after ten selected deletions, and rejects 12
wrong-code controls, including one that retains each selected push in turn.
The two-input, two-output transaction exercises in-range `SIGHASH_SINGLE`
as well as `SIGHASH_ALL`. A `CHECKMULTISIG; DROP; TRUE` variant accepts an empty
first-scanned signature but rejects a malformed nonempty one, consistent with
the source encoding gate. Two nine-dummy selections sharing the fixed final
nonce give distinct scriptCodes and ALL digests; Core accepts a separately
recovered key list for each and rejects the second list when only its nonce
key is replaced with the first list's nonce key. The adapter does not expose
the error code. These 25 cases are native evidence for selected source
behavior, not full-lock acceptance or a proof of arbitrary-witness refinement.
The new source-shaped final evaluator checks the reached ten-count cells,
strict-DER gate, nonempty signatures, key-skip scan, shared ten-signature
FindAndDelete scriptCode, and NULLDUMMY. Lean now composes its successful
result with an arbitrary-stack full byte-model run to obtain seven HORS
opening matches, two distinct bonus positions, the selected scriptCode, and
ten DER-valid successful pairs at Core-shaped stack addresses. The evaluator's
success is an explicit premise; actual Core acceptance has not yet been
refined to it, and the checker remains an abstract ECDSA predicate.
The full disposable 9,923-byte lock now has a separate two-output,
puzzle-relaxed Core check: the shared-scriptCode witness accepts, while ten
one-key controls retaining one reached final signature push in scriptCode
all reject. The first seven native cases remain byte-identical. This tests
the actual generated final multisignature path, but the three puzzle
   `CHECKSIGVERIFY` sites are still replaced by `OP_2DROP` and arbitrary
   accepted witnesses are not covered.
   Core's failed `CHECKMULTISIG` scan has an additional source-control-flow
   detail: once remaining signatures outnumber remaining keys, it returns
   false before checking the next signature's DER encoding. The Lean scan was
   corrected to make that early exit. A pinned isolated Core probe accepts a
   malformed lower signature when the first failed comparison makes it
   unreachable and the false result is dropped; it rejects both the undropped
   false result and a malformed signature that is actually attempted. This
   does not itself establish the first-round checker/outcome bridge for a
   Core-accepted full-lock spend. The Lean source certificate below now
   states that bridge explicitly at the reached stack.
An isolated fixed-signature `SIGHASH_ALL` probe now records the complete
source-shaped preimages and SHA256d digests for ten committed-field changes
and two `scriptSig`-only controls. In all ten changed-preimage cases, pinned
Core rejected the old key and accepted a freshly recovered key; the two
unchanged-preimage controls retained the old key. Lean proves a fixed-context
ordered-output preimage distinction under an explicit injective wire-encoding
premise and maps any same-key verification of the new message to an admissible
ECDSA recovery target. A second Lean theorem permits other fields and
scriptCode to vary: the full source-shaped ALL preimage parser now recovers
version, every prepared input, ordered outputs, locktime, and the ALL word
for every valid encoded transaction. Input-script preparation preserves each
ordered prevout and sequence; equal prepared preimages therefore imply equal
committed transaction fields despite different original scriptSigs or
scriptCodes. In one fixed ledger context they imply equal owner-authorization
projections, including resolved previous outputs and fee. A 139-byte Lean
fixture equals the pinned app's baseline preimage. Concrete CompactSize and
nonnegative eight-byte amount encodings are included. Lean-checked branch
vectors match the pinned app, and two 253-boundary transactions passed Core.
The CompactSize decoder now rejects overlong encodings, and Lean proves that
every successful parse consumes exactly the shortest encoding of its value.
A separate nine-case pinned Core 27.2 probe accepts a canonical synthetic
transaction and returns deserialization error `3` for six overlong-length
variants, an all-empty SegWit witness record, and an unknown SegWit flag.
This matches the rejection branches in Core v27.2's
[CompactSize reader](https://github.com/bitcoin/bitcoin/blob/v27.2/src/serialize.h)
and [transaction reader](https://github.com/bitcoin/bitcoin/blob/v27.2/src/primitives/transaction.h).
Core's resource cap, full parser, and contextual consensus checks remain
outside the Lean model.
The source-shaped model now also performs BASE/ALL input-script preparation;
a second fixture starts with different scriptSig bytes and checks that
replacement and blanking yield the same 139-byte preimage. This remains a
model of the source branch, not a C++ equivalence theorem.
The source-shaped Lean legacy serializer now covers every 32-bit hash-type
branch, including NONE, SINGLE, ANYONECANPAY, and the out-of-range SINGLE
constant-message exception. It proves that type `0x01` equals the earlier
ALL model; five exact byte fixtures tie the Lean code to an independent
Python serializer. Core 27.2's published corpus supplies 500 varied cases:
467 ALL-like, 16 NONE, 17 in-range SINGLE, and 229 ANYONECANPAY. Every
expected digest matches independent preimage hashing and the pinned app;
210 scripts contain simple opcode-boundary `OP_CODESEPARATOR` removal. The
corpus has neither literal `0x01` nor out-of-range SINGLE, which have separate
native probes. These are finite differential checks.
The C++ serializer and reached-scriptCode equivalence remain open.
[The source contract](CORE-SIGHASH-ALL.md) explains why this is not universal
same-key rejection or an arbitrary-witness QSB theorem:
the full parser/refinement bridge and quantum hash-target bound remain open.
An independent conservative count now avoids that exact-count premise for the
Lean predicate: among all `256^20` twenty-byte strings, at most
`12·256^14` can satisfy the required header, R-length, S-tag, and S-length
conditions. The injection removes all six constrained byte positions, even
though two move with the R length. Thus its density is at most `12/256^6`.
The checked finite random-function union theorem combines this target bound
with 150 setup-selected inputs when
the entire uniform R160 function is independent of the material selecting
those inputs, giving at most `150·12/256^6` for this *syntax setup event*.
This deliberately loose estimate is not a quantum-query or unauthorized-spend
bound, and connecting the Lean predicate to Core's compiled parser remains
unproved.
For the one literal disposable lock in `ByteLayout.program`, Lean checks that
none of its 150 second-round commitments passes this DER predicate. It follows
conditionally that a successful final matching scan with a DER-sound pair
verifier cannot take either bonus commitment branch for that lock. This does
not prove the same fact for all generated vaults, equate the predicate or scan
with the compiled Core verifier, or supply a spend-probability bound.
`QSB/FinalBonusIndices.lean` then extracts the two actual bonus signature
bytes from that same accepted byte-model run. Each equals a generated dummy
at a surviving original HORS position. The surviving-position permutation
proves that these two positions differ from each other and from all seven
signed opening positions, so their union has exactly nine positions. The
seven other reached signature slots are the generated dummies at those seven
traced positions in reverse draw order; the theorem also identifies the fixed
nonce slot and empty NULLDUMMY cell. This
full-run statement still assumes the successful DER-sound ten-pair scan;
the byte interpreter's supplied final signature Boolean does not establish
that premise, and Core refinement remains open.
Lean also checks that the 150 literal generated dummy signatures are pairwise
distinct as byte strings. The nine selected original positions therefore
yield nine distinct dummy-signature bytes. This does not exclude another
occurrence of one of those byte patterns elsewhere in the locking script by
itself. A deterministic source-fixture inventory separately checks that each
of the 150 final dummy signatures and the fixed final nonce appears as exactly
one opcode-boundary push in this literal lock and that the app deletes that
one push. This remains executable evidence rather than a Lean/Core theorem
about the sequential ten-signature scriptCode. `QSB/ScriptCodeSelection.lean`
proves that an opcode-level filter of the selected signature pushes is
independent of their order and equals successive single-signature filters. Its
`Op.push` model does not retain the push opcode encoding, so the byte-faithful
Core link is still open.
The fixture inventory now checks that all 151 selected patterns are direct
pushes and that every boundary prefix match is a complete opcode. Whole-opcode
deletion therefore preserves the segmentation used by Core's source algorithm
for any subset of these literal patterns. The app's implementation also gives
identical bytes for 35 selected ten-signature sets under three deletion
orders. Lean now parses the generated 9,923 serialized bytes into precisely
880 chunks, decodes each chunk to the byte-machine instruction, checks all
151 selected final signature patterns are distinct direct pushes appearing
exactly once, and proves the chosen chunk-filter scriptCode is independent of
index order. It also proves that a selected pattern matching at any generated
opcode boundary consumes exactly that complete chunk, for any following
bytes. The generator checks the script hash externally.
`QSB/FindAndDelete.lean` now models repeated byte-pattern deletion at opcode
boundaries followed by parsing the next opcode. For every ordered list of
selected final dummy signatures and the fixed nonce, Lean proves that this
loop returns the exact serialized-chunk filter of the literal lock, including
repeated patterns. The proof uses checked simple-opcode and complete-match
properties; the literal script also has no `OP_CODESEPARATOR` opcode.
`QSB/CoreGetOp.lean` adds a separate source-shaped model of Core v27.2's
opcode iterator advance. Lean proves it equals the existing parser for every
byte string, including malformed or truncated PUSHDATA1/2/4 inputs. The two
source-shaped sequential deletion loops consequently agree for every byte
script and ordered pattern list. Applied to the literal lock, this gives the
same final scriptCode for any chosen final-signature index list and the
one-push pinning result. These are
source-level model theorems, not compiled-C++ refinement or a full arbitrary
scriptSig and transaction extractor. The source fixture confirms that
the pinning push occurs only once at byte offset zero; the eighth isolated
Core case corroborates deletion for those signature bytes.
`QSB/CoreFindAndDelete.lean` further models Core's delayed copy of each parsed
opcode and its return of the original script when no pattern matched. Lean
proves its byte output agrees with the prior deletion model for every script
and pattern, then obtains the same literal final and pin scriptCodes. This
narrows the source-control-flow gap but does not turn the Lean model into a
compiled-Core acceptance theorem.

`QSB/PinningScriptCode.lean` identifies the actual nonce and puzzle key bytes
reached by both pinning checks from any successful initial byte-model stack.
Under an explicit successful-verifier bridge, the SHA256 of that nonce key is
strict DER. `QSB/SourceWitness.lean` composes this with the final-round
witness theorem: both puzzle hits and the seven final openings arise from the
same modeled execution. It still lacks Core verifier/sighash equivalence,
dynamic-setup parameterization, and a joint quantum hash bound.
`QSB/CoreStructuralEquiv.lean` proves exact two-way agreement between the
bottom-first Core-shaped structural interpreter and the top-first byte
interpreter for every modeled opcode and run, including structural
`CHECKMULTISIG` transitions with supplied true or false scan outcomes,
NULLDUMMY, opcode cost, and the 1,000-cell post-op guard.
The result holds for arbitrary starting byte stacks, hash functions, and
supplied signature outcomes. It also lifts the lower-stack suffix frame and
overflow results to the source-shaped structural run. Both interpreters still
take signature-scan outcomes as inputs, so this does not refine compiled Core
or its DER, FindAndDelete, sighash, key parsing, and ECDSA checks.
`QSB/CoreFinalTruth.lean` models Core's final `CastToBool` test and proves that
it equals the byte model's `[1]` truth test after any successful modeled
program ending in `CHECKMULTISIG`, including the exact 880-opcode lock. The
final structural step pushes only `[1]` or an empty cell, so arbitrary
scriptSig-supplied noncanonical truthy bytes cannot occupy that top slot.
The theorem converts a source-shaped final `CastToBool` success into the
`finalTruth` premise of the extraction results. Pinned Core 27.2 accepts or
rejects seven isolated final-stack byte cases as this model predicts,
including negative zero. Actual compiled-Core-to-model execution and
signature-checker results remain separate obligations.
`QSB/DynamicCoreFinalTruth.lean` proves that every parameterized Config A
Lean lock, for arbitrary commitment and fixed-signature bytes, ends in the
same final `CHECKMULTISIG`. Its source-shaped structural run therefore has
the same Core-shaped `CastToBool` and byte-model truth value. A source-shaped
accepted run with all reached site checks is returned by the two-candidate
certificate search, including a false first-round result. This is still a
Lean-to-Lean connection; it does not derive the run or site checks from
compiled Core.
`QSB/CoreSourceExtraction.lean` lifts this composition to a truthy full
source-shaped structural run. Its executable `necessarySignatureChecks`
examines the reached source stacks at all six signature opcodes: the fixed pin,
the early, first-round, and late SHA256-derived puzzle checks, and both
multisignatures. An earlier version omitted the first-round
`CHECKSIGVERIFY` at instruction 423, leaving its supplied `true` unchecked;
`necessary_checks_first_puzzle` now exposes that source-shaped checker result.
The generic first-round scanner reads actual count and pair slots and deletes
all reached signatures before matching. It must return a Boolean equal to
the structural run's supplied outcome; a false result is permitted, while a
fatal attempted encoding failure fails the certificate. Under those source-model
premises, Lean extracts the same seven-plus-two final witness and exposes the
fixed pin and final nonce's actual `SIGHASH_ALL` calls on their source-shaped
scriptCodes. The earlier multisignature may still return false. This is not
compiled Core acceptance: deriving the source checker outcomes from the
compiled interpreter, exact transaction sighashes, ECDSA, and the
source-to-Core relation remain external.
`QSB/CoreCheckedStep.lean` now offers a separate executable source-shaped
opcode run whose signature results are computed from each reached stack.
CHECKSIGVERIFY uses the complete Core push pattern for FindAndDelete before
the DER gate; CHECKMULTISIG computes the common deleted scriptCode and
ordered scan before source-shaped cleanup. Lean proves that any successful
literal run records six signature-site results, that each successful checked
CHECKSIGVERIFY exposes its actual hash-type and verifier call, and that a
computed true final ten-pair result exposes all ten source-addressed strict-DER
pairs. The generic true scan itself forces all ten signatures to be nonempty
strict DER and short enough for direct pushes; no short-push premise is needed
at this boundary. Lean also proves that every successful checked run replays
in the older structural interpreter using exactly its computed signature
results, then projects to the byte machine.
For the literal lock, any successful checked run therefore yields the seven
distinct final HORS opening positions and their commitment equations. If its
final CastToBool is true, the actual checked final scan is true and all ten
reached signature/key pairs pass the source-shaped checker against one common
deleted scriptCode. For this one literal fixture, where no generated final
commitment is strict DER, the run then identifies nine distinct second-round
positions: seven signed openings and two bonus dummies. The executable
`FinalRoundWitness.extractMatchedWitness` consequently returns a modeled
round witness with valid opening equations and its key read from the actual
reached final stack. This removes caller-chosen signature Booleans from this
*new source model*. `QSB/CoreCheckedRunCertificate.lean` now proves that a
truthy checked run also satisfies all six reached checks in the existing
certificate. Its records have the exact shape
`[true, true, true, firstRound, true, true]`; the actual first-round scan
selects that Boolean, and the two-candidate certificate search finds a
result. The prior source extraction consequently yields the pinning key,
strict-DER hashes of the pin and final keys, and the two fixed
`SIGHASH_ALL` calls on their reached scriptCodes without separately assuming
the six checker results. The converse simulation and compiled-Core refinement
remain unproved. The key parser, ECDSA, transaction digest, and hash functions
remain external inputs. A small checked-run theorem
also demonstrates a computed false non-VERIFY multisignature followed by a
truthy push; it is an isolated model case, not a QSB spend.
`QSB/CoreCheckedDynamic.lean` lifts the checked-run final extraction to
parameterized Lean Config A locks. From a truthy checker-derived run, it proves
that the computed final scan is true; a byte-level ten/ten count and NULLDUMMY
layout then turns that scan into the source-shaped ten-pair evaluator on the
same reached stack. If all second-round commitments are 20 bytes, the run
either exposes an explicitly DER-shaped setup commitment or computes seven
matching openings and nine distinct second-round positions. This no longer
requires a separately postulated final-scan result for the parameterized Lean
run. The same run now computes the exact six-site record pattern, discharges
the four reached CHECKSIGVERIFY and first multisignature source checks, and
enters the parameterized two-candidate certificate search. With the shared
`H`/`R` transaction checker, `QSB/CoreCheckedJointTransaction.lean` then
derives the two strict-DER key puzzles and fixed `SIGHASH_ALL` calls; on a good
setup it derives the seven `R(H(opening))` equations and final ALL call. The
arbitrary transaction-to-checked-run implication, builder equivalence, real
checker semantics, and joint quantum bound remain unproved.
`QSB/CoreCheckedWire.lean` now accepts supplied locking-script bytes rather
than silently regenerating them for execution. Its executable `matchesWire`
check proves exact equality with a claimed parameterized Lean lock. When that
check succeeds, the source-shaped `GetOp` parser recovers the opcode program
for 20-byte commitments and short fixed signatures. A truthy checked run of
those supplied bytes yields both DER key hits and fixed ALL calls; on a good
setup it also yields seven reached `R(H(opening))` equations and nine distinct
positions. This per-script equality check can replace a universal Python
builder theorem for an individually validated lock, but no theorem yet takes
the spent output bytes from a Core-accepted transaction into this check or
refines Core execution and ECDSA/key parsing. The pinned builder source-shape
audit and four disposable full-lock byte comparisons remain finite evidence.
Lean also checks that the literal disposable 880-chunk fixture passes the
new exact-byte validator; this fixture is not a production spent output.
`QSB/DynamicRoundWitness.lean` now computes a parameterized `RoundWitness`
from a returned good-setup source certificate. It reads seven opening pairs
from the executable trace, decodes two bonus indices from reached dummy
signature bytes, and reads the final key from the reached tenth key slot.
Lean proves the nine-position shape, opening equations, and strict-DER hit for
that key. The supplied-wire theorem combines this same computed witness with
both pin and final strict-DER hits and both fixed ALL verifier calls under one
shared `H`/`R` world; the two keys may coincide. This is a modeled source-run
necessity with external hash, key, and ECDSA functions. It does not extract a
witness from arbitrary Core-accepted transaction bytes or prove a joint
quantum-query probability bound.
`QSB/DynamicSourceGame.lean` packages the supplied-wire checked run as a
source-model attempt containing transaction fields, selected input, supplied
lock bytes, and already-decoded initial stack cells. Its deterministic game
extractor returns the reached pin key and final-round witness. The pin and
round relations retain the actual fixed ALL verifier calls; the round relation
identifies the nine positions selected by that source run. Under the explicit
good-setup and lock-shape premises, Lean proves `SourceExtraction` and the
fresh-opening-or-two-puzzle disjunction for this *checked source model*. That
removes its internal extraction gap, not the game gap for consensus-accepted
raw transactions. A Core-to-source refinement, real key/ECDSA semantics, and
one-budget quantum event bound remain unproved.
Without the good-setup premise, the same modeled unauthorized event implies
the joint failure event or an explicitly DER-shaped second-round commitment.
With the explicit setup equality `commitment_i = R(H(secret_i))`, Lean states
the fresh-opening event against those same-world commitments. The extractor
has no explicit secret-map argument, but the supplied checker functions are
not proved independent of those secrets or charged to a query budget. No
small probability is silently assigned to either branch.
`QSB/DynamicRawSource.lean` now starts the same *source-model* extractor from
submitted raw transaction bytes, selected input number, and separately
supplied spent-output script bytes. The Lean transaction-envelope parser
recovers legacy or SegWit fields and selects that input's actual scriptSig;
an explicit evaluator supplies its post-scriptSig stack. Lean proves the raw
bytes re-encode to the parsed envelope, the selected input exists, and the
owner-facing projection equals the parsed transaction's projection. For a
good-setup truthy checked-source run, the raw-byte extractor discharges the
game's extraction interface. Without the good-setup premise, the modeled
unauthorized event again implies a joint failure or DER-shaped commitment;
with setup equality, the opening target is `R(H(secret_i))` in the same world.
The scriptSig evaluator, Core transaction parsing and lock execution, and
the link from a real spent output to the supplied script remain unproved.
`QSB/LedgerBoundRawSource.lean` tightens the source frontend: the attacker
submits only raw transaction bytes and a selected input, while a fixed ledger
function supplies the script for the selected target prevout. Lean checks the
parsed prevout equals that target and proves that source acceptance forces
the ledger's script to equal the validated QSB wire; a different target
script cannot pass. The same ledger function supplies the authorization
projection; the game also checks the parsed selected prevout as its target-
spend predicate. The good-setup source extraction and joint-event reduction
carry through. This removes an independently caller-chosen spent script from
that *source-model* game. It does not establish UTXO existence, unspent
status, other Core transaction checks, or Core-to-Lean execution refinement.
`QSB/RawPublicHistoryEvent.lean` now carries the public-key-aware history
classification through this ledger-bound raw frontend. On a good setup and
an owner-forbidden source projection, one successful prepared attempt has the
seven reached HORS equations, nine positions, and both reached ALL calls in
the same H/R world, classified against the same supplied public-key set and
approved-call list. The proof is conditional on source-model acceptance and
the `ECDSATargets` verifier contract; actual consensus acceptance, public
transcript completeness, and a causal shared-query bound are still missing.
`QSB/RawReachedSubsetSighash.lean` now compares two raw submissions that both
pass this literal checked-source acceptance predicate. It obtains each
transaction and initial stack from that submission's successful `prepare`
call, so the stacks are tied to the parsed scriptSig through the supplied
evaluator. If the selected input is the same and the decoded transactions
agree after erasing original scriptSigs, their reached final source-shaped
ALL preimages are equal exactly when their nine selected dummy-position sets
are equal. Each run has its own transaction-dependent external ECDSA checker;
the H/R functions are shared. This is still a source-model implication,
not a statement about compiled Core or SHA256d digest injectivity.
The pinned local Core adapter's three early-exit cases were rerun and matched
`evidence/multisig-early-exit.json` byte for byte. A later 25-case isolated
ten-signature rerun used the same hash-pinned Core adapter and library in the
recorded arm64 Ubuntu image. All 22 earlier case records stayed unchanged;
the three added subset-switch outcomes appear in
`evidence/ten-signature-find-and-delete.json`. These finite
probes corroborate the relevant source behavior but do not refine every
compiled-Core execution to the Lean interpreter.
`QSB/CoreCheckedCertificate.lean` searches the two possible first-round
multisignature outcomes and verifies the full reached source-model certificate
before returning a result. It additionally recomputes the reached first-round
source scan and requires it to equal the candidate flag. Lean proves that any
returned flag equals both this scan and the structural run's reached outcome
cursor. The finite search is sound and complete relative to candidates with
this direct-match condition, then derives the fixed `SIGHASH_ALL` obligations
from a returned certificate. The search returns a Boolean and final source
state; the parameterized good-setup `RoundWitness` is now computed from that
source-model result, but there is no parser of adversarial transaction bytes.
Hash functions, key
parsing, and ECDSA remain explicit inputs; this search is not a compiled-Core
acceptance proof or a quantum query bound.
The first version of this generic scanner reused the final-round
`directPushPattern`, which only serializes signatures shorter than 76 bytes.
That was unsound for arbitrary first-round witnesses: Core constructs
`CScript() << vchSig` with PUSHDATA1 at 76–255 bytes and PUSHDATA2 at
256–520 bytes, and it deletes even signatures the pair loop will skip.
`QSB/CorePushSerialize.lean` now models those prefixes; the first-round
scanner uses it for every reached signature. A Lean theorem shows the old
pattern differs at 76 bytes. Five isolated pinned-Core cases at the 75, 76,
255, 256, and 520-byte boundaries confirm that the skipped signature's push
is deleted before the earlier checker call. `scanAtStack_finalTen` now states
its short-signature premise explicitly when relating the generic scanner to
the older final-round evaluator. The premise follows for any successful
ten-of-ten final scan from strict DER, as checked by
`finalTenEval_success_generic_scan`. This repairs the source certificate but
does not establish a compiled-Core refinement for arbitrary witnesses.
The separate `QSB/CorePushFindAndDelete.lean` theorem proves that, for any
simple-chunk script and sufficient fuel, canonical push patterns match only
complete original opcode chunks. Repeated deletion therefore filters those
chunks, even with long, duplicate, malformed, or subsequently skipped
signatures. Its 880-step literal and parameterized Config A specializations
discharge the source-shaped deletion fuel obligation. Scripts with other
encoded chunk shapes need a separate rigidity proof.
The analogous generic `CHECKSIGVERIFY` shortcut is now checked separately:
`CoreChecksigEval.evalBaseVerifyAll_eq_core` proves its returned `Option Bool`
equals a version using full Core push serialization for every input. Under
the pinned DERSIG gate, long signatures are fatal regardless of their
intermediate deletion pattern; any nonfatal signature is short enough for
the direct form. This result does not apply to the first multisignature,
where a long signature can be skipped after affecting the shared scriptCode.
`QSB/JointSourceChecks.lean` now instantiates these source checks with one
shared H256 function `H` and one R160 function `R`: the reached pin and final
fixed signatures verify against `H(H(sourceAllPreimage))`, and the seven
opening equations use `R(H(opening))`. The puzzle-signature lemma retains its
actual last-byte hash type and permits the out-of-range SINGLE constant
digest. This is a deterministic source-model connection, not a sampled joint
oracle game or a quantum query-success theorem; the ECDSA checker and Core
acceptance remain external.
`QSB/DynamicJointTransaction.lean` specializes the complete parameterized
checked-source certificate to a selected transaction input and that same
joint `H`/`R` pair. For each of the ten reached final signatures, it exposes
the actual DER bytes, key bytes, last-byte sighash flag, and successful
external ECDSA call on a digest computed against one common Core-shaped
FindAndDelete scriptCode. Every digest is either `H(H(preimage))` for the
selected legacy hash type or the raw out-of-range SINGLE constant; a valid
input index is necessary. This is conditional on finding the source
certificate with the supplied key parser and ECDSA predicate. It is not a
compiled-Core acceptance implication or a quantum success bound.
The good-setup extractor now retains the *reached signature cells*, rather
than only nine selected commitment positions. With no DER-shaped second-round
commitment, the first nine actual source-addressed final signatures are
generated `0x03` dummies. The transaction theorem then proves that whenever
the selected input exists and its index is at least the output count, each of
their nine external ECDSA calls receives the raw `01 00…00` SINGLE-bug digest.
The complementary checked branch covers an input inside the output list:
each of those calls instead receives `H(H(SINGLE preimage))` using the same
reached final scriptCode. Thus the source result classifies both transaction
layouts without relying on the app's two-input policy. Lean also proves all
nine dummy pairs use one common digest in either branch; their messages cannot
be treated as nine independent hash targets.
This applies to the three-input/two-output layout observed in the pinned Core
experiment, but remains a source-model implication. It does not remove the
fixed nonce's separate ALL commitment or prove that a real arbitrary witness
produces the checked certificate.
`QSB/DynamicCheckedCertificate.search_complete` proves the other direction
of the executable certificate boundary: if either first-round Boolean has a
truthy structural run satisfying the reached source checks, the two-candidate
search returns a certificate. This removes an internal search-completeness
obligation, while the implication from an arbitrary Core-accepted transaction
to those source conditions remains unproved.
The same certificate fixes the tenth final signature to the lock-pushed
second-round nonce for every successful modeled run with 20-byte second-round
commitments. The source-addressed stack theorem transfers this exact byte
identity through reversal. When the parameterized nonce ends in `0x01`, its
reached ECDSA call is therefore on `H(H(sourceAllPreimage))` with the common
final FindAndDelete scriptCode. The arbitrary-lock `0x01` condition is an
explicit premise; the source checker and compiled-Core bridge remain open.
The late puzzle's checked source stack consumes `H(key)` for that *same*
tenth final key, forcing a strict-DER hash output. The parameterized good-setup
theorem combines this with seven actual `R(H(opening))` commitment equations
and the nonce's `H(H(ALL preimage))` ECDSA call in one certificate. This is a
deterministic joint event over shared functions, with an adversary-dependent
key and scriptCode. A separate checked parameterized pin-side theorem now
identifies the early puzzle's signature as `H(pinKey)` for the reached pin key
and forces strict DER. One source certificate therefore supplies both
DER-shaped key hashes and both fixed signatures' `H(H(ALL preimage))` ECDSA
calls, allowing the pin and final keys to coincide. It does not establish a
quantum query bound; Core/builder refinement and an adaptive disclosure model
remain open. The nonce ECDSA call by itself is not a fresh hash target because a
public key can be recovered for a chosen digest.
`QSB/DynamicDisclosureEvent.lean` now makes the adaptive-disclosure case split
explicit for any terminal set of freely disclosed key bytes. In one checked
source certificate on an owner-forbidden projection, either a reached pin or
final key outside that set has strict-DER `H(key)`, or both keys are in the set
and both fixed `SIGHASH_ALL` checks verify on preimages outside *every* valid
owner-approved release preimage. This includes equal pin/final keys and keeps
one shared `H`; it does not assume the disclosed set is independent of the
oracle. Generic source-shaped FindAndDelete length lemmas and the checked
9,981-byte Lean wire limit establish that both reached scriptCodes fit the
ALL serializer's length domain. This deterministic split has no QROM
probability estimate or compiled-Core acceptance implication.
The known-key branch now has a more precise finite-target interface:
`QSB/DynamicDisclosureEvent.ECDSATargets` explicitly requires every true
external ECDSA check to land in a wire-digest set of at most eight values for
that fixed signature and key. Under this still-unproved Core-verifier bridge,
Lean derives two `H(H(ALL preimage))` target memberships from the same
certificate; their target-set union has at most 16 values even if the two
keys coincide. `RecoveryCandidates.secp_digestTargets_card_le_eight` proves
the abstract curve-count component under its stated premises. Neither that
count nor the source reduction bounds a coherent-query search on the shared H
with oracle-dependent disclosed keys.
An approved disclosure of a *matching fixed signature and key* supplies one
oracle-dependent digest already inside that target set. The new
`QSB/DynamicRetarget.lean` theorem shows that an owner-forbidden verification
with the same signature/key must use a distinct ALL preimage and either
collide with the approved `H(H(preimage))` digest or hit one of at most seven
other wire-digest targets. This prevents treating the whole eight-target set
as fixed independently of the oracle. It is conditional on a recorded
matching approved call and the still-external ECDSA target contract; it is
not a quantum collision or search bound. A further checked lemma turns the
equal-digest case into an explicit collision for that *same* H: if the first
hashes agree, the distinct ALL preimages collide; otherwise their distinct
first hashes collide under the second H application.
The history event now retains precisely those reached preimages in its
collision branch. Its former branch, `∃ a ≠ b, H(a) = H(b)` with no relation
to the attempted call, was unsuitable for a quantum success bound: Lean proves
that this unrestricted event holds for every total 32-byte-output H on all
byte strings, even before any query. A finite checked example also has an
unrelated global collision while the two chosen preimages do not collide.
The corrected witnessed event is equivalent to equality of the two reached
SHA256d digests. It still needs a causal query/transcript theorem; this
repair is not a QROM bound.
`QSB/DynamicRetarget.search_pin_final_history_cases` now classifies both
reached source checks against a list of approved fixed-signature/key ALL
calls. If no record uses the key, the branch retains a DER-shaped verifying
call on a forbidden preimage. If the key was released under another signature
but no exact pair matches, the attempted digest lies in an at-most-eight
target set. A matching pair yields the reached collision or at-most-seven
alternative-target event. A key absent from the approved-call list may still
have been queried or exposed elsewhere, so that branch is not yet an
oracle-fresh event. The list must contain all relevant approvals to represent
a complete disclosure transcript. The result is deterministic; causal
transcript modeling and a shared-query quantum bound are still missing.
`history_event_public_case` refines the classification using a supplied set
of publicly disclosed keys. An unmatched pair whose key is in that set is
charged to the at-most-eight digest-target branch even if the approved-call
list has no record for it. Only a key absent from both sets remains in the
DER-key branch. Completeness of the supplied disclosure set is external, and
absence still does not establish an unqueried or independent oracle input.
The checked `search_good_setup_joint_public_history_event` applies this
classification to both reached calls in one good-setup certificate while
retaining the seven opening equations, nine distinct positions, and shared
H/R functions. Its supplied public-key set is not a modeled query transcript.
On a good setup, `search_good_setup_joint_history_event` places those two
checks and their three cases alongside the seven reached `R(H(opening))`
equations and two distinct
bonus positions from the same source certificate and the same H and R.
The same parameterized certificate also yields the reached first pinning
CHECKSIGVERIFY call. Its signature bytes are provably the lock-pushed pin
signature for any initial stack on which the modeled prefix succeeds. Strict
DER makes the reached signature's direct-push deletion equal Core's full
push serialization. If the pin signature's last byte is `0x01`, the checked
source ECDSA call uses `H(H(sourceAllPreimage))` for the selected transaction
input and reached pin scriptCode. The key remains a scriptSig-supplied byte
string, and the ALL premise is explicit because the parameterized lock
accepts arbitrary pin bytes.
For the complete parameterized Lean serialization with two 150-entry pools of
20-byte commitments and three fixed signatures shorter than 76 bytes,
`QSB/DynamicScriptLimits.lean` proves an exact length of
`9756 + pin.length + nonce0.length + nonce1.length`. Its maximum, 9,981 bytes,
is below the 10,000-byte script-size guard in the pinned Core 27.2 interpreter.
Isolated pinned-Core bare scripts with bounded pushes and drops accept at
9,981 and 10,000 bytes and reject at 10,001 bytes
(`evidence/bare-script-boundary.json`).
This discharges that size check for the Lean serialization under those width
premises; universal Python-builder equality and compiled-Core acceptance
refinement are still separate obligations.
`QSB/FinalScriptCode.lean` connects that loop to the ten signature bytes
actually reached by the final modeled CHECKMULTISIG. Under an accepted full
byte-model run and the explicit nonempty, encoding-sound successful-scan
premises, their order is second bonus, first bonus, seven gathered dummies in
reverse draw order, then the fixed nonce. Permuting that list to the nine
original dummy positions plus nonce leaves the resulting scriptCode unchanged.
For two distinct final dummy-position sets, a pinned Core 27.2 differential
on the 880-opcode puzzle-relaxed lock now accepts separately recovered key
lists and rejects the second list when its final nonce key is retained from
the first. The in-range final ALL digests differ. This is a synthetic,
unfunded two-output test with three puzzle checks changed to `OP_2DROP`;
see `evidence/full-subset-switch-core.json`. It does not establish a real-lock
spend, a universal Core extraction theorem, or a probability bound.
The theorem also identifies `SIGHASH_SINGLE` on each of the nine reached
dummy signatures and the fixed `SIGHASH_ALL` nonce in slot ten.
The successful equal-count scan verifies every corresponding reached key pair;
in particular, the fixed nonce verifies against the last reached key.
This removes a freely chosen signature-list premise from the modeled
scriptCode result; it does not show that Core supplies the scan premise or
that ECDSA verifies against the real transaction sighashes.
Lean also checks the literal signature flags: all 150 final dummy signatures
end in `SIGHASH_SINGLE` (`0x03`), while the fixed final nonce ends in
`SIGHASH_ALL` (`0x01`). The dummy signatures use the constant SINGLE message
only for transactions whose input index is beyond the output list; this is
not guaranteed for arbitrary transactions. The ALL nonce message depends on
the selected scriptCode and transaction fields. A sound final-round extractor
must distinguish these per-signature messages.
The pinned Core adapter verifies an isolated fixed SINGLE signature with a
newly recovered key when a second output makes the sighash in range; the
out-of-range recovery key fails on that same transaction. A further disposable
test runs the complete two-round stack path with the three puzzle checks
relaxed to `OP_2DROP`: one output accepts with the SINGLE-bug recovery keys;
two outputs reject those old dummy keys and accept keys recovered for the
in-range message; changing the selected second output's value then rejects.
The same accepted two-output witness remains accepted with either a non-push
scriptSig prefix computing an extra bottom-stack value or an extra 520-byte
bottom-stack element.
The pinned adapter now also accepts 1, 64, 256, and 385 additional empty
bottom-stack cells before that witness, but rejects 386. The original seven
native outcomes and transaction hashes remain unchanged. For the parallel
disposable byte-model witness, `QSB/BytePrefixCapacity.lean` proves that
peak recording preserves the ordinary run and checks a base peak of 615:
385 extras reach exactly 1,000 cells. A separate diagnostic, proved to
erase to the ordinary run, identifies the 386-cell case as a 1,001-cell
overflow after modeled zero-based opcode index 754. The
`QSB/ByteStackFrame.lean` proof generalizes the modeled boundary to arbitrary
bottom-stack byte values: with at most 385 extra cells the fixture remains
truthy with peak `615 + tail.length` and final height `569 + tail.length`;
with 386 or more cells the ordinary byte run rejects. A per-opcode frame
property, including `OP_ROLL` and `CHECKMULTISIG`, yields both sides of this
capacity threshold for any successful nonempty modeled base run. This does
not establish the behavior of arbitrary tails in compiled Core. The
two boundary scriptSigs are 1,534 and 1,535 bytes, well below Core's
10,000-byte script limit. The adapter reports only acceptance, so the
precise native failure opcode is
not observed. These are finite tests with three puzzle sites relaxed, not
universal arbitrary-scriptSig extraction from compiled Core.
Three additional pinned Core cases corroborate the modeled content-independent
boundary: 385 deterministic nonempty 20-byte cells pass, 386 fail, and 384
empty cells plus one 520-byte cell pass. All three scriptSigs are below the
10,000-byte limit; the adapter still exposes only acceptance.

Changing only the unselected first output and rederiving the fixed ALL keys
accepts while reusing the in-range SINGLE dummy keys. Lean proves the
corresponding source-shaped preimage and joint-digest invariance for any
unselected output changes that retain the selected output. All 15
HORS comparisons, pinning, and both CHECKMULTISIGs remain active. This is a
two-input component experiment, not acceptance of the unmodified QSB lock
or an unauthorized spend.
A test-only variable-input adapter calling the same pinned Core library agrees
with the original wrapper on one accepted and one rejected two-input control.
The complete puzzle-relaxed lock then accepts two three-input, two-output
layouts: QSB at input 1 uses in-range SINGLE, while QSB at input 2 uses the
out-of-range constant SINGLE digest despite the two outputs. At input 2 a
change to both output values rejects with the old fixed ALL keys, then accepts
with those keys rederived while the original final-round nine dummy keys stay.
The recorded per-input Core results and message scalars make the distinction
reproducible.
The official Core 27.2 macOS ARM consensus library independently reran all
28 disposable cases when Docker Desktop was unavailable. The archive and
original dylib hashes were pinned; macOS required ad hoc re-signing of the
temporary extracted library, and the loaded hash is recorded. All 28 case
records match the prior Linux report byte-for-byte in
`evidence/full-two-outputs-core-parity.json`. This strengthens finite native
differential evidence but does not expose interpreter stacks or prove
arbitrary-witness Core refinement.
The same pinned adapter also accepts these two QSB input positions inside a
SegWit-serialized transaction whose separate input spends a valid P2WSH
`OP_DROP OP_TRUE` script. Changing only the consumed P2WSH witness datum
preserves acceptance with the same QSB unlocking script; replacing its witness
script with the wrong bytes rejects input 0 while the bare QSB input still
verifies. Thus a raw-byte
extractor cannot assume the app's legacy-only transaction serialization.
`QSB/SegwitTxWire.lean` now round-trips a canonical marker/flag `00 01`
envelope with at least one nonempty witness stack and proves that changing only those stacks
leaves its *source-shaped* legacy digest unchanged. It does not prove full
Core transaction parsing or that the unmodified QSB lock can be spent.
`QSB/LegacyTxWire.lean` separately round-trips canonical raw legacy
serialization, without the hash-type suffix of the ALL preimage. For the
same transaction fields, its raw envelope and the SegWit envelope yield the
same modeled legacy digest. A 167-byte fixture matches an app-built raw
transaction accepted in the pinned Core ALL-commitment probe. These facts
now have converse proofs: **any successful Lean parse** of either raw envelope
re-encodes exactly to the parsed transaction fields (and witness stacks for
SegWit) followed by the returned tail. The proof composes canonical
CompactSize, fixed-width fields, ordered inputs and outputs, and witness
stack parsers. It does not show that every Core-accepted byte string is parsed
by either Lean decoder, that the parsed fields satisfy transaction-consensus
validity, or that Core's actual signature checker matches the source model.
`QSB/TransactionEnvelopeWire.lean` now dispatches a complete raw transaction
on the first parsed input-vector count. For nonempty valid source fields, it
round-trips both the legacy form and the `00 01` SegWit form; every successful
strict parse has nonempty inputs and exactly re-encodes to its raw bytes. A
successful *modeled* legacy digest from those raw bytes is then either
`H(H(preimage))` under the same supplied `H` or the historical out-of-range
SINGLE constant. This is the source-model transaction-byte entry point for
the later joint event. Core v27.2's
[transaction reader](https://github.com/bitcoin/bitcoin/blob/v27.2/src/primitives/transaction.h)
uses the empty initial input vector as the witness-marker branch, while
[CheckTransaction](https://github.com/bitcoin/bitcoin/blob/v27.2/src/consensus/tx_check.cpp)
rejects an empty input vector. These source-code observations do not prove
compiled-Core parser equivalence, contextual transaction validity, or that
the QSB lock's actual checker calls use this modeled digest.
The distinction is concrete: `QSB/ConsensusValidityBoundary.lean` checks a
canonical two-input legacy envelope that the Lean parser accepts although
both inputs repeat the same prevout. Core v27.2
[CheckTransaction](https://github.com/bitcoin/bitcoin/blob/v27.2/src/consensus/tx_check.cpp)
rejects that transaction with `bad-txns-inputs-duplicate`. The pinned
[script API](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/bitcoinconsensus.cpp)
checks each of its two synthetic `OP_TRUE` inputs successfully, as recorded in
`evidence/consensus-validity-boundary-core.json`; that API does not call
`CheckTransaction`. The finite native result and source-code reading make
script-verifier acceptance an insufficient replacement for full transaction
acceptance, even when every input script passes. This is a validation-boundary
counterexample, not a QSB spend or a counterexample to a quantum bound.
`JointSourceChecks.legacyDigest_single_bug_ignores_outputs` and
`checker_single_bug_ignores_outputs` prove the corresponding source-shaped
invariance for any output replacement that leaves the selected input past
the last output. These tests do not solve the three real hash puzzles or prove
universal Core-to-Lean extraction.
`QSB/FinalRoundWitness.lean` maps the recorded opening pairs into the abstract
round-witness interface using an executable lookup. Lean checks the seven-plus-two
shape and the opening hash equalities for the constructed witness. The earlier
theorem permits an independently supplied key; a new full-run theorem instead
uses the actual last reached multisignature key. The generated late puzzle
segment proves that its CHECKSIGVERIFY signature is SHA256 of that same key.
Under explicit successful, encoding-sound predicates for the reached final
ten-pair scan and late puzzle check, the fixed final nonce verifies against
this key and its SHA256 is strict DER in the source-shaped Lean predicate.
An executable `extractMatchedWitness` now computes that modeled witness from
the signed prefix and final reached stack: it looks up the two bonus dummy
signatures among the 150 generated values and reads the last reached key.
Lean proves that the returned value equals the witness in the source-shaped
pin/final certificate, including the two-candidate certificate search and
the shared-hash-function theorem. This removes freely selected witness fields
at that modeled boundary. It does not establish Core checker equivalence,
the ECDSA nonce equation for the real legacy sighash, a transaction extractor,
or a quantum puzzle bound. For dynamic setups, DER-shaped commitments remain
an explicit exception to the dummy-only bonus argument.

Five pinned Core 27.2 cases corroborate this first final-round signed
boundary on a puzzle-relaxed complete lock: the canonical index 2 accepts,
while indices 0, 1, 152, and nonminimal `980000` reject. The native rejection
does not by itself identify the failing opcode or establish Core-to-Lean
refinement; the test keeps pinning, HORS comparisons, and both multisignature
checks real while relaxing the three hash-to-signature puzzle checks.

Eight further cases probe the second signed index on that same puzzle-relaxed
lock: canonical and nonminimal encodings of 3 accept; 0, 1, 2, -1, canonical
152, and nonminimal 152 reject. These are native complete-lock outcomes, not
an opcode-level diagnosis or a Core-to-Lean refinement proof. The default
first-index probe was rerun and reproduced its recorded evidence byte-for-byte.

A generated byte fixture also retains all push bytes in the 9,923-byte Config A
lock. Lean checks its 880 opcodes and the adjacency of all 15
`HASH160; EQUALVERIFY` comparisons. An intermediate byte interpreter proves
that any reached pair on an accepting modeled suffix compares an actual
opening's hash with the next stack item, for arbitrary hash functions, stack
tails and suffixes. An executable opening trace preserves the interpreter's
result; a successful run of the literal lock has exactly 15 matched records,
and Lean proves that dropping the first eight leaves exactly the seven records
executed by the generated final signed blocks at opcodes 749–839. This advances
local HORS extraction but does not by itself label those byte-trace records
with original pool indices or refine signature outcomes and transaction
acceptance to Bitcoin Core. Separately, `extractWholeFinal` now executes the
literal prefix and reads each subsequent raw ScriptNum and opening from the
reached stack. Lean proves it returns seven distinct original positions and
actual opening bytes for every successful full byte-model run, with each
opening hashing to its generated commitment. A second executable function
returns the ordered 143-position residual pool, and Lean proves selected plus
residual positions permute the original 150. These results need no assumption
that public commitment bytes are distinct. Its input is still a modeled stack
with supplied signature outcomes, not an adversarial transaction or Core
acceptance proof; equality with the independent byte-opening trace remains
unproved.
The trace also composes with any executable program prefix, so a future
provenance invariant can apply it at each of the 15 concrete comparison sites.

A disposable byte witness also completes all 880 modeled instructions and all
15 HORS comparisons with the expected 201-op and 569-cell final stack. It uses
a generated HASH160 lookup table and externally supplied signature results.
The byte fixture also confirms that the first-round multisignature Boolean
does not affect final modeled truth, while the final Boolean does. These are
model consistency checks, not a real Script acceptance or solved puzzles.

The game-level theorem has the exact form

    Pr[accepted unauthorized spend]
      <= ε(fresh opening on forbidden projection)
       + ε(two-puzzle search on forbidden projection)
       + ε(source-extraction gap).

The primitive events do not assume Script acceptance. The source-extraction
premise, when used, is explicit and unproved; the unconditional theorem retains
the gap. Lean proves that a constant-`none` extractor puts the entire bad event
in that gap. None of the three epsilon terms has a nontrivial QSB bound.
Lean also checks the refined bound with the two-puzzle term split into
distinct-key and same-key events:

    Pr[accepted unauthorized spend]
      <= εFresh + εDistinctKey + εSameKey + εExtractionGap.

The published two-distinct-input QROM result could address only the distinct
branch after its other game hypotheses are met. The same-key branch needs a
separate argument; no nontrivial bound is established for either branch.
In particular, a same-key replay is not limited to identical sighash digests.
For a fixed ECDSA signature and public key, opposite admissible recovery
points can yield two different verified message scalars. Lean proves the
finite-recovery-point group-element target-set algebra, and a pinned public
secp256k1 fixture verifies both messages for one signature and key. The fixture
supplies neither a SHA256d preimage nor an accepted QSB spend. A QROM argument
must bound hits to the full admissible message-target set; a collision-only
replay event is too narrow. The actual secp256k1 point count, Core digest
conversion and transaction refinement remain open.
Core 27.2 normalizes a high-S signature before calling libsecp256k1. Lean
proves that negating S swaps the corresponding recovery point with its
opposite; a pinned isolated Core check accepts a strict-DER high-S variant
under the same key and ALL digest. Thus an original-DER-S target set needs
both recovery-point signs. Lean proves target membership after normalization
under an explicit sign-closed admitted-point premise. This does not establish
that Core's parsed recovery points satisfy that premise or the full
Core-to-Lean verifier relation.
Lean also proves the numerical inequality `p < 2n` for the secp256k1 field
prime and subgroup order. Under an explicit at-most-two-points-per-x premise,
it bounds admissible recovery points and their message group-element targets
by four. Lean now derives that fiber bound for any collection of affine
points satisfying a field-valued curve equation and unique `(x,y)`
coordinates: two solutions of the same square equation differ by sign.
Proving that Core's admitted recovery points map injectively to such affine
secp256k1 coordinates, excluding infinity and invalid points, remains open.
Lean also proves `2^256 < 2n`: each message residue modulo the secp256k1
order has at most two unsigned 256-bit digest representatives. Combined with
the conditional four-recovery-point bound, a fixed signature/key has at most
eight possible wire digest targets. This is finite target accounting, not a
SHA256d quantum hit bound; the Core digest-to-residue bridge, point parser,
and oracle correlations remain unresolved.
`QSB/WireECDSATargets.lean` now turns that numeric count into actual 32-byte
target strings. Lean proves fixed-width byte/natural round trips and builds
the `ECDSATargets` contract from an explicit four-residue verifier contract;
an alternative constructor derives its four-residue count from the checked
recovery-point fiber theorem. The universal verifier-to-recovery relation and
the mapping of Core's digest bytes to `readBE` remain premises, not results.
Core 27.2 passes `hash.begin()` to libsecp256k1's scalar parser, whose pinned
4x64 implementation reads its input with big-endian 64-bit loads
([Core public-key verifier](https://github.com/bitcoin/bitcoin/blob/v27.2/src/pubkey.cpp#L267-L282),
[secp256k1 scalar parser](https://github.com/bitcoin/bitcoin/blob/v27.2/src/secp256k1/src/scalar_4x64_impl.h#L150-L161)).
The existing isolated native semantics fixture reproduced byte-for-byte in
this run; it is finite corroboration, not a universal Core refinement. Lean
also checks that Core's out-of-range SINGLE raw `uint256::ONE` buffer
(`01` followed by 31 zero bytes) denotes `2^248` under this byte order,
matching the pinned fixture's accepted recovery-key case.
`QSB/SighashBinding.lean` composes this count with the source-shaped ALL
serializer: an owner-forbidden semantic projection implies a distinct
prepared preimage from any approved release in the same fixed ledger
context. This includes changes to inputs, sequences, version, locktime, or
outputs. The explicit verification and reduction premises put its digest in
the at-most-eight-value target set. No Core acceptance or quantum probability
enters the theorem.
The pinned app's `ecdsa_recover` helper considers only x=`r`. A second public
algebraic fixture uses x=`r+n`: the app's ECDSA verifier accepts its signature
and key at scalar message zero, but neither helper parity reconstructs that
key. This shows why the helper's candidate count is not an adversary bound.
That earlier fixture has no SHA256d preimage. A separate disposable two-input
bare-`OP_CHECKSIG` transaction fixes `(r,s)=(2,1)` and one `SIGHASH_ALL`
preimage/digest. The pinned Core 27.2 adapter accepts four distinct compressed
public keys recovered from the two curve solutions at `x=r` and the two at
`x=r+n`; it rejects a wrong-key control. The app helper returns only the
two `x=r` keys. Lean checks four distinct `(x,y)` candidates and their
modular curve equations for this `r`, showing that the four-coordinate
count can be attained. This is finite isolated Core evidence, not a QSB
lock spend, universal Core-to-Lean ECDSA refinement, or quantum probability.

The closed DER-32 *syntax count expression* has density
`780555 / 2^65` (about `2^-45.426`), and the analogous DER-20 expression is
`390405 / 2^65` (about `2^-46.425`). Core accepted all 256 trailing sighash
bytes in isolated legacy signature tests. The exact count's equivalence to a
formal BIP66 parser remains open. Under the explicit premise that each of 300
commitment-encoding events has marginal probability at most `390405 / 2^65`,
Lean bounds the probability of *any* such event by
`300 * 390405 / 2^65`, without assuming independence. A new finite
random-function theorem establishes the required individual target densities
when the whole R160 function is uniform and independent of all setup material
used to select its inputs; its shared-function union bound permits collisions
among the 300 inputs. Equating the counted DER target with Core's exact parser
is still unproved. These are setup-syntax facts, not an extraction-gap or
spend bound, and they do not analyze adaptive quantum access to R160.

## Critical remaining proof obligations

1. Implement a byte-faithful extractor from every consensus-accepted
   arbitrary scriptSig and transaction. Prove the pinning and enforced final
   round relations, ScriptNum/index behavior, HORS checks, actual final
   signature roles, FindAndDelete, and transaction-field commitments. Either
   characterize and bound DER-shaped commitment/setup exceptions or weaken the
   extracted shape in a way that still supports a sound cryptographic target.
2. Prove a quantum query-success bound for the *joint* SHA-256/SHA256d/HASH160
   oracle game after adaptive honest disclosures. It must cover known good
   puzzle inputs, key reuse, equal pin/final keys, variable selected subsets,
   accepted key encodings, sighash collisions and other same-key ECDSA
   recovery targets, multiple vaults, and one shared query budget. Standalone
   unstructured-search or two-distinct-input results do not by themselves meet
   these hypotheses.
3. Refine the Lean projection and acceptance predicates to Core byte parsing,
   consensus and the chosen chain state. Distinguish consensus validity from
   default relay and miner inclusion; verify the deployed binary if a claim
   about deployment is later desired.

The most valuable next step is obligation 1. It determines the real
cryptographic failure event to which an applicable QROM theorem would need
to reduce. The current `ExtractionGap` cannot responsibly be assigned zero.

Reproduction commands and the pinned native-adapter provenance are in
`README.md`; experiment scopes and exact source-to-model mapping are in
`PROOF-STATUS.md`; primary sources and their applicability limits are in
`RESEARCH.md`.
