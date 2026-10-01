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
   control and five-byte rejection. Compiled Core interpreter refinement
   remains open.
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

## What Lean proves

The pinned Lean 4.30.0/mathlib build checks 798 theorem dependency lists with
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
deterministic result for the literal generated byte model; a dynamic lock
parameterization and Core acceptance implication remain unproved.
The underlying aligned-pool lemma is now parameterized by an arbitrary
commitment map. When a dynamic setup is represented as one shared sampled
twenty-byte-output function `R` applied to sources selected independently of
`R`, the same local overshoot branch implies a hit in that setup's DER target.
Lean's finite-function count bounds the probability of **any** of 150 such
hits by `150·12/256^6`, without treating the outputs as independent. An
arbitrary bad event covered by this hit event inherits the count. The required
dynamic-lock execution/alignment and compiled-Core scan bridge are still
premises, and this setup term is not a bound on unauthorized spending.
`QSB/DynamicFinalInit.lean` now models the actual second-round data-push block
with arbitrary commitment and nonce bytes. Lean proves its successful stack
effect, 150-position initial alignment, paired-erasure preservation, and
equality with the literal block when specialized to the disposable fixture.
Two disposable executions of the pinned builder independently confirm that
the commitment pushes reverse the original indices, the second-round dummy
signatures are identical across setups, and the suffix after instruction 749
is byte-identical (`evidence/dynamic-final-data.json`). The full dynamic
signed-loop invariant and universal builder-to-model correspondence are still
unproved; this evidence does not establish Core acceptance or a spend bound.
The local dynamic signed-source theorem now classifies any reached, bounded
20-byte comparison under explicit aligned-pool and retained-width premises.
Its source is a current commitment at a known original position, except that
a 20-byte final nonce signature may itself be selected and match the HASH160
output. The literal 55-byte nonce excludes that branch; an arbitrary setup
cannot inherit this exclusion. In an isolated bare `CHECKSIG` experiment,
pinned Core 27.2 accepted a 20-byte strict-DER `SIGHASH_ALL` signature with a
message-specific recovered key and rejected both a wrong key and an altered
ALL-signed output (`evidence/nonce20-core.json`). This confirms that Core
signature validity alone does not remove the source exception. No matching
HASH160 opening or QSB-lock spend was produced. A dynamic seven-block
interpreter proof must carry this disjunction, and any security reduction must
exclude or charge the nonce-hit event under the **joint** hash model.
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
Eight further isolated `FindAndDelete` cases each pass with a public key
recovered for the app's opcode-boundary scriptCode and fail with a key
recovered for a deliberately wrong scriptCode. They cover separated and
adjacent repeated canonical
signature pushes, an embedded byte pattern, noncanonical `PUSHDATA1/2/4`, and the
literal 56-byte pinning signature in an isolated lock.
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
count/dummy negatives, for 22 cases total.
This corroborates the selected source behavior but does not compute the final
QSB scriptCode for arbitrary Core-accepted witnesses. `CORE-FINAL-MATCH.md` records the exact
remaining Core-to-Lean final-checker bridge.
An additional isolated 10-of-10 multisignature experiment places all 151
fixture signature pushes in a nonexecuted branch. Core accepts keys recovered
against the shared scriptCode after ten selected deletions, and rejects 12
wrong-code controls, including one that retains each selected push in turn.
The two-output transaction exercises in-range `SIGHASH_SINGLE` as well as
`SIGHASH_ALL`. A `CHECKMULTISIG; DROP; TRUE` variant accepts an empty
first-scanned signature but rejects a malformed nonempty one, consistent with
the source encoding gate. The adapter does not expose the error code. These
22 cases are native evidence for selected
source behavior, not
full-lock acceptance or a proof of arbitrary-witness refinement.
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
`QSB/CoreCheckedCertificate.lean` searches the two possible first-round
multisignature outcomes and verifies the full reached source-model certificate
before returning a result. It additionally recomputes the reached first-round
source scan and requires it to equal the candidate flag. Lean proves that any
returned flag equals both this scan and the structural run's reached outcome
cursor. The finite search is sound and complete relative to candidates with
this direct-match condition, then derives the fixed `SIGHASH_ALL` obligations
from a returned certificate. The search returns a Boolean and final source
state; the `RoundWitness` in the extraction theorem is still existential and
has not been implemented as an efficient parser of adversarial transaction
bytes. Hash functions, key
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
The separate `QSB/CorePushFindAndDelete.lean` theorem now proves, for any
signature list on this fixed literal lock, that each canonical push pattern
can match only a complete original opcode chunk. Repeated deletion therefore
equals filtering those chunks, even with long, duplicate, malformed, or
subsequently skipped signatures. This discharges the 880-step fuel obligation
for the source-shaped first-round scriptCode; it does not generalize to an
unrelated lock with different encoded chunks.
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
`QSB/FinalScriptCode.lean` connects that loop to the ten signature bytes
actually reached by the final modeled CHECKMULTISIG. Under an accepted full
byte-model run and the explicit nonempty, encoding-sound successful-scan
premises, their order is second bonus, first bonus, seven gathered dummies in
reverse draw order, then the fixed nonce. Permuting that list to the nine
original dummy positions plus nonce leaves the resulting scriptCode unchanged.
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
out-of-range recovery key fails on that same transaction. This does not
establish full-lock acceptance with an alternate transaction layout.
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
No SHA256d preimage, Core transaction, or QSB spend is exhibited.

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
