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
   152 also pass the same Core adapter; a byte-level ScriptNum candidate and
   selected examples are checked in Lean, but full Core refinement is open.
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

The pinned Lean 4.30.0/mathlib build checks 539 theorem dependency lists with
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
`QSB/DERSyntax.lean` now gives an executable source-shaped translation of
[Core 27.2's strict signature-encoding checks](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp). Lean proves that any accepted
20-byte value has positive R/S byte lengths summing to 13 and the required
six-byte header/length shape. The crafted overshoot signature is accepted by
this predicate. A proof that this Lean predicate equals Core's compiled parser
for every byte string, and a count of its entire 20-byte accepted set, remain
open; the earlier `390405/2^65` figure is still conditional on that count
correspondence.
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
`QSB/FinalRoundWitness.lean` maps the recorded opening pairs into the abstract
round-witness interface using an executable lookup. Lean checks the seven-plus-two
shape and the opening hash equalities for the constructed witness. Its key is
provided independently; nonce binding, the final puzzle, a transaction-byte
extractor, and Core acceptance still need separate proofs or assumptions.

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
tails and suffixes. This advances local HORS extraction but does not identify
that stack item as an intended commitment in every witness or refine signature
outcomes to Bitcoin Core.
The result also composes with any executable program prefix, so a future
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
   accepted key encodings, sighash collisions, multiple vaults, and one shared
   query budget. Standalone unstructured-search or two-distinct-input results
   do not by themselves meet these hypotheses.
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
