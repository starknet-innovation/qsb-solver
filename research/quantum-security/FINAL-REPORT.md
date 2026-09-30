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
   and identify fixed commitment `152+i`, for `i<150`. The full accepted-run
   bridge and later selections remain to be proved.
4. A last-bonus index of 152 selects a locking-script HORS commitment rather
   than a dummy signature in the generated stack trace. On a deliberately
   altered 20-byte DER-shaped commitment, the puzzle-relaxed full lock passes
   Core's actual final `CHECKMULTISIG` with a recovered public key; the natural
   commitment rejects this overshoot. The crafted commitment does **not**
   equal `HASH160` of its generated HORS secret. This is a source-extraction
   edge case and a possible bad-setup condition, not a production-vault
   forgery or a solved real hash puzzle.
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

The complete spend-path and attack table is in `SPECIFICATION.md`. It covers
funding, pinning, both rounds, index and scriptSig manipulation, disclosure,
recovery, alternate transaction layouts, policy, and chain inclusion.

## What Lean proves

The pinned Lean 4.30.0/mathlib build checks 267 theorem dependency lists with
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
pair. This fixes the count and matching obligations, but not the provenance of
those cells or the refinement from the abstract pair predicate to Core's byte
parser, FindAndDelete scriptCode and ECDSA checker.

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
`300 * 390405 / 2^65`, without assuming independence. This is a setup-syntax
bound, not an extraction-gap or spend bound.

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
