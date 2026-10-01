# Security specification for the pinned Config A implementation

Status: proposed security game, grounded in inspected code; not a proved
security theorem. All statements concern the revisions in
`evidence/source-inventory.json`, not a verified deployed service or chain tip.

## Concrete construction

The supported app path calls `bridge.generate`, which calls `cmd_setup` with
Config A. `bridge.validate_state` admits only:

| Property | Value |
|---|---|
| Output type | Bare legacy script, not a P2SH or Taproot wrapper |
| HORS pools | Two distinct indexed pools, each with 150 entries |
| Secret generation | 20 random bytes per entry |
| Commitment | HASH160(secret) = RIPEMD160(SHA256(secret)) |
| Round 1 | 8 signed selections, 1 bonus selection |
| Round 2 | 7 signed selections, 2 bonus selections |
| Puzzle hash | Single SHA-256 of the witness's nonce public-key bytes |
| Fixed nonce signatures | Hardcoded DER signatures with SIGHASH_ALL = 0x01 |
| Dummy signatures | Distinct 9-byte signatures with SIGHASH_SINGLE = 0x03 |
| App spend layout | Helper input 0, QSB input 1, one destination output |
| Dummy message in that layout | 01 followed by 31 zero bytes; scalar 2^248 |
| Script budget in experiment | Derived and recorded in round-results.json |

The active legacy bytecode contains pinning, two sequential selection/puzzle
rounds, and two CHECKMULTISIG instructions. Config A has no conditional recovery
branch, alternate wallet-key branch, CLTV/CSV emergency branch, or code separator.
The UI's recovery operation unlocks the same HORS material and uses the same
spend path. The original wallet is a service requirement, not an additional
condition in the QSB output. An attacker may supply a helper input they control.

The general upstream builder also has Ar, S, D, and test configurations. Those
are not admitted by the inspected app bridge. Deprecated Config D has different
legacy code and is not covered. P2SH convenience functions are not the active
funding construction. No conclusion here applies to embedding QSB in a new
wrapper with an additional spend path.

The GPU's historical challenge leading-zero predicate is not this predicate:
the preparation script substitutes the production DER check. CPU verification
additionally checks recoverability. The combined solver and historical solver
are search implementations; neither limits a consensus adversary's witnesses.

## Security game

Fix the versioned consensus semantics, a valid unspent-output context L, and a
security parameterization of the hashes. For the concrete implementation the
hash lengths and pool sizes are fixed as above.

1. **Setup.** The challenger samples independent HORS secrets for each vault,
   builds the exact locking script, and creates a target unspent output in L.
   Its amount, script, and outpoint are public. All nonce constants, dummy
   signatures, and commitments are public. Ordinary wallet funds before their
   confirmed transfer into this output are outside the QSB custody claim.
2. **Authorization.** The honest owner chooses an exact withdrawal intent.
   Authorization covers the ordered prevouts, destination script and value,
   fee derived from authenticated prevout amounts, and the final agreed
   non-witness transaction fields. The solver may propose locktime/sequence
   within the intended search range, but HORS disclosure is attached to the
   final assembled transaction. Define Auth as the set of authorized semantic
   transaction projections **ever released with owner approval**, not the set
   of transactions the server happens to accept or currently displays. Once
   full signing material is released, later cancellation cannot revoke that
   transaction cryptographically. At minimum every never-approved recipient,
   value, or fee change is a forbidden projection. Witness-only malleations are
   not themselves theft. A separate current-intent or cancellation property
   would need a different game and likely ledger assumptions.
3. **Disclosure.** On an authorized signing request the attacker receives all
   public solver inputs and outputs, the complete assembled transaction, and
   all revealed HORS preimages. This is a conservative grant: the QSB scriptSig
   is assembled before the separate wallet signs the helper input. Disclosure
   is counted when that material leaves the trusted QSB runtime for an external
   signer, caller, or publication, whether or not a miner receives or confirms it. Abandoned jobs,
   failed submission, backup rollback, and conflicting restored devices do not
   erase the attacker's knowledge. Record D[vault,round] as the union of the
   disclosed indexed positions. Use r[vault] as the number of disclosures.
   The browser stores reminder guards in device-local storage; the SDK defaults
   to an in-memory guard unless the caller supplies persistent storage, while
   its CLI supplies a file-backed guard. These honest-client controls do not
   erase old unbound backups or constrain direct Bitcoin spending.
4. **Attacker.** A quantum algorithm may prepare arbitrary states, query the
   modeled hash oracles coherently, perform arbitrary classical computations,
   see published scripts/transcripts, supply malicious solver results, choose
   arbitrary consensus-permitted scriptSigs and transaction layouts, and use
   its own helper inputs. Grant discrete logarithms of all valid secp256k1
   points at no cost; a rigorous quantum version grants coherent evaluation
   too. No theorem may rely on ECDLP hardness, a hidden recovery nonce, or a
   requirement to use the honest CUDA enumeration.
5. **Output and success.** The attacker outputs a transaction and unlocking
   scripts/witnesses. Success means the transaction consumes a target QSB
   outpoint, is accepted by the specified ledger/consensus predicate in L,
   and its semantic projection is outside Auth. The forged transaction need
   not pass any app API, CPU admission check, or miner relay policy. A target
   already spent on the selected chain cannot be spent again in that same L;
   evaluate mempool races before confirmation, or specify the alternate chain
   context when considering a reorganization.

Core v27.2's standard policy includes `NULLFAIL` and `CLEANSTACK`, while its
mandatory verification flag list does not. The constructed bare output is not
an ordinary standard relay template. Therefore this game deliberately uses
consensus validity plus an external inclusion assumption, not mempool relay
admission. A miner that accepts nonstandard but consensus-valid transactions
could include one; whether any miner will do so is a separate empirical matter.

An actual Lean theorem will need explicit types and predicates implementing all
five items. The current `ExtractedRound` is an intermediate algebraic interface,
**not** a replacement definition of consensus acceptance or of this game.
`QSB/Game.lean` now defines a transaction projection, an unauthorized-spend
predicate with Core acceptance and target consumption left explicit, and a
monotone disclosure history. Its authorization lemma covers changed outputs;
the Bitcoin parser and acceptance predicate still require refinement.
`QSB/Reduction.lean` states the next implication with an extractor that reads
the adversary's transaction and returns its pinning and final-round witness.
That extractor is not implemented for arbitrary Script executions. A shaped
final witness requires seven distinct signed positions and two disjoint bonus
positions; otherwise the corresponding extraction gap remains possible.
Within the literal byte model, `FinalSignedChain.extractWholeFinal` now
computes the seven signed positions and actual openings from any successful
full run, including arbitrary initial byte stacks and supplied signature
outcomes; `extractWholeRemaining` computes their ordered residual pool.
Neither consumes transaction bytes or establishes that Core
acceptance supplies such a run. Under the later source-shaped final scan and
signature-encoding premises, `FinalRoundWitness.extractMatchedWitness`
computes a complete modeled `RoundWitness` from this trace, the two reached
bonus signature bytes, and the last reached key. The game extractor still
needs an actual transaction and Core-acceptance refinement.
One final-suffix invariant is now proved for arbitrary underlying stacks:
successful execution of the ten fixed public-key rolls preserves the pushed
signature count 10 at CHECKMULTISIG's count position, and the final push makes
the public-key count 10. In the generated byte suffix, if the pre-suffix stack
is `first :: rest`, the ten final signature slots contain `rest[0..9]`, and
successful modeled execution forces the next source cell `rest[10]` to exist
and be empty for NULLDUMMY. A Core-style matching-loop theorem shows that a
successful 10-of-10 match cannot skip a key and must verify each corresponding
pair. This does not establish that the ten signature cells arose from the
intended dummy pool or that Core's byte-level verifier equals the abstract
pair predicate.
The exact byte-model suffix from immediately after the last final-round bonus
roll sharpens this source statement: for any stack at that boundary whose
remaining program succeeds, its cells 0–9 become the final signature slots,
and cell 10 becomes the empty NULLDUMMY slot. The intervening late puzzle
check and deep key rolls do not change those eleven sources. Later full-run
byte-model theorems identify the preceding signed and bonus sources; Core
execution and signature-verifier refinement remain unproved.
For the last bonus roll, this forces an empty pre-roll source at depth 10 if
the decoded index is below 10, or at depth 9 if it is at least 10. The four
generated instructions between bonus rolls preserve the first roll's shallow
cells below a new top index. Consequently, when pre-first-bonus source cells
9 and 10 are both nonempty, a first bonus index below 9 is impossible on a
successful modeled suffix; the last bonus index must also be at least 10.
The generated initialization pushes 150 nonempty dummy bytes, and seven
selections confined to that pool leave the two premises true regardless of
selection order. The checked full-program byte-model theorem now confines all
seven signed selections to that pool and records their distinct original HORS
positions. A second full-program byte-model theorem transports those cells
through the reached bonus suffix: the decoded first bonus roll depth is in
9–152 and the last in 10–152. Bitcoin Core refinement remains unproved.
For the reached first bonus roll, the byte-model source map identifies depths
9–151 as surviving 9-byte dummies and depth 152 as the first surviving
20-byte HORS commitment. The selected byte is tracked through the actual
modeled roll. The latter branch is the setup exception requiring signature
validity analysis. A checked reached-roll map classifies the second source:
after a dummy first choice, second depth 152 reaches the first commitment;
after a commitment first choice, every reachable second source is a dummy.
The actual second moved byte follows that map. A checked arbitrary full-run
byte-model theorem records both post-bonus states and selected-byte equations,
as well as the seven distinct signed HORS openings. Its final-witness theorem
identifies the ten pre-CHECKMULTISIG signature-source cells as second bonus,
first bonus, seven gathered dummy bytes, and fixed nonce, followed by the
empty dummy. The sole possible bonus commitment is one original second-round
HORS position absent from the seven signed openings; either overshoot places
it in a specific final signature slot. Core signature validity and the DER-shaped setup event remain
open.
The byte model also proves that both bonus depths stay below 152 if those two
reached signature slots satisfy a supplied syntax predicate and no generated
second-round commitment does. The syntax premise is not inferred from the
model's supplied CHECKMULTISIG Boolean; Core parsing and verification remain
to be connected.
The Core-shaped equal-count matching-loop theorem provides a narrower
interface: a successful ten-pair scan and a per-pair verifier sound for syntax
imply that the reached bonus slots satisfy the syntax predicate. Equality of
that abstract scan with the actual Core check remains an external obligation.
`CORE-FINAL-MATCH.md` states the source-level refinement contract, including
Core's sequential opcode-boundary FindAndDelete before its ten-pair scan. Eight
isolated pinned-Core differential cases corroborate the app's FindAndDelete
behavior on canonical, repeated, embedded-pattern, and noncanonical PUSHDATA1/2/4 pushes;
they do not determine the full QSB scriptCode for arbitrary witnesses.
`QSB/CoreMultisigStack.lean` separately proves that Core's bottom-first
one-based stack addresses correspond to the byte model's ten reached final
signature/key slots and NULLDUMMY cell in every truthy full byte-model run.
It leaves the actual Core pair-verification outcome as an explicit premise.
The pinned Core encoding gate permits an empty signature, even though an empty
signature cannot make an ECDSA pair check succeed. The refined Lean interface
therefore states nonemptiness and encoding acceptance separately for every
successful pair; it does not infer either fact from a supplied Boolean outcome.
For the one literal disposable lock in the Lean byte model, all 150
second-round commitments fail a source-shaped strict DER predicate. Under a
successful DER-sound ten-pair scan, neither final bonus index can reach a
commitment in that lock. The claim does not quantify over other generated
setups or replace compiled-Core refinement. The checked alternative says that
any matched modeled bonus overshoot identifies an unopened original commitment
that passes the same signature-syntax predicate. Specializing to strict DER
produces a dummy-bonus-or-unopened-DER-commitment disjunction. Its bad-setup
branch still needs dynamic-lock bytes and a Core parser bridge before it can
be charged to a setup probability.
At the local reached-scan boundary, Lean now allows an arbitrary commitment
map: aligned residual pool positions and the two bonus slot equations imply
that any commitment-selection branch is a syntax hit at an unopened position.
For outputs of one uniformly sampled twenty-byte function `R`, independent of
the material selecting its 150 inputs, a checked shared-function count bounds
the DER setup-hit fraction by `150·12/256^6`. The parameterized byte-model
execution below now supplies the aligned boundary; universal builder-to-model
correspondence and Core acceptance implying its matched signature scan are
still separate obligations. Neither is supplied by the count theorem.
The parameterized second-round data block in `DynamicFinalInit` supplies the
first such execution boundary for arbitrary commitment and nonce bytes: every
successful modeled block has the intended stack order and initially aligned
pools. The literal block is its exact specialization. A three-build
pinned-builder check corroborates push order and the unchanged post-data
opcode suffix across two setups and a 20-byte final nonce. The seven signed
selections and both bonus source traces have now been lifted through that
parameterized suffix; universal builder-to-model correspondence remains open.
At one reached signed comparison, the parameterized source classifier gives a
current commitment with its original pool position whenever the nonce bytes
are not 20 bytes. Without that width premise, a shallow selection can instead
be the fixed nonce itself, provided it is 20 bytes and equals the HASH160 of
the supplied opening. A conditional run theorem derives this result from the
generated five-opcode comparison with an explicit reached post-ADD stack and
bounded parsed roll depth. A pinned-Core isolated `CHECKSIG` probe demonstrates
that a 20-byte strict-DER `SIGHASH_ALL` nonce can verify for a recovered key;
it does not demonstrate a matching hash opening or a QSB spend. Lean now
proves that a successful *complete* signed suffix preserves the retained raw
bytes through comparison and parses them nonnegative at the final dummy roll.
This places the earlier comparison at depth at least 145, where every shallow
source is a nine-byte dummy; a matching bounded source must be a commitment,
irrespective of nonce width. Thus the nonce branch is only possible for a
comparison prefix that does not complete the signed block in this byte model.
For the first signed selection, Lean now starts before the dynamic data pushes
and proves the disjunction from a successful prefix run through the first
comparison. It extracts the actual witness-tail raw index, applies the reached
MIN/ADD cap, and identifies a commitment by original pool position when that
branch occurs. This prefix is exactly the literal final round's first 314
instructions under the fixture specialization. A second checked theorem
carries the first full block through the paired dummy roll: from the data
pushes to the first 315 literal instructions, success forces an
original-position commitment opening even with a 20-byte nonce. The exact
dynamic pool-transition induction now covers all seven blocks and returns the
same executable opening and residual-position traces as the literal proof.
`DynamicBonusFirst`, `DynamicBonusSecond`, `DynamicBonusTrace`, and
`DynamicBonusChain` carry the aligned pool through both reached bonus draws
and the late-puzzle stack rearrangement. Successful parameterized byte-model
execution places the bonus bytes in final signature slots 12 and 13, the
seven gathered dummies in slots 14–20, the arbitrary nonce in slot 21, and
the empty dummy in slot 22. A bonus index at 152 selects a commitment at an
original position outside the seven openings. With an explicit successful
DER-sound ten-pair scan, `DynamicBonusDER` proves that both bonus draws stay
in the dummy region or an unopened commitment passes DER syntax. The latter
is a setup exception, not a quantum spend bound. Compiled-Core acceptance,
checker refinement, universal builder correspondence, and transaction-level
extraction remain open.
Under the complementary premise that all 150 second-round commitments fail
strict DER syntax, `DynamicBonusIndices` proves that the two reached bonus
signature bytes are surviving dummies at distinct original positions outside
the seven signed openings. `DynamicBonusSetup` lifts this pointwise result to
one shared sampled twenty-byte-output setup function: later witness choices
may depend on that function, while the material choosing its 150 setup inputs
is independent of it. The excluded DER-shaped-commitment setup fraction is
bounded by `150·12/256^6`; `DynamicBonusProbability` proves the same
inequality for the uniform measure on the nonempty finite setup space. This
is classical uniform-function setup analysis, not a coherent-query or
unauthorized-spend bound.
`DynamicSetupReduction` inserts that setup term into the game-level measure
bound. With an explicit uniform setup marginal, good-setup transaction/Core
extraction, honest release, and fresh-opening plus distinct/same-key puzzle
event bounds for one joint adversary distribution, Lean proves
`Pr[Unauthorized] ≤ εfresh + εdistinct + εsame + 150·12/256^6`.
The good-setup extraction and all three quantum event bounds remain external
premises. In particular, the count theorem supplies only the final setup
term and cannot justify setting the other terms to zero.
For that same accepted byte-model run, `QSB/FinalBonusIndices.lean` identifies
both reached bonus signature bytes as generated dummies at original HORS
positions disjoint from the seven signed opening positions. The union has nine
positions. The seven other final signature slots contain generated dummies at
the traced positions in reverse draw order; the remaining slots contain the
fixed nonce and empty NULLDUMMY byte. `QSB/FinalRoundWitness.lean` uses an
executable lookup over the seven recorded opening pairs to populate the
`RoundWitness` shape and valid
opening fields used by the abstract reduction. The earlier shape theorem
accepts a separately supplied key. A newer full-run theorem uses the key in
the actual last reached final multisignature slot and proves that the late
puzzle CHECKSIGVERIFY receives SHA256 of those same bytes. Conditional on
encoding-sound successful final and puzzle checks, SHA256 of this reached key
is strict DER and the fixed nonce checks against it. The executable
`extractMatchedWitness` builds this modeled witness from the reached signed
prefix, final bonus signature slots, and final key slot; the source-shaped
certificate proves equality with that computed value. This dummy-only bonus
argument relies on the literal generated commitments being non-DER; other
setups need an exceptional branch. The real transaction
sighash/ECDSA nonce relation, compiled-Core refinement, and a transaction-byte
extractor remain open.
At the first signed selection of the final round, the generated lookup map
has a sharper local boundary: indices 0–1 point to 9-byte dummy signatures,
2–151 to the 150 20-byte HORS commitments, and capped 152 to the prior round's
Boolean CHECKMULTISIG result. The modeled generated comparison tail rejects
the capped case and low indices because HASH160 outputs 20 bytes. A successful
full byte-model execution now forces the first final-round signed raw index
to parse as `2+i` for `i<150`, with generated commitment `i` equal to the
HASH160 of the actual opening. This includes all negative raw values and
nonminimal encodings in the exclusion argument. Lean checks the repeated
13-opcode schema, including the fixed raw-index roll, for all seven signed
blocks. For any reached block with the current pool shape and original-index
alignment, successful byte-model execution forces an in-range current
commitment, equates it with the actual opening's HASH160, and removes that
commitment and its matching dummy. The two pool invariants survive for the
next block. `QSB/FinalSignedChain.lean` establishes the starting premises and
composes all seven blocks from an arbitrary successful full generated
byte-model run. Its trace contains seven distinct original commitment
positions, each matched to the HASH160 of the opening consumed at that block.
Core refinement and actual signature verification remain required.
The literal-byte lock fixture separately proves that each of its 15 HORS
`OP_EQUALVERIFY` comparisons immediately follows `OP_HASH160`. In the byte
interpreter, any reached comparison on an accepting modeled run must equate
the hash of the actual opening bytes to the bytes immediately below them.
The full-run byte-model theorem now identifies commitment origins for the
seven final signed checks. It has not been lifted to an arbitrary
consensus-accepted Bitcoin witness: Core execution and signature-check
outcomes still require refinement.
A generated disposable witness executes the complete byte fixture and reaches
all 15 comparisons, conditional on a lookup-table HASH160 and externally
supplied signature results. That single run does not discharge the
arbitrary-witness obligation.
The formal disclosure and extracted-witness records expose HORS values only at
their declared opened positions; no total secret array is included in the
attacker transcript type.
The measured fresh-opening and two-puzzle events require a projection outside
the owner's authorization set, but do not assume Bitcoin acceptance. Without
that restriction, a replay or harmless mutation of a released authorized
transaction could make the proposed primitive event likely even when no theft
occurred. The owner-forbidden message class is fixed independently of the hash
and Script predicates.
The two bonus-slot experiments also mean an unconditional final-round
seven-plus-two *dummy-position* extractor is too strong for arbitrary setup
bytes. A 20-byte HORS commitment could itself parse as a DER signature; an
ideal random HASH160 output gives that event positive probability. The current
Lean reduction leaves it in `ExtractionGap`. A useful next refinement would
separate such setup/encoding exceptions from other arbitrary-witness gaps and
bound them under an explicit joint hash model.
For reference, the Lean-checked 20-byte DER count expression gives syntactic
density `390405 / 2^65`. Lean now proves uniform target density for any
`R160(source ξ)` in a finite idealization where the entire R160 function is
sampled independently of input-selecting setup material `ξ`. Taking `ξ` to
contain the H256 oracle and honest secret makes `source ξ = H256(secret)`. The
same shared-function model proves a union bound without assuming distinct
inputs or independent outputs. If the expression matches Core's parser, the
probability that any
commitment is DER-shaped is at most 300 times this density by a union bound.
That is only a setup-syntax calculation, not a bound on unauthorized spending.

## Hash model and resources

The natural candidate idealization uses independent random functions H256 and
R160 with quantum query access. SHA256d(x) is H256(H256(x)); HASH160(x) is
R160(H256(x)); the puzzle uses that SAME H256 on key bytes. Do not replace these
uses with independent oracles without a domain-separation argument. The code
does not add domain-separation tags. Public-key encodings, hash inputs of other
roles, and attacker-selected preimage lengths must be accounted for.

`QSB/JointSourceChecks.lean` instantiates the deterministic source checks
with exactly this shared `H256 = H`, `SHA256d = H ∘ H`, and `HASH160 = R ∘ H`
structure. `QSB/DynamicJointTransaction.lean` now instantiates all ten
reached final source checks for a selected transaction input: each successful
external ECDSA call uses that signature's actual hash type, one common
Core-shaped deleted scriptCode, and either `H(H(legacy preimage))` or the
out-of-range SINGLE constant. The same certificate exposes the first pinning
call on the lock-pushed signature; if that signature ends in `0x01`, its
source ECDSA digest is `H(H(sourceAllPreimage))`. This hash-type condition is
explicit for the parameterized lock. The certificate and checker remain source-model
premises. These modules have no random-oracle sampling or quantum-query
semantics; the query-success theorem still needs a game over those same
functions and their adaptive disclosures.

Use **one shared adversary budget `q`** for coherent queries to the tagged
oracle that evaluates either H256 or R160. A query controlled by a
superposition of primitive tags consumes one query, so a proposed bound may
not assign a fresh `q` to each primitive, each SHA256d/HASH160 composition,
each vault, or each disclosure phase. Honest setup and classical signing can
evaluate the same functions without being charged as adversary queries, but
their published, oracle-correlated values must be included in the game.
Preprocessing and attacker queries before disclosures count toward `q`.
`QSB/Probability.lean` checks finite multi-vault union accounting without any
independence assumption; it does not license assigning a separate full query
budget to each vault when stating the per-vault primitive bounds.
After one final-round disclosure of seven distinct positions, the shaped
covered choice space has `C(7,7)·C(143,2) = 10,153` signed/bonus pairs. Two
disjoint such disclosures raise `d` to 14 and the count to 34,845,096. These
are Lean-checked arithmetic statements for the abstract pool model, not an
attack probability or a proof that Script enforces the shaped choices.
Quantum query count is not a physical runtime estimate: memory, circuit depth,
fault tolerance, and parallelism need a separate analysis.

The signing interface is classical. Granting quantum superposition access to a
wallet signing oracle would be a stronger, different game and must not be
imported accidentally from quantum-access signature literature.

No primitive quantum bound has yet been instantiated. In particular, a target
density calculation is neither a lower bound on attack work nor an upper bound
on QSB forgery probability. No multiplication of pinning and round probabilities
is justified by separate-looking code paths.
The `NovelTwoPuzzle` event asks for two DER-valid key hashes, but a new
transaction might reuse a previously successful key. Exact legacy sighash
replay and serialization equivalence are possible routes. Moreover, even with
*different* message scalars, one fixed ECDSA signature and public key can
verify through different admissible recovery points: `R` and `-R` share an
x-coordinate and hence the same `r`. The pinned secp256k1 fixture in
`evidence/ecdsa-replay-targets.json` exhibits this algebraic case, not a QSB
spend or a transaction preimage. A same-key bound must target the finite set
of message scalars permitted by all admissible recovery points, after Core's
hash-to-scalar conversion; it cannot classify every new-message replay as a
hash collision. Lean bounds admissible points and message group-element
targets by four conditional on the at-most-two-points-per-x curve/parser
premise; that premise and Core's digest conversion remain unproved. The event
is therefore a joint search-or-replay target, not
necessarily two fresh independent DER hits. Bounding it must include the
shared hash oracles, sighash correlations, all accepted public-key encodings,
and adaptive disclosed subsets.
For the source-shaped legacy ALL serializer, Lean now proves that any
owner-forbidden exact projection in one fixed ledger context has a different
preimage from every approved release. The proof decodes the complete prepared
preimage and recovers ordered outpoints, sequences, outputs, version, and
locktime; the fixed ledger maps those outpoints to previous outputs and fee.
Different preimages still may hash to one fixed signature/key's admissible
ECDSA target digest. Core serializer and ledger refinement, and the shared-
budget quantum target-hit bound, remain open.
It also does not require the pin and final-round key bytes to be distinct; a
distinct-input QROM theorem cannot cover their equality case without a
separate argument.

## Spend-path and attack table

| Phase/path | Attacker action | Actual condition / current result |
|---|---|---|
| Before QSB funding | Break an ordinary wallet signature | Outside protection of an already-created QSB output; funding wallet security remains a separate issue. |
| Funded, no disclosures | Open unrevealed commitments | HASH160 preimage/multi-target problem after valid-index extraction; quantum bound and full extraction pending. |
| Pinning | Replace fixed ALL signature with NONE/SINGLE/ANYONECANPAY | Fixed signature bytes are in the lock; attacker cannot directly replace them. FindAndDelete and stack extraction still require proof. |
| Pinning | Recover EC private scalars | Explicitly granted. Candidate-key derivation is already public; field equation lemmas are checked in Lean. |
| Pinning / round puzzle | Use alternative serialized keys | Core admits compressed, uncompressed and correctly formed hybrid keys under the inspected consensus flags. The GPU's compressed-only search is not an adversary restriction. |
| Hash-derived puzzle signature | Choose favorable sighash byte | A 256-case isolated Core sweep accepts every last-byte value with a recovered key under the pinned consensus flags. Do not infer SIGHASH_ALL authorization from this signature. The fixed nonce signature is the intended binding check. |
| Round 1 multisignature | Let CHECKMULTISIG return false | First result is left under later stack data. Modified-lock Core consensus experiment accepts this case. Standard relay policy may reject a false nonempty signature through `NULLFAIL`, but relay policy is not a consensus security condition. Full two-round binding cannot be assumed. |
| Round 1 after disclosure | Reuse its old nonce key after changing destination | Core accepts the modified test lock even though the old nonce key fails on the new transaction; pinning and round 2 are freshly recovered. Under the real lock, the original DER-valid SHA256(old key) remains DER-valid, and a puzzle verification key for the new message is publicly recoverable. This is a conditional attack route, not a solved real-lock forgery. |
| Round 1 HORS | Supply an incorrect preimage | Rejected in Core experiment. The unchecked multisignature does not remove earlier OP_EQUALVERIFY checks. |
| Round 2 multisignature | Let final CHECKMULTISIG return false | Rejected in Core experiment; final stack truth is required. |
| Signed indices | Negative, large, duplicate, or reordered indices | OP_MIN only upper-clamps. An initial stack with any parsed first index at least 152 makes the first signed selection try to reach below the intended commitment pool. For the exact stated top-stack family, Lean proves the full byte-model program rejects every post-index continuation: an empty one fails the external-cell roll; a short one after a marker fails the opening roll; otherwise a marker mismatch fails the first hash comparison, and a match makes the next fixed roll select a 20-byte lock commitment as a ScriptNum operand. Longer stacks hit the modeled 1000-cell limit. This includes nonminimal encodings accepted by the byte model. Truncated-lock Core tests for canonical 152, nonminimal `980000`, and four-byte `ffffff7f` accept immediately before that `OP_MIN` and reject when it is added. This is a counterexample to cap-only or single-comparison confinement arguments, not an accepted forgery. The general arbitrary-witness loop invariant remains open. |
| Bonus indices | Reuse gathered signatures, select nonce, null dummy, or a commitment | Either final-round bonus index of 152 can reach round-2 commitment position 7 after canonical signed selections. An altered-lock Core test accepts each role when the commitment bytes are a DER-valid signature and the attacker supplies the recovered public key, with puzzle checks relaxed. The test's crafted commitment is not HASH160 of a generated secret; valid-setup probability and the full real lock remain unresolved. Counting ordinary subsets alone is insufficient. |
| Dummy signatures | Change destination under SIGHASH_SINGLE bug | Isolated Core tests confirm the dummy signature verifies in the 2-input/1-output layout, where its message is constant. With two outputs, its message is in range: a full two-round, puzzle-relaxed lock rejects the old recovered dummy keys, accepts newly recovered keys, and rejects a selected second-output mutation. It accepts an unselected first-output mutation with the same dummy keys when the fixed ALL keys are rederived. Lean proves that in-range SINGLE's source preimage and joint digest ignore unselected outputs. The key bytes supplied by the scriptSig must be modeled. The unmodified lock's puzzle checks and arbitrary input layouts remain untested by this case. |
| Alternate transaction layout | Use more inputs/outputs or reorder QSB input | App refuses such layouts, but Bitcoin may admit them. Full security game must analyze their in-range SINGLE sighashes and publicly recovered verification keys, not forbid them by service policy. |
| ScriptCode | Exploit FindAndDelete across pools / embedded data | Must track deletion at instruction boundaries, all multisig signature items, and code-separator semantics. Source pinning is not a proof. |
| Arbitrary scriptSig | Execute non-push opcodes before the bare lock | Core's bare-script boundary passes any successful scriptSig stack to the lock with a fresh opcode counter. Lean proves first modeled commitment origin for an arbitrary preceding stack evaluator, but Core-to-byte-model refinement and later selection sources remain open. |
| Mempool / cancelled spend | Reuse the disclosed 15 preimages for a new recipient | Principal fresh-message attack. Round 1's unchecked result obstructs intended two-round analysis; remaining puzzle-search quantum reduction pending. |
| Multiple disclosures | Combine preimages from different authorizations | Union D grows monotonically; Lean proves the structural accounting. One-time wallet guards are not on-chain enforcement. |
| Recovery | Bypass original wallet by using one's own helper | Permitted by the output script if other conditions are met. Original-wallet API authentication cannot be used as a cryptographic assumption. |
| Backup compromise | Guess passphrase or steal decrypted secrets | Device/backup confidentiality assumption, not a QSB hash-puzzle theorem. PBKDF iteration count and character minimum do not establish password entropy. |
| Repeated funding / several vaults | Reuse a script/key or attack many targets | Must count shared secrets and total targets; service's one-deposit rule does not constrain outside payments. |
| Miner policy / reorganization | Race, censor, or change the selected chain | Inclusion/liveness and consensus security assumptions are separate from script-level unforgeability. |

## Required proof chain

Actual accepted unauthorized spend
→ faithful arbitrary-witness Script extraction for pinning and FINAL round
→ fresh final-round target opening OR a novel two-puzzle solution
→ a precisely specified quantum oracle problem
→ a concrete query-success upper bound.

Only generic portions of the middle implication and probability bookkeeping
are currently proved. The game-level Lean theorem includes a visible
`ExtractionGap` branch. Pinning and final-round puzzle composition, faithful
extraction, and a matching quantum query theorem remain open. The first-round
multisignature cannot be added back as a necessary condition. An unexplained
"implementation error probability" cannot be assigned zero to bridge these gaps.
