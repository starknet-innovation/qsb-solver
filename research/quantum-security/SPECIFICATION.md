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
One final-suffix invariant is now proved for arbitrary underlying stacks:
successful execution of the ten fixed public-key rolls preserves the pushed
signature count 10 at CHECKMULTISIG's count position, and the final push makes
the public-key count 10. A Core-style matching-loop theorem shows that a
successful 10-of-10 match cannot skip a key and must verify each corresponding
pair. This does not establish that the ten signature cells arose from the
intended dummy pool or that Core's byte-level verifier equals the abstract
pair predicate.
The literal-byte lock fixture separately proves that each of its 15 HORS
`OP_EQUALVERIFY` comparisons immediately follows `OP_HASH160`. In the byte
interpreter, any reached comparison on an accepting modeled run must equate
the hash of the actual opening bytes to the bytes immediately below them.
This has not been lifted to an arbitrary accepted Bitcoin witness: the
commitment cell's origin and the signature-check outcomes still require a
whole-program stack invariant and Core refinement.
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
The last-bonus experiment also means an unconditional final-round
seven-plus-two *dummy-position* extractor is too strong for arbitrary setup
bytes. A 20-byte HORS commitment could itself parse as a DER signature; an
ideal random HASH160 output gives that event positive probability. The current
Lean reduction leaves it in `ExtractionGap`. A useful next refinement would
separate such setup/encoding exceptions from other arbitrary-witness gaps and
bound them under an explicit joint hash model.
For reference, the Lean-checked 20-byte DER count expression gives syntactic
density `390405 / 2^65`. If each of the 300 commitment bytestrings is marginally
uniform and that expression matches Core's parser, the probability that any
commitment is DER-shaped is at most 300 times this density by a union bound.
That is only a setup-syntax calculation, not a bound on unauthorized spending.

## Hash model and resources

The natural candidate idealization uses independent random functions H256 and
R160 with quantum query access. SHA256d(x) is H256(H256(x)); HASH160(x) is
R160(H256(x)); the puzzle uses that SAME H256 on key bytes. Do not replace these
uses with independent oracles without a domain-separation argument. The code
does not add domain-separation tags. Public-key encodings, hash inputs of other
roles, and attacker-selected preimage lengths must be accounted for.

Count q256 and q160 separately, including coherent queries, preprocessing,
multi-vault work, and attacker queries before disclosures. The honest setup and
signing computations condition the oracle transcript and must be modeled.
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
transaction might reuse a previously successful key if its fixed-signature
legacy sighash collides or has an overlooked serialization equivalence. It is
therefore a joint search-or-replay target, not necessarily two fresh independent
DER hits. Bounding it must include the shared hash oracles, sighash collisions,
all accepted public-key encodings, and adaptive disclosed subsets.
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
| Signed indices | Negative, large, duplicate, or reordered indices | OP_MIN only upper-clamps. An initial stack with index 152 makes the first signed selection roll reach an external 20-byte cell after the intended commitment pool. For the exact stated initial-stack family, Lean proves the full byte-model program rejects even a matching external marker: the next fixed roll selects a 20-byte lock commitment as a ScriptNum operand. Truncated-lock Core tests accept immediately before that `OP_MIN` and reject when it is added. This is a counterexample to cap-only or single-comparison confinement arguments, not an accepted forgery. The general arbitrary-witness loop invariant remains open. |
| Bonus indices | Reuse gathered signatures, select nonce, null dummy, or a commitment | A last-bonus index of 152 reaches round-2 commitment position 7 in the generated trace. An altered-lock Core test accepts that role when the commitment bytes are a DER-valid signature and the attacker supplies the recovered public key, with puzzle checks relaxed. The test's crafted commitment is not HASH160 of a generated secret; valid-setup probability and the full real lock remain unresolved. Counting ordinary subsets alone is insufficient. |
| Dummy signatures | Change destination under SIGHASH_SINGLE bug | Isolated Core test confirms the dummy signature still verifies in the 2-input/1-output layout. Dummies do not bind outputs. |
| Alternate transaction layout | Use more inputs/outputs or reorder QSB input | App refuses such layouts, but Bitcoin may admit them. Full security game must analyze their non-bug sighashes, not forbid them by service policy. |
| ScriptCode | Exploit FindAndDelete across pools / embedded data | Must track deletion at instruction boundaries, all multisig signature items, and code-separator semantics. Source pinning is not a proof. |
| Arbitrary scriptSig | Execute non-push opcodes before the bare lock | Consensus permits more than the app's honest push-only witness. Needs a general initial-stack argument and global stack/element limits. |
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
