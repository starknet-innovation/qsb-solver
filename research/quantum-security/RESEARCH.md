# Primary research and applicability

Read alongside the source-based analysis, not as external certification of this
implementation. Bibliographic references below are primary sources.

## QSB construction

Avihu Mordechai Levy, *Quantum-Safe Bitcoin Transactions Without Softforks*,
[PDF at the implementation's pinned upstream revision](https://raw.githubusercontent.com/avihu28/Quantum-Safe-Bitcoin-Transactions/2c9172051d5c150ef0a994ca6b988a08a3ef9e85/paper/QSB.pdf).
Downloaded PDF SHA-256:
`37bcec4564e4950967803b7482e28614de4acbfbacd5e6de4ad0341b13fac6ba`.

The paper motivates fixed-signature public-key recovery, hash-to-signature
puzzles, FindAndDelete subset selection, and HORS authorization. Sections 3.3
and 4 analyze two rounds and discuss quantum search. This project does not adopt
its numerical security estimates as proved bounds. The actual emitted script,
its first-round Boolean handling, and an explicit joint quantum oracle game
must first be reconciled with the intended construction. Paper estimates are
not Lean theorems and are not a substitute for that reconciliation.
The paper's RIPEMD160 puzzle density is also distinct from the pinned worker's
Config A, which selects `hash_mode='sha256'` in `qsb_pipeline.py`; the worker
names its RIPEMD160 variant `Ar`. The report states separate illustrative
DER-20 and DER-32 calculations and treats neither as a spend bound.

## Quantum subset cover

Samuel Bouaziz-Ermann, Alex B. Grilo, and Damien Vergnaud,
[*Quantum Security of Subset Cover Problems*, ITC 2023](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITC.2023.9).
Downloaded PDF SHA-256:
`d940d9bd38dab895c7c0790346cd08085ed30425013a7895703ebd889361b45e`.

The standard subset-cover problem takes subset indices from evaluations of
specified random hash functions on messages. Its quantum query bounds are
relevant background, but the inspected QSB code searches over subsets that
change ScriptCode and a recovered key. Establishing that this procedure has
the distribution and adversarial access required by a subset-cover theorem is
an additional reduction. Adaptive disclosures, bonus indices, and failed
round enforcement must be included. No result from the paper has yet been
instantiated as a QSB bound.

## Quantum search

Michel Boyer, Gilles Brassard, Peter Høyer, and Alain Tapp,
[*Tight Bounds on Quantum Searching*](https://arxiv.org/abs/quant-ph/9605034).
Bennett, Bernstein, Brassard, and Vazirani,
[*Strengths and Weaknesses of Quantum Computing*](https://arxiv.org/abs/quant-ph/9701001).

These establish the black-box unstructured-search baseline. A target density p
suggests square-root search cost under that model. It does not show that a
structured protocol exposes only that model, that adaptive predicates are
independent, or that multiplying several target densities yields a valid QSB
quantum bound. An attack's query cost is an upper bound on attack complexity,
not a proof of a matching lower bound.

Takashi Yamakawa and Mark Zhandry,
[*Classical vs Quantum Random Oracles*, EUROCRYPT 2021, Theorem 9](https://iacr.org/archive/eurocrypt2021/126960137/126960137.pdf).
For a single fresh random function H and two **distinct** output inputs, the
theorem bounds the probability that both H outputs lie in a fixed target set of
density p by `(2q+1)^4 p^2` after q quantum queries. This applies to the
standalone, no-correlated-advice two-target experiment, provided the parser's
target density has been correctly counted. It does **not** yet give a QSB
unauthorized-spend bound: the honest solver can publish oracle-correlated
DER-valid keys, the same key-byte input might satisfy both signature roles,
and the legacy sighashes also use the same hash oracle. Counting all honest
oracle work as part of q is formally possible but can make the estimate vacuous.
The QSB target additionally relates both keys to one adversarial transaction
and a variable selected subset. A proof must separate key reuse and equal-key
cases and model the signing transcript, rather than simply substitute the
DER count into Theorem 9. The theorem's q-to-the-fourth loss also shows that
two unconstrained hits alone do not double the quantum work exponent.
`QSB/DynamicRetarget.lean` now makes the approved-call history split explicit:
an unmatched signature/key pair may reuse a key released under another
signature, in which case the source reduction retains an at-most-eight digest
target event instead of treating `H(key)` as a new DER hit. Even when no
approved-call record uses the key, absence from that list does not establish
that the key was unqueried or oracle-independent. Thus the distinct-input
theorem still cannot be applied to the complete QSB event without a causal
transcript and shared-query argument.
`OracleDependentSelection.singleton_target_count_not_adaptive_bound` gives a
finite warning about per-key counts: every fixed key has one digest target,
but an oracle-dependent disclosed digest can determine a key whose target is
hit in every world. This does not model ECDSA or a causal query budget; it
shows why the eight-target contract alone cannot supply an adaptive bound.
`history_event_public_case` additionally takes a supplied public-key set.
It routes an unmatched pair using an already disclosed key to the finite
digest-target branch, even without an approved-call record. The set's
completeness and any quantum oracle-query history remain external premises.
`search_good_setup_joint_public_history_event` applies that split to both
reached calls in one good-setup source certificate alongside the seven
opening equations, with one shared H/R pair and no independence assumption.

Qipeng Liu, [*Non-uniformity and Quantum Advice in the Quantum Random Oracle
Model*](https://arxiv.org/abs/2210.06693), treats oracle-dependent advice as
part of the security experiment and gives bounds for certain search games,
including one-way inversion. QSB's classical signing transcripts are likewise
oracle-dependent and may contain already-valid puzzle inputs. Liu's inversion
bounds do not directly address QSB's joint pinning/subset/sighash relation; they
identify the kind of advice accounting a new reduction must make explicit.

Minki Hhan and Aaram Yun,
[*Oracle Recording for Non-Uniform Random Oracles, and its Applications*](https://eprint.iacr.org/2023/1371.pdf),
prove an `O(p q²)` search-success bound for an independently sampled Bernoulli
oracle with marked-output probability `p`. This is a candidate tool for the
fresh-key branch isolated by `QSB/DynamicDisclosureEvent.lean`, not a bound
already applicable to QSB: the complete game reveals oracle-dependent good
keys, and the same multi-bit `H` also computes sighashes and HASH160 inputs.
Any reduction must preserve that shared oracle, count all relevant coherent
queries, and handle the known-key retarget branch separately.
The same paper re-proves an `O(q³/2^n)` collision-success bound for a uniform
`n`-bit random oracle. `QSB/DynamicRetarget.lean` now supplies a collision in
the same H whenever a reused fixed signature/key verifies on a distinct ALL
preimage with the approved `SHA256d` digest. Applying a collision theorem to
the complete QSB game still requires accounting for how the approved call
and disclosure transcript were generated, as well as Core refinement.
`QSB/JointFreshRoutes.lean` separately decomposes a *reached* undisclosed
HORS opening into exact setup-secret recovery, an H collision on the opening
and setup-secret bytes, or an R collision on distinct H outputs. Its pair is
specified by the extracted witness and sampled setup, so it is a candidate
output for a causal collision reduction. It does not itself supply that
reduction: the algorithm must produce the reached pair with all honest and
adversarial oracle calls charged, and exact-secret recovery needs its own
bound. The decomposition avoids the vacuous event that some collision exists
anywhere in an enormous sampled function.
`QSB/JointFreshCandidates.lean` enumerates every extracted signed
opening/secret pair in index order, with at most 150 pairs in the concrete
game. It also enumerates their H-image pairs for an R-collision output. A
reached route is guaranteed to occur in the corresponding list. A checked
classical postprocessor tests candidates in order and outputs a valid pair on
either collision route, after at most 150 predicate evaluations in the
concrete game. Its counter is not yet an oracle-query count. A QROM reduction
still has to charge the H-image evaluations, the predicate's H or R calls,
and the actual source extractor's cost; the postprocessor cannot be treated
as free oracle-dependent selection.
`QSB/JointFreshPostprocessing.lean` replaces those implicit evaluations with
ordered query-input traces and cached responses. Conditional on an available
extractor result and setup secrets, the concrete H-collision route needs at
most 300 further classical H calls; the R-collision route needs at most 300 H
and 300 R calls. The cached selector then makes only byte comparisons. These
are additional calls after the attack output is measured, not bounds on the
honest or adversarial work. The `Experiment` record still permits arbitrary
oracle-dependent extraction/output, so a causal QROM algorithm and its full
shared budget must be built before applying a quantum collision theorem.

Kai-Min Chung, Serge Fehr, Yu-Hsuan Huang, and Tai-Ning Liao,
[*On the Compressed-Oracle Technique, and Post-Quantum Security of Proofs of
Sequential Work*, Theorems 5.7 and 5.9](https://eprint.iacr.org/2020/1305.pdf),
give a candidate framework for the *whole* terminal event. Their Theorem 5.7
starts with one fixed relation between the algorithm's reported oracle inputs
and outputs. It bounds the square root of success probability by a sum of
compressed-database transition capacities and an output-recording term. It
does not license replacing each adaptive QSB subevent by its fixed-input
density. Theorem 5.9 handles an algorithm that reports only inputs, with an
additional terminal transition capacity; alternatively, all responses needed
to verify the relation must be reported or obtained by explicitly charged
queries. The paper's preimage and collision estimates are examples for their
own relations, not bounds for QSB.

Its Theorem 5.30 gives a generalized collision bound of order
`q³·Γ/M` for a fixed function `f(input, oracleResponse)` and a uniform
`M`-element response set, with `Γ` the largest response fiber that can match
another input's `f` value. For the product-valued tagged ideal oracle,
`QSB/TaggedOracle.lean` proves that the full 256-plus-160-bit response space
has `M = 2^416` elements. Taking `f` to be the first coordinate gives
`Γ = 2^160`, or `Γ/M = 2^-256`; taking the second gives
`Γ = 2^256`, or `Γ/M = 2^-160`. The counts hold uniformly over tagged inputs,
so they cover the distinct H-tag and R-tag collision pairs extracted above.
`QSB/TaggedFreshCollisionBridge.lean` maps the reached postprocessor's
distinct byte pairs to tagged projected collisions under explicit pointwise
byte-to-bit realization premises, retaining the additional 300/600-call
postprocessing allowances. It also constructs a deterministic tagged function
whose observed coordinates are exactly the encoded source H/R functions and
proves the collision implication directly for that function. This construction
does not provide a uniformly sampled finite-domain tagged oracle.
This identifies a *candidate* bound for those two routes only. The theorem
cannot yet be instantiated for QSB: the world-indexed game has only a
classical bounded-query causal algorithm and no coherent-query one, the
honest signing transcript may use many H queries, and coherent H/R-to-tagged
simulation needs its own charged budget. `QSB/FixedWidthOracleEncoding.lean`
bijectively encodes the source H/R responses of their proved 32/20-byte
widths into 256/160-bit registers; arbitrary byte-string query inputs still
need a finite-register encoding. `QSB/BoundedInputEncoding.lean` gives an
injective bit register when a maximum input length `B` is stipulated, with one
additional bit for the H/R input tag. The
source model has not established such a maximum for every H/R query.
`QSB/FiniteBranchingInputBound.lean` proves a weaker existential fact for one
fixed classical machine: finite fuel and finite-width replies imply that some
maximum input length covers every request it actually makes in any oracle
world. That maximum can depend on the complete fixed machine input, so it
does not provide a uniform register for attacker-chosen submissions.
`QSB/ActualQueryBitEncoding.lean` packages that existential width as a
bounded tagged-query type and gives an injective bit encoding of every actual
raw-cache request in every oracle world for the same fixed machine input.
Equality of encoded values is exactly equality of the H/R-tagged queries.
The chosen width is noncomputable and no coherent implementation is proved.
Exact setup-secret recovery and the two-puzzle route require separate
quantum arguments, and compiled-Core refinement remains open.

An applicability test for QSB has four concrete obligations:

1. Express the ideal H256 and R160 pair as one jointly sampled oracle game
   with one *aggregate* coherent-query budget. `QSB/TaggedOracle.lean` proves
   a finite-domain sampling fact: a uniform product-valued function on
   disjoint H/R input tags has constant-size fibers over every observed H/R
   pair, hence a uniform observed pair. This is an idealization, not an
   identity about real SHA-256 and RIPEMD-160. The same Lean module checks the
   computational-basis identity for an H-only or R-only XOR query implemented
   by two product-oracle calls with clean scratch. Lifting that circuit to a
   coherent-query semantics and charging its two calls in a causal attack
   game remain external. Every SHA256d inner/outer call and HASH160
   inner/outer call must preserve repeated inputs and use the same aggregate
   budget. The cited theorem has finite
   input and output sets; an application must justify a finite input-register
   domain for the attack under analysis instead of silently applying it to
   all byte strings.
2. Make setup, honest releases, disclosure choices, and the attacker's output
   one causal oracle algorithm. Count honest oracle calls or prove a separate
   advice theorem that permits the actual oracle-correlated transcript.
   `QSB/CausalQueryAlgorithm.lean` supplies the classical form of this
   obligation: one deterministic machine with an explicit query budget and
   all other randomness in its initial state produces the attack output, the
   disclosed set, and the released list from one sampled H/R pair. Its
   recorded trace has at most `budget` entries, every recorded response is
   the oracle's actual value, and the whole transcript is unchanged by any
   oracle modification outside the recorded queries. Appending the traced
   postprocessor gives at most `budget + 300` classical calls on the H route
   and `budget + 600` on the R route.
   `QSB/JointPostprocessingCausality.lean` proves that this postprocessor is
   causal once its raw candidate list is fixed: H responses select the later
   R-query inputs, and agreement on one tagged trace preserves the cached
   result and both traces. The R route records four queries per candidate.
   The world-indexed H and R postprocessors inherit this congruence under
   an explicit equality of their extracted candidate lists. The extractor
   still supplies that list without a causal construction or query charge.
   `QSB/JointCandidateMachine.lean` packages a stronger conditional route:
   one bounded classical machine returns the transcript and opening pairs;
   its `Realizes` premise equates both with the world-indexed experiment. That
   premise plus equal non-oracle initial state and agreement on recorded
   replies yields candidate equality and causal H/R postprocessing, with
   combined bounds `budget + 300` or `budget + 600` for 150 positions. The
   extractor implementation and its query charge remain to be established.
   `QSB/JointCandidateProductWorld.lean` makes the machine's initial state a
   function of coins alone in a `(coins, H/R functions)` world, so equal coins
   discharge the pointwise initial-state equality premise. Independence of
   coins and the oracle under the sampled distribution is still separate.
   `QSB/ByteMachineQueries.lean` begins
   charging the world-indexed source extractor: the byte-model run of any
   parameterized lock is causal in an explicit trace of at most 33 hash-opcode
   H/R calls; a successful run records exactly 18 H and 15 R calls. The
   Core-shaped run inherits that causality. `QSB/LockSignatureQueryBudget.lean`
   instruments the source-shaped multisignature pair scan and proves that both
   ten-key scans in a successful checked lock run attempt at most 20 pairs in
   total. `QSB/JointLegacyDigestQueries.lean` traces one modeled digest with
   zero or two H calls and proves causality for that trace. The six signature
   sites reserve 48 H calls when each verifier uses one such digest. The
   `QSB/CheckedRunQueryTrace.lean` component theorems connect the 33 calls to
   the checked run's computed signature records, bound reached digest calls,
   and prove source-shaped signature-step causality with fixed external key
   validation and ECDSA. `QSB/FullCheckedRunQueries.lean` interleaves those
   dependencies along the computed checked run and bounds the list by 81
   entries. Failed-step guards may make it conservative.
   `QSB/FullCheckedRunCausality.lean` proves the entire checked result and
   list are unchanged when a second H/R world agrees on that list, holding
   the lock, transaction, key validator, and ECDSA fixed.
   `QSB/FullCheckedRunPrefixCausality.lean` proves that the first `k`
   replies determine the next checked-run query. The cache machine in
   `QSB/CheckedRunCacheMachine.lean`, with the premise discharged in
   `QSB/CheckedRunCacheCompleteness.lean`, reproduces the checked source
   result in at most 81 actual tagged H/R queries for one fixed input
   bundle. Construction of that bundle, external checker functions,
   the repeated structural runs inside the source extractor,
   scriptSig evaluation, and honest setup/signing still need to be charged.
   `LedgerBoundRawSource.extractor` reaches `DynamicCheckedCertificate.search`
   through raw preparation and `DynamicRoundWitness.extract`; that path can
   search twice and uses several structural prefixes per candidate rather
   than one `CoreCheckedStep.run`. The 81-entry theorem therefore cannot be
   added directly as the extractor budget. External `evalScriptSig`, key
   validation, and ECDSA still lack implementations with proved finite
   oracle-call contracts.
   `QSB/CertificateStructuralQueries.lean` isolates one candidate's seven
   potential structural runs, including repeated prefixes. Its conservative
   dependency list has at most 231 hash-opcode entries and is causal for the
   structural-run results. `QSB/CertificateStructuralPrefixCausality.lean`
   turns those seven runs into a fixed-input classical cache machine with at
   most 231 actual H/R requests and the same seven structural results.
   The signature checker calls and the rest of the extractor are still
   uncharged. `QSB/CertificateSignatureQueries.lean`
   separately gives source direct-push CHECKSIGVERIFY and final ten-key
   multisignature evaluations causal digest traces of at most two and 20 H
   inputs respectively. `QSB/CertificateCandidateCausality.lean` combines
   those with the first multisignature scan and seven structural runs in an
   eager inventory of at most 299 dependencies for one candidate. Agreement
   preserves its source-model result. This inventory can reorder and include
   skipped calls. `QSB/CertificateSearchCausality.lean` combines both Boolean
   candidate inventories into at most 598 entries and preserves the
   source-model search result under agreement.
   `QSB/CertificateCandidateCacheMachine.lean` proves the 299-entry eager
   candidate list prefix-causal and constructs a fixed-input classical cache
   machine that returns the exact candidate result within 299 actual H/R
   requests. `QSB/CertificateSearchCacheMachine.lean` composes the two eager
   candidate lists and returns the exact two-trial search result within 598
   actual classical H/R requests for fixed inputs.
   `QSB/DynamicSourceExtractorCausality.lean`
   adds the repeated search and three further structural runs for one fixed
   prepared attempt, obtaining a conservative 1,295-entry dependency list
   and extractor result congruence.
   `QSB/DynamicSourceExtractorCacheMachine.lean` proves this list
   prefix-causal and constructs a fixed-input classical cache machine that
   returns the exact optional extractor result within 1,295 actual H/R
   requests. Raw parsing, scriptSig, fixed-input construction, and external
   predicates remain outside that machine.
   `QSB/DynamicRawExtractorCausality.lean` lifts the
   result through fixed raw preparation and ledger target binding, with the
   same downstream 1,295-entry bound; supplied evaluator and ledger calls
   remain uncharged. `QSB/ScriptSigTraceContract.lean` gives a conditional
   402-entry allowance for a successfully evaluated, certified scriptSig
   trace with at most 201 counted opcodes.
   `QSB/WorldIndexedScriptSigExtractor.lean` composes that contract with raw
   extraction: after successful preparation its analytic list has at most
   1,697 entries and preserves the extractor result under oracle agreement.
   Failed scriptSig evaluations are not bounded by the success-only cap,
   and the contract's full-list congruence is not an actual causal machine.
   `QSB/ScriptSigBoundedCausalContract.lean` adds an all-run cap on the
   supplied `reached` list and one-step trace causality as explicit
   assumptions. A concrete evaluator must separately prove that this list
   faithfully covers its query-bearing execution. Under those
   stronger assumptions, `QSB/ScriptSigAllRunRawBound.lean` proves the full
   raw inventory prefix-causal and at most 1,697 entries even on failure.
   `QSB/WorldIndexedRawCacheMachine.lean` uses that inventory to return the
   exact optional raw extractor result within 1,697 classical H/R requests
   for fixed raw inputs and callbacks.
   `QSB/RestrictedScriptSigHash160.lean` witnesses the stronger contract for
   a direct-push `HASH160`/`EQUALVERIFY` fragment. Its H/R query projection
   agrees with a concrete two-request machine on success and failure after
   hashing; this is not full opcode-event trace equivalence and does not
   cover arbitrary bare scriptSig. None of these request bounds charges
   coherent queries or queries hidden in callbacks.
   `QSB/LedgerBoundRawCacheMachine.lean` adds one fixed ledger and target
   selector: binding failure returns `none` with no H/R requests, and binding
   success reuses the conditional 1,697-request raw machine. A ledger that
   varies with the oracle world or carries uncounted oracle work remains
   outside this fixed-ledger result.
   `QSB/ClassicalMachineSequence.lean` supplies a generic way to run two
   halted classical H/R machines against the same oracle pair, returning
   their two outputs with exactly concatenated query logs within `q+r`
   requests. `QSB/CausalRawExtractorSequence.lean` instantiates it with the
   conditional raw cache: a first-stage halt with complete raw input `p`
   within `q` requests yields `(p, rawResult p)` and the exact concatenated
   log within `q + 1,697` requests. A game must still establish an
   oracle-independent initial state and that this first stage constructs the
   actual QSB lock, ledger context, submission, and evaluator contract;
   a first-stage timeout needs separate fallback handling.
   The honest machine is not shown to use the sampled secrets correctly, and
   no coherent-query version exists.
3. Define one fixed, oracle-independent relation over a reported transcript,
   selected transaction, and enough oracle input/output pairs to verify the
   *reached* seven opening equations and both signature-puzzle routes. It must
   include equal pin/final key bytes, released keys, ECDSA message retargets,
   shared SHA256d inputs, and the actual authorization projection. An
   unrestricted global collision property is too broad: `DynamicRetarget`
   shows it is already true for every fixed-width whole function, even when
   the reached transaction has no collision.
4. Bound the relation's per-query compressed-database transitions, including
   output verification, by explicit local response sets. A small DER target
   density or an at-most-eight ECDSA digest fiber for a *fixed* key does not
   establish those transition capacities when keys, targets, and disclosures
   depend on earlier oracle responses. `OracleDependentSelection` gives finite
   counterexamples to that shortcut. `QSB/TaggedLocalResponses.lean` checks
   the paper's local response sets for the two projected collision relations
   only: a further query against a recorded database of length `s` collides
   with a recorded entry for at most `s·2^160` of the `2^416` responses on the
   H projection and at most `s·2^256` on the R projection, so the paper's
   per-query estimates `Γ/M` and `s·Γ/M` are `2^-256` and `s·2^-256` for H
   and `2^-160` and `s·2^-160` for R. These are the classical counting
   inputs to Example 5.28's capacity estimate, not the transition-capacity
   theorem itself, and they say nothing about the oracle-dependent key,
   target, and disclosure selections of the two-puzzle route or about the
   exact-secret route. Only after this bound can Theorem 5.7 or
   5.9 yield a nontrivial `εjoint` for `JointRawSourceWorld`.

The current Lean reduction establishes an event inclusion and conditional
measure inequality. It supplies none of these four QROM obligations; in
particular, no numerical QSB query bound follows from the cited theorem yet.

## Elliptic-curve threat

Peter Shor,
[*Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*](https://arxiv.org/abs/quant-ph/9508027).

The proposed game removes elliptic-curve discrete-log hardness as a security
assumption. The Lean scalar-equation lemmas are compatible with that choice;
they do not formalize Shor's algorithm or a quantum circuit.

## Bitcoin consensus sources

- [Core v27.2 interpreter](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp): CHECKMULTISIG result handling, optional NULLFAIL/CLEANSTACK policy checks, FindAndDelete and legacy signature rules. The legacy `SIGHASH_ALL` serializer includes ordered inputs (blanking other input scripts), all outputs, version and locktime; the checker removes the signature's final hashtype byte, computes that sighash, then verifies the ECDSA signature. This source reading does not prove that equal verification for a fixed key forces an equal sighash: opposite ECDSA recovery points permit distinct message scalars.
- [Core v27.2 consensus API flags](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/bitcoinconsensus.h): flags used by the app adapter.
- [Core v27.2 strict DER and hashtype checks](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp): the trailing hashtype restriction is guarded by `STRICTENC`, separately from `DERSIG`. The local 256-case Core sweep confirms that the pinned consensus adapter accepts all trailing bytes with recovered verification keys; this concerns isolated scripts, not QSB's complete lock.
- [Core v27.2 consensus API flags](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/bitcoinconsensus.h): `VERIFY_ALL` includes `DERSIG` and `NULLDUMMY`, but does not include `MINIMALDATA`. [Core v27.2 CScriptNum](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/script.h) allows at most four bytes for ordinary numeric opcodes and interprets the last byte's high bit as a sign; `QSB/ByteIndex.lean` mirrors those byte rules but is not a compiled-binary refinement proof.
- [Core v27.2 policy flags](https://github.com/bitcoin/bitcoin/blob/v27.2/src/policy/policy.h): `NULLFAIL` and `CLEANSTACK` are in standard policy, not the listed mandatory verification flags. The QSB output uses an unusual bare script and the structural fixture leaves a large stack; direct miner acceptance must be kept separate from default relay policy.
- [Core v27.2 public-key parser](https://github.com/bitcoin/bitcoin/blob/v27.2/src/pubkey.h) and [secp256k1 key parsing](https://github.com/bitcoin/bitcoin/blob/v27.2/src/secp256k1/src/eckey_impl.h): legacy key encodings included in the attacker model.
- [Core v27.2 `CPubKey::Verify`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/pubkey.cpp#L267-L282), [secp256k1 ECDSA verifier](https://github.com/bitcoin/bitcoin/blob/v27.2/src/secp256k1/src/ecdsa_impl.h#L195-L264), and [32-byte message conversion](https://github.com/bitcoin/bitcoin/blob/v27.2/src/secp256k1/src/secp256k1.c#L444-L457): Core normalizes high-S before the low-S verifier; the verifier rejects infinity and tests x=`r` and, when in range, x=`r+n`, after reducing the message to a scalar. The Lean sign-adjustment and affine-fiber theorems still require a Core-to-curve representation proof.
- [Core v27.2 official checksums](https://bitcoincore.org/bin/bitcoin-core-27.2/SHA256SUMS): archive identity for the native experiments.

These sources fix the interpreter used for this analysis. No claim is made that
an API flag set dynamically tracks current or future mainnet activations.

## Unsupported shortcuts explicitly rejected

- “SHA-256 therefore 128 quantum bits” ignores HASH160, transcript reuse,
  structured subset search, and actual target density.
- “The GPU checks two rounds” does not show consensus enforces both.
- “The server rejects changed outputs” does not constrain an attacker submitting
  directly to miners.
- “No attack found” is not an upper bound on attack success.
- “Lean compiled” establishes only the exact formal statements and premises.
