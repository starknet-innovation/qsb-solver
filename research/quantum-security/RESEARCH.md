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
`history_event_public_case` additionally takes a supplied public-key set.
It routes an unmatched pair using an already disclosed key to the finite
digest-target branch, even without an approved-call record. The set's
completeness and any quantum oracle-query history remain external premises.

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
