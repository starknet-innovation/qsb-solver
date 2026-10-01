# Proof status and implementation boundary

This file distinguishes checked mathematics, computational experiments, and
unresolved claims. There is no theorem of full QSB unforgeability yet.

## Checked Lean statements

`QSB.lean` imports the modules and prints dependencies for the reported results.
The build and dependency outputs are retained under `evidence/`.

| Module | Result | Scope / missing connection |
|---|---|---|
| Disclosure | Valid openings either open an undisclosed indexed target or use only disclosed indices | Assumes an extracted set of distinct commitment positions and actual hash equalities. |
| Disclosure | With one disclosure of the same cardinality, no fresh opening implies exactly the same signed set | Does not prove that Script enforces the cardinality or that a different message cannot reuse this set. |
| Disclosure | Fewer disclosed positions than required implies a fresh target opening | A structural implication, not a query-success bound. |
| Disclosure | Additional disclosures preserve coverage | Supports union accounting, including unmined authorizations. |
| Extraction | An extracted enforced round implies a fresh opening or covered puzzle solution | `ExtractedRound` premises are explicit. It is not Bitcoin acceptance, and cannot presently be supplied for round 1. |
| Extraction | Novel-message version targets owner-forbidden projections and excludes assembled transactions whose QSB unlocking material was already released | Necessary because replay or harmless mutation of an authorized release may otherwise satisfy an overbroad puzzle event with certainty. Release includes unmined and helper-unsigned material. |
| Probability | Event inclusion and two primitive bounds imply their sum bounds the bad event | Arbitrary measure; no independence assumed. A probability interpretation requires a normalized terminal distribution. |
| Probability | Same result with a separately bounded model-gap event | An unknown/structural implementation gap is not negligible and cannot be assigned zero. |
| Probability | A finite union of vault-failure events is bounded by the sum of their per-vault bounds | No independence premise. Each bound must charge the adversary's shared global hash-query budget. |
| Probability | If each of 300 commitment-encoding events has probability at most `390405/2^65`, their union has probability at most `300·390405/2^65` | No independence premise. The per-commitment marginal bound and correspondence to Core's parser are explicit external obligations; this is not an extraction-gap or spend-probability bound. |
| Random-function setup | If a whole finite function `R : X → Y` is sampled uniformly and independently of setup material `ξ`, then `R(source ξ)` hits any fixed target set with exactly its target density. For any finite collection of setup-dependent sources addressing the same `R`, their union has at most the sum of those densities. | `QSB/RandomOracleSetup.lean` proves exact count identities and the shared-function union inequality. In the candidate idealization, `ξ` may include the honest secrets and H256 oracle, while `R` represents R160. The model excludes prior information about `R` in `ξ` and does not model adaptive or quantum access, the exact Core DER target, or spend acceptance. |
| Nonce | The publicly computable scalar (s*k-z)/r satisfies the fixed-signature equation | Field algebra with r nonzero; no discrete-log hardness. |
| Nonce | A fixed recovery point and public key determine the scalar message | Does not conflate the several possible recovery points or a hash integer with its residue modulo N. |
| Nonce | Fixed message/recovery point determine the key scalar when r is nonzero | secp256k1 group/encoding instantiation is not yet formalized. |
| Nonce | Given a fixed recovery point, any new message has a publicly computable verification key | Formalized over a field module. It explains why the hash-derived puzzle signature alone cannot authorize the destination. Bitcoin group parsing and encoding remain open. |
| Nonce | In the fixed-recovery-scalar field model, one key can satisfy both fixed signatures exactly when their publicly computed recovered scalars coincide | Gives an explicit equality-case equation; real sighash correlations, alternate recovery points and key-byte encodings remain unproved. |
| Nonce | For a fixed signature and key, each admissible recovery point determines one message group element; the finite set of message targets has cardinality at most the recovery-point set. Opposite points give distinct targets unless their scalar multiples are 2-torsion. | `QSB/Nonce.lean` proves the field-module algebra. It does not prove which secp256k1 points Core admits, how SHA256d digests reduce modulo the group order, or a quantum success bound. A public secp256k1 fixture checks that the same signature/key verifies two distinct scalars; no Bitcoin preimage or spend is shown. |
| Nonce high-S normalization | If a verifier negates S, the corresponding recovery equation uses the opposite recovery point. With a recovery-point set closed under negation, a normalized verification lands in the original-DER-S message-target set. | `QSB/Nonce.lean` proves both algebraic statements. Core 27.2's `CPubKey::Verify` normalizes high-S before secp256k1 verification, and one isolated pinned-Core high-S fixture accepts the same key and ALL digest. Mapping all Core-accepted signatures and parsed points into a sign-closed Lean recovery set remains unproved. |
| Recovery candidates | Since the secp256k1 field prime is below twice its group order, an admissible x-coordinate reducing to `r` is either `r` or `r+n`. Lean now proves the at-most-two-affine-points-per-x bound from a field-valued curve equation and uniqueness of `(x,y)` coordinates, giving at most four recovery points and four message group-element targets under those premises. | `QSB/RecoveryCandidates.lean` proves the modulus arithmetic, the generic square-root/fiber theorem, and the conditional cardinality bound. Connecting Core's parsed recovery points to unique affine coordinates on the secp256k1 field, excluding infinity and invalid points, and Core digest conversion remain external. This is target-set size accounting, not a quantum success bound. |
| Wire digest targets | Since `2^256 < 2n` for the secp256k1 group order, each admitted message residue has at most two 256-bit digest representatives. Under the conditional four-message-target bound, at most eight unsigned wire digest values can verify one fixed signature/key. A curve-equation version discharges the abstract fiber premise; a separate theorem puts a digest in this finite set when its reduction equals an admitted message target. | `QSB/RecoveryCandidates.lean` proves this arithmetic and finite-set accounting. The map from Core's ECDSA group message to a scalar residue and Core's digest conversion are explicit premises. The target set may be correlated with the joint hash oracles; no quantum hit probability is claimed. |
| Concrete ordered-output wire encoding | The source-shaped CompactSize count, nonnegative eight-byte little-endian value, length-prefixed script, and recursive output-list encoding round-trip and are injective for count/script lengths below `2^64` and values below `2^63`. | `QSB/OutputCodec.lean`, `QSB/WireIntegers.lean`, and `QSB/WireOutputs.lean` check the byte functions and valid-domain proofs. Equality with Core's compiled C++ writers, the actual consensus monetary domain, and Core's complete transaction serialization are not formalized. Lean boundary vectors match the pinned app's serializer; two 253-boundary transactions pass the Core adapter. |
| Source-shaped complete ALL preimage parser | For every valid source-shaped wire transaction, a full parser recovers version, prepared ordered inputs, ordered outputs, locktime, and the appended ALL word. The serializer is injective on those valid fields. BASE/ALL preparation blanks original input scripts and substitutes the selected scriptCode; a second theorem proves that this preparation preserves the ordered prevout and sequence fields. Thus even with different scriptSigs, selected inputs, and scriptCodes, equal source-shaped preimages imply equal version, ordered outpoints and sequences, outputs, and locktime. One 139-byte Lean encoding matches the pinned app's baseline preimage; a second fixture checks the prepared result with different original scriptSigs. | `QSB/SighashAllWire.lean` and `QSB/SighashAllWireFixture.lean` prove this on the finite-width wire domain. A fixed ledger-resolution function maps the committed outpoints to previous outputs, so equal preimages also imply equal `Game.Projection` in that same ledger context. The Core C++ serializer, selected `scriptCode` from arbitrary accepted witnesses, and actual ledger resolution have not been refined to this model. |
| Source-shaped legacy hash-type serializer | The Lean serializer now branches on the low five hash-type bits and ANYONECANPAY flag: NONE omits outputs, SINGLE writes null outputs before the signed index, other input sequences become zero in those branches, and ANYONECANPAY retains only the selected input. The out-of-range SINGLE branch has no preimage and its raw `uint256::ONE` digest bytes are recorded separately. Type `0x01` provably equals the earlier ALL preimage. Five exact Lean byte fixtures cover ALL, NONE, in-range SINGLE, SINGLE with ANYONECANPAY, and an unknown-base ALL-like type with ANYONECANPAY. | `QSB/LegacySighashWire.lean` and its generated fixture cover the source-shaped wire semantics, not compiled Core C++ or actual ECDSA. The fixture uses an independent Python serializer separately checked against all 500 pinned Core 27.2 published vectors (467 ALL-like, 16 NONE, 17 in-range SINGLE; 229 ANYONECANPAY); no published vector exercises the out-of-range SINGLE exception, which has separate isolated native evidence. `scriptCode` after FindAndDelete and CODESEPARATOR removal, valid transaction fields, and actual consensus checker linkage remain external. |
| Conditional ALL authorization binding | An attempted transaction outside the authorized semantic-projection set has a distinct source-shaped ALL preimage from every approved release in the same fixed ledger context, including forbidden changes to prevouts, sequences, version, locktime, outputs, or the fee induced by those prevouts. Under explicit admitted-recovery-point, digest-reduction, and fixed-key verification premises, its unsigned digest lies in a target set of at most eight values. | `QSB/SighashAllWire.unauthorized_sourceAll_distinct_preimage` and `QSB/SighashBinding.source_all_forbidden_projection_wire_digest_target` extend the earlier changed-output statements. This is finite target accounting, not a query-success bound. Core preimage identity, actual key verification and recovery points, ledger binding, and a joint-oracle quantum bound remain external. It does not prove universal old-key rejection. |
| Parameters | C(142,1)=142; C(143,2)=10153; C(150,9)=82947113349100 | Honest distinct-subset combinatorics only. Does not restrict malicious stack choices. |
| Parameters | With `d` disclosed distinct final-round positions, the abstract covered-choice count `C(d,7)·C(143,2)` is monotone; it is 10,153 at `d=7` and 34,845,096 at `d=14` | Counts index pairs under the shaped pool model; neither option count nor the formula is a success probability. |
| Parameters + Game | If each signing record releases at most seven positions, the covered-choice count after `r` records is at most `C(min(150,7r),7)·C(143,2)` | Conservative across all records, including unrelated vaults; assumes each record's asserted release cap and still gives no QROM success bound. |
| Parameters | DER count expression is exactly 2449811572532375301807922306615930029710387026976812229606768640, density `780555 / 36893488147419103232`, and lies between 2^210 and 2^211 | Closed arithmetic about an explicit expression; bijection to a formal BIP66 parser remains to be proved. This is not a QROM success bound. |
| Parameters | The analogous 20-byte DER syntax expression has density `390405 / 36893488147419103232`, about 2^-46.43 | Relevant to accidentally DER-shaped HASH160 commitments. Independent uniform R160 setup marginals now have a separate checked count theorem, but parser correspondence and whether such a value is exploitable in a valid setup remain open. |
| Selection | OP_MIN plus a nonnegative successful roll yields its stated bounds | Large values clamp; there is no inferred upper-bound rejection. |
| Selection | A bounded, 20-byte comparison selects the pool if earlier items have different lengths | A local loop-invariant building block, not the completed Script extraction. |
| Selection | Removing a tagged pool position preserves distinctness | Tags are positions; hash collisions are not excluded. |
| Selection | A successful nine-step abstract without-replacement traversal partitions into seven signed and two disjoint bonus tags | Does not prove that every accepted production Script execution behaves like this traversal. The exact stack/byte invariant is still missing. |
| Generated layout | A false first `CHECKMULTISIG` result leaves the symbolic trace accepting; the final result controls the top of stack | Generated from 880 actual Config A instructions and a disposable canonical witness, with signature outcomes supplied explicitly. This is not an arbitrary-witness Script theorem or a solved hash puzzle. |
| Generated layout | The trace has 201 counted operations and 569 final stack cells; the first false result remains at depth 285 | Confirms the structural source reading for this fixture. ScriptNum parsing, signature semantics and actual byte sizes are outside this model. |
| Generated layout | With first signed index 152 and one inserted external symbolic 20-byte cell, the first selection's `OP_ROLL` reaches that cell | A checked **local counterexample** to inferring pool confinement from `OP_MIN` alone. The complete malformed probe fails symbolic execution; it is not a forged or accepted witness. The trace ends after instruction 315, the first selection roll. |
| Generated layout | An externally chosen symbolic commitment can match the first `HASH160` comparison; this probe then fails at the second index `OP_MIN` | Passing one HORS comparison does not imply the selected commitment came from the lock. The global stack invariant may still reject this malformed witness. |
| First signed overshoot | The full generated byte-model program rejects initial stacks with arbitrary pinning-key bytes, any unparsable first index or any first index parsing to a ScriptNum value at least 152, and any post-index continuation stack. Equivalently, a successful modeled run with this top-stack layout has a parsed first-index value below 152. The first two signature outcomes are granted true; later outcomes and hash functions are arbitrary. | `QSB/FirstOvershoot.lean` derives the 302 lock pushes and pinning stack effect, then proves the first `OP_MIN` clamps parsed values at least 152, including nonminimal encodings accepted by the model. An unparsable index fails `OP_MIN`; an empty continuation fails the external-cell roll. After an external marker, fewer than eight further cells fail the opening roll; otherwise a marker mismatch fails the first hash comparison. A match leaves the retained 152 to roll a lock commitment into a signature position; the next fixed 301-roll then selects another 20-byte lock commitment, which `OP_MIN` rejects as a four-byte ScriptNum. Long tails reject at the modeled 1000-cell limit during pinning, lock pushes, or early selection. This is a top-stack family, not arbitrary-scriptSig extraction or Core refinement. |
| First signed lookup map | The 150 generated cells at depths 152–301 are 20-byte commitments; the 152 shallower fixed cells are not 20 bytes. A roll at depth `153+i` for `i<150` selects exactly fixed commitment `152+i`, independently of the lower witness stack. With a retained cell of at most four bytes, any HASH160 match at a roll index at most 302 must identify one of those commitments. | `QSB/FirstIndexMap.lean` proves these literal-byte and list-roll facts; `QSB/ByteMachine.lean` proves that successful modeled `OP_ADD` parses both inputs within the four-byte limit. The output-index link is proved below for the specified initial top-stack layout; arbitrary `scriptSig` and later selection sources remain open. |
| First signed in-range indices | For every nonnegative parsed first index below 152, the byte model's first `OP_MIN` yields its canonical encoding; the following `OP_ADD` produces offset `151+n`, and the modeled `OP_ROLL` uses that depth. From the generated first-index prefix, this holds for any lower tail that fits the 1000-cell bound. If that roll puts a `HASH160` output on top, then `n=2+i` for some `i<150` and the selected cell is fixed commitment `152+i`. Values 0 and 1 cannot produce that hash match. | `QSB/FirstNumericRange.lean` checks all 152 serializer/parser cases and connects the byte steps to the fixed-region origin theorem. It does not cover negative indices, an arbitrary accepted `scriptSig`, Core refinement, or later HORS selections. |
| First signed negative near-range | For every parsed first index from −1 through −151, the byte model's first `OP_MIN` retains that value; `OP_ADD 151` produces a nonnegative roll depth from 150 down to 0. None of those selected cells can match a 20-byte `HASH160` output, even with arbitrary lower stack cells. | `QSB/FirstNegativeRange.lean` checks all 151 encodings, the generated first-index prefix, arithmetic steps, and modeled roll. The all-negative argument below covers larger magnitudes under explicit successful-step premises. Arbitrary accepted `scriptSig`s and Core refinement remain open. |
| First signed all-negative source | For any negative parsed first index, successful local `OP_MIN`, `OP_ADD 151`, and `OP_ROLL` steps cannot leave an opening's `HASH160` output on top. Parseable encodings of negative values remain nonpositive; the subsequent sum and reparsing give a roll depth at most 151, where no cell can match that output. | `QSB/ByteIndexSign.lean` and `QSB/FirstNegativeAll.lean` prove this for arbitrary magnitudes and arbitrary lower stacks in the byte model. The theorem has explicit successful-step premises; it does not yet extract them from every accepted full-script or Core execution. |
| First signed below-cap source | For any parsed first index below 152, if the reached byte-model `OP_MIN`, `OP_ADD 151`, and first signed `OP_ROLL` leave an opening's `HASH160` output on top, that index must be `2+i` for `i<150`, and the selected cell is fixed commitment `152+i`. This includes nonminimal raw encodings, negative values, and arbitrary lower stacks. | `QSB/FirstNegativeAll.below_cap_first_roll_has_commitment_origin` combines the positive and all-negative local theorems. The accepted-run bridge below discharges these local premises for the specified top-stack family, but arbitrary `scriptSig`/Core refinement remains open. |
| Accepted first signed origin | For the initial byte stack `nonce :: puzzle :: rawIndex :: arbitraryTail`, with the two pinning outcomes granted true, every successful run of the full 880-op generated byte program has a parsed first index `2+i` for `i<150` and a first HASH160 comparison against fixed lock commitment `152+i`. This holds for arbitrary hash functions satisfying output widths, later signature outcomes, and lower stack bytes. | `QSB/FirstAcceptedOrigin.accepted_first_signed_commitment_origin` derives the local MIN/ADD/roll and `HASH160; EQUALVERIFY` facts from successful execution, then combines the overshoot and below-cap theorems. It proves only the first signed selection for this top-stack layout. Arbitrary `scriptSig` execution, all later selections, signature checking, and Core refinement remain open. |
| Arbitrary initial byte stack, first origin | Starting the generated byte-model lock at operation count zero with any byte stack and any Boolean signature-outcome list, success forces at least three top stack cells, true outcomes for both pinning checks, a parsed first index `2+i` for `i<150`, and a first matching HASH160 cell at fixed lock commitment `152+i`. | `QSB/PinningShape.accepted_arbitrary_initial_stack_first_origin` proves this by inverting the pinning prefix, rejecting a two-cell post-pinning stack at the first 302-roll, then applying the accepted first-selection theorem. This is arbitrary initial **byte-model** state, not arbitrary real `scriptSig`/Core execution or a proof about later selections. |
| Arbitrary scriptSig evaluator, first origin | For every partial function from scriptSig values to initial byte stacks, a successful composition with the generated byte-model bare lock has the same first lock-commitment origin and true modeled pinning outcomes. | `QSB/BareBoundary.accepted_bare_composition_first_origin` composes the previous theorem with an arbitrary preceding evaluator. It assumes the generated lock itself runs in `ByteMachine` with a fresh opcode counter. Core-to-`ByteMachine` refinement and actual signature outcomes remain unproved. |
| Final byte suffix, arbitrary stack | For any underlying byte stack and any successful, truthy run of the whole generated byte program, the final `CHECKMULTISIG` is reached with both raw count operands `[0x0a]` (numeric 10), and its supplied outcome is true. | `QSB/ByteFinalCounts.accepted_true_whole_program_final_counts` checks the literal final suffix, all ten raw index decodings and push/roll effects, count-cell preservation, and the final Boolean stack result. It does not identify the ten signature/key bytes or prove that the true outcome corresponds to Core's DER, FindAndDelete, sighash and ECDSA checks. |
| Final signature/dummy cells, arbitrary stack | If the pre-suffix stack is `first :: rest`, each of `rest[0..9]` is preserved into the corresponding final CHECKMULTISIG signature slot, and `rest[10]` becomes its dummy slot. Any successful modeled final suffix forces `rest[10]? = some []`; this also proves that source cell exists. | `QSB/KeyRolls.final_witness_option_origin` proves the generic roll mapping; `QSB/ByteFinalCounts.accepted_final_setup_witness_option` and `accepted_final_suffix_source_dummy_empty` check the generated raw-index byte suffix and its modeled NULLDUMMY rule. These identify source positions in the pre-suffix stack, not their provenance from the earlier signed/bonus selections. Core refinement and actual signature verification remain open. |
| Post-bonus source to final signatures | Starting from any byte stack immediately after the final bonus `OP_ROLL` (instruction 849), every successful modeled execution of the remaining generated program reaches CHECKMULTISIG with its ten signature slots equal to that stack's cells 0–9 and its dummy slot equal to cell 10. Success forces cell 10 to exist and be empty. | `QSB/ByteLatePuzzle.accepted_generated_final_witness_origins` and `accepted_generated_postbonus_dummy_empty` prove this through the exact seven-opcode late puzzle and final key-roll suffix, without assuming a canonical earlier stack or outcome values. The full-program theorem below now establishes earlier source roles in `ByteMachine`; Core's FindAndDelete/sighash/ECDSA rules and refinement remain open. |
| Last bonus NULLDUMMY source, arbitrary stack | For any successful modeled suffix after the last bonus roll, a decoded last index below 10 requires the pre-roll cell at depth 10 to be empty; an index at least 10 requires the pre-roll cell at depth 9 to be empty. If depth 10 is nonempty, a successful last index must be at least 10. | `QSB/FinalBonusBoundary.lean` composes a generic list-roll origin theorem with the post-bonus dummy theorem. It assumes successful execution and a decoded nonnegative index, not a canonical earlier stack. It does not establish the two source-cell values from arbitrary earlier selections. |
| Two-bonus bridge, arbitrary shallow cells | The generated fixed roll and cap between the two final-round bonus rolls preserve all shallow pre-first-bonus cells with a one-cell shift. If the pre-first-bonus cells at depths 9 and 10 are both nonempty, a successful modeled continuation requires the first bonus index to be at least 9 and the last to be at least 10. | `QSB/ByteBonusBetween.successful_two_bonus_index_bounds` proves this for arbitrary bytes and supplied outcomes. The later full-program theorem now supplies those nonempty premises in `ByteMachine`; Core refinement and actual signature verification remain open. |
| Generated second-round dummy pool | The 152 generated initialization pushes put the nonce and empty dummy above 150 nonempty dummy bytes over any earlier stack within resource limits. Any seven pool-only signed rolls, in any order, leave nonempty cells at the two pre-first-bonus source depths, so a successful modeled two-bonus suffix must use indices at least 9 and 10 respectively. | `QSB/PoolRollInvariant.lean` checks the literal bytes and generic list-roll property. `QSB/FinalSignedChain.lean` proves pool-only behavior for all seven signed blocks in every successful **byte-model** run. `QSB/FinalBonusAccepted.lean` now carries those source cells through the reached bonus suffix; Core refinement remains open. |
| First final-round signed lookup boundary | In the exact generated second-round initialization, the first signed lookup at depth `151+n` selects a 9-byte dummy for `n=0,1`, a 20-byte locking-script commitment at position `n-2` for `2≤n<152`, and the prior round's CHECKMULTISIG result for `n=152`. Depths 0–151 contain only a short retained ScriptNum, the 55-byte nonce, the empty cell, and 9-byte dummies. The generated comparison rejects all those depths and capped 152; at depths 153–302 it matches an opening's HASH160 to the selected commitment. | `QSB/FinalSignedBoundary.lean` proves the literal first-selection source map and local byte-model comparison consequences for arbitrary preceding stack tails and hash functions with 20-byte HASH160 outputs. The seven-block whole-program byte-model composition is stated below; Core refinement remains open. |
| Accepted first final-round signed commitment origin | Every successful full 880-op generated byte-model run from any initial byte stack and supplied signature outcomes forces the first final-round signed raw index to parse as `2+i` for some `i<150`; the generated commitment at `i` equals `HASH160(opening)` for an opening consumed by the exact generated comparison. Nonminimal raw index encodings are included. | `QSB/FinalSignedAccepted.accepted_whole_program_first_final_commitment_origin` proves this first-selection statement; the chained theorem below now covers all seven selections in `ByteMachine`. Actual Core signature outcomes and Core-to-byte-model refinement remain open. |
| Seven final-round signed blocks, reached-block transition | All seven literal 13-opcode blocks follow the same fixed raw roll, MIN/ADD, commitment roll, preimage roll, HASH160 comparison, and paired dummy roll pattern. For any block `k`, given its current gathered/dummy/commitment pool shape and original-index alignment, successful byte-model execution itself forces the raw index to parse as `2+k+j` for a current pool position `j`, equates the actual opening's HASH160 with that commitment, and removes the commitment and matching dummy. It preserves both invariants for the next block. The raw comes from earlier tail offset 283; the opening comes from tail-after-raw offset `291-k`. | `QSB/FinalSignedLoop.accepted_signed_block_transition` derives the in-range index and paired transition from successful execution of **one reached block**, including negative and nonminimal ScriptNum cases. `QSB/FinalSignedChain.lean` composes the blocks for a full byte-model run. |
| All seven final signed HORS openings, arbitrary byte stack | Every successful full 880-op generated byte-model run from any initial byte stack and supplied signature outcomes consumes seven actual openings whose HASH160 outputs match seven distinct original generated second-round commitments. | `QSB/FinalSignedChain.accepted_whole_program_final_signed_openings` inverts the preceding CHECKMULTISIG and initialization pushes, composes all seven literal signed blocks, records each original commitment index, and proves their distinctness. The later full-program theorem classifies bonus and final signature sources. Supplied signature outcomes and arbitrary Bitcoin Core scriptSig/consensus refinement remain open. |
| Final bonus bounded depths, arbitrary byte stack | Every successful full generated byte-model run forces the decoded first bonus roll depth into 9–152 and the decoded last bonus roll depth into 10–152, alongside the seven distinct signed HORS openings. | `QSB/FinalBonusAccepted.accepted_whole_program_signed_and_bonus_bounds` carries the post-signed nonempty source cells through the exact first fixed roll/cap, both bonus rolls, and final NULLDUMMY-enforcing suffix. The upper bounds use the generated `OP_MIN` caps and allow nonminimal raw ScriptNums. The later byte-model theorem classifies both source branches, including the commitment at depth 152. Core signature validity and refinement remain open. |
| First final bonus reached-roll source map | From a reached seven-signed pool-shaped state, first bonus depths 9–151 select a surviving 9-byte generated dummy, while depth 152 selects the first surviving 20-byte HORS commitment; the arbitrary earlier tail is unreachable. | `QSB/FinalBonusAccepted.first_bonus_source_map`, `first_bonus_source_width`, and `accepted_first_bonus_source_role` prove the layout and actual moved top byte after the exact fixed raw roll/cap/bonus roll. `QSB/FinalBonusSecond.accepted_whole_program_bonus_source_trace` now composes this into an arbitrary full byte-model run. Core signature validity remains open. |
| Second final bonus source, arbitrary byte stack | If the first bonus takes a dummy, second depths 10–151 take surviving dummies and depth 152 takes the first surviving commitment. If the first takes that commitment, all second depths 10–152 take dummies. Thus at most one bonus selection can take a commitment in a completed generated byte-model run. | `QSB/FinalBonusSecond.second_bonus_source_map` proves the two list branches; `accepted_second_bonus_source_role` tracks the actual moved byte through the intervening fixed roll and cap. `accepted_whole_program_bonus_source_trace` reaches both post-bonus states from any initial byte stack and supplied signature outcomes, records their exact selected-byte equations, and retains the seven distinct signed HORS openings. Core signature checks and the DER-shaped setup event remain open. |
| Final CHECKMULTISIG signature-source roles, arbitrary byte stack | Every successful full generated byte-model run reaches the pre-CHECKMULTISIG state with ten signature-source cells in order: second bonus, first bonus, seven gathered generated dummy bytes, and fixed nonce; the next dummy cell is empty. The gathered dummies correspond in reverse order to the seven traced original HORS positions. The two bonus bytes obey the classified dummy/commitment source branches. The sole possible bonus commitment is identified by an original HORS position absent from those seven openings. | `QSB/FinalSignedChain.accepted_ordered_blocks` tracks gathered dummy identity through each signed erasure; `QSB/FinalBonusSecond.accepted_whole_program_final_signature_origins` carries that identity and the exact two-roll shallow-cell invariant to the reached pre-CHECKMULTISIG state. Signature outcomes remain supplied Booleans; this is not Core DER/FindAndDelete/sighash/ECDSA verification or a quantum success bound. |
| Conditional bonus setup exception | If both reached final bonus signature slots satisfy an externally supplied syntax predicate, and all 150 generated second-round HORS commitments fail that predicate, both bonus depths are strictly below 152. | `QSB/FinalBonusSecond.no_bonus_commitment_of_signature_syntax` derives this from the same full byte-model run, its exact pre-CHECKMULTISIG prefix, and the unopened commitment origin. The model does not establish the syntax premise: Core signature parsing and successful multisignature verification still require refinement. The hash-distribution probability of the bad setup remains a separate obligation. |
| Final bonus setup syntax probability | If each of the 150 second-round commitments has actual parser-syntax marginal at most `390405/2^65`, the probability that any of them is syntax-valid is at most `150·390405/2^65`. | `QSB.der20_final_bonus_setup_union_bound` is a checked measure union bound without independence. The marginal premise and Core parser/count correspondence remain external; this covers only this final bonus setup event, not all extraction gaps or unauthorized spends. |
| Core-shaped matching interface for bonus syntax | If the reached final ten-signature/ten-key scan succeeds under a per-pair verifier whose success entails signature syntax, and no generated second-round commitment satisfies that syntax, both bonus depths are below 152. | `QSB/FinalBonusSecond.matched_final_signature_has_syntax` derives syntax of each slot from the equal-count matching loop. `no_bonus_commitment_of_matching_verifier` composes it with the full byte-model source trace. Relating the external pair verifier and scan result to Core's actual parser, FindAndDelete, sighash, and ECDSA remains open. |
| Source-shaped strict DER predicate and encoding gate | A 20-byte byte string accepted by the Lean strict-DER predicate has positive R and S byte lengths summing to 13, with the six required DER header/length bytes. The modeled `VERIFY_ALL` encoding gate accepts the empty signature as a special case; on nonempty bytes it equals the strict-DER predicate. | `QSB/DERSyntax.lean` translates Core 27.2 `IsValidSignatureEncoding` and the empty-signature branch of `CheckSignatureEncoding`. The 73-case pinned-Core differential corpus below corroborates this behavior, but is not compiled-Core equivalence or a full cardinality/bijection theorem for the earlier DER-20 count expression. |
| Core-ordered DER source model | A second source-shaped model performs Core 27.2's 14 strict-DER checks in early-return order, including the bitwise 0x80 sign tests. Lean proves it equals `DERSyntax.valid` for every byte list and that all indexed reads reached on an accepted input are in bounds. | `QSB/CoreDEREncoding.lean` checks the translation-to-translation correspondence. The models share the source reading; this is not a refinement proof for compiled C++ or an ECDSA-success theorem. |
| Conservative DER-20 target count | At most `12·256^14` of the `256^20` twenty-byte strings pass the Lean strict-DER predicate, giving density at most `12/256^6`. With 150 setup-selected inputs to one independently sampled uniform R160 function, the generic checked union theorem yields at most `150·12/256^6` for any such syntax hit. | `QSB/DERHeaderBound.lean` proves an injection that removes six constrained byte positions, including the R-length-dependent S tag and length, plus output-space cardinality, scaled density, and a generic bounded-target random-function union theorem. This bound avoids the unproved exact `390405/2^65` parser count, but still assumes independent random-function setup and does not cover quantum queries, Core predicate refinement, or unauthorized spends. |
| Literal final-round setup | None of the 150 second-round HORS commitments in the one disposable generated lock passes the source-shaped strict DER predicate. Under a successful ten-pair scan with a DER-sound verifier, both bonus depths are therefore below 152 for that lock. | `QSB/FinalBonusDER.lean` checks all 150 literal bytes with kernel reduction and specializes the conditional matching theorem. It is not a statement about every generated vault; Core binary refinement and a tighter or more realistic setup bound remain open. |
| Nine final-round source positions, conditional full byte-model run | In one accepted run of the literal generated byte model, a successful DER-sound ten-pair final scan implies that the seven signed HORS openings and both reached bonus dummy signatures use nine distinct original positions. The theorem identifies all nine actual pre-CHECKMULTISIG signature slots by original index, plus the fixed nonce slot and empty NULLDUMMY cell. | `QSB/FinalBonusIndices.lean` uses the surviving-position permutation, both actual roll indices, the gathered-dummy trace map, and the literal lock's no-DER-commitment fact. The successful scan and DER-sound verifier remain external premises; neither follows from supplied Boolean signature outcomes. This is not Core acceptance or a quantum probability bound. |
| Literal final dummy-byte distinctness | The 150 generated final-round dummy signatures are pairwise distinct, so the nine distinct original indices in the conditional full-run theorem correspond to nine distinct dummy-signature byte strings. | `QSB/FinalSignedLoop.generated_dummy_pool_nodup`, `generatedDummyAt_injective`, and `QSB/FinalBonusIndices.nine_dummy_bytes_distinct` are checked on this one lock. They do not rule out identical push patterns elsewhere in the script or settle FindAndDelete scriptCode equality for arbitrary setups. |
| Final scriptCode selection models | Filtering the literal program's `Op.push` nodes by selected final signature bytes is order-independent and equivalent to one-at-a-time filtering. A separate byte-chunk lemma proves that a boundary match consumes one complete encoded opcode when its length equals the pattern's length, and filtering whole encoded chunks is order-independent. | `QSB/ScriptCodeSelection.lean` proves these conditional list facts. The exact fixture check below establishes the direct-push length condition for all 151 selected signature patterns and tests 35 ten-signature sets in three orders. Equality with Core's byte-level sequential FindAndDelete for every reached witness still needs parser/refinement proof. |
| Serialized lock and selected pushes | A source-shaped Lean parser splits the generated 9,923-byte lock into exactly 880 encoded chunks; decoding every chunk recovers the 880-opcode byte-machine program. All 151 possible final signature patterns are direct pushes, distinct, and each appears as exactly one complete encoded chunk. Any selected pattern matching at a generated opcode boundary consumes that complete chunk, regardless of following bytes. The selected final scriptCode obtained by whole-chunk filtering is invariant under any permutation of selected indices. | `QSB/EncodedLayout.lean` is generated from the pinned builder; `QSB/EncodedScript.lean` kernel-checks the parser, decoder, finite inventory, and boundary-match implication. The generator externally checks the script SHA-256 against the pinned fixture. `QSB/CoreGetOp.parse_eq_parseOne` relates a separate Core-shaped iterator-width parser to the existing parser for every byte string, including truncated PUSHDATA1/2/4 inputs. This is source-level modeling, not compiled-C++ equivalence or arbitrary-witness selection. |
| Sequential byte deletion on the literal lock | For any ordered list of the 151 selected final signature patterns, three Lean delete-at-boundary models return the whole-chunk-filtered script, even with repeated patterns. This includes every final index list with the fixed nonce appended. The literal lock has no `OP_CODESEPARATOR` opcode. | `QSB/FindAndDelete.lean` proves a generic simulation under explicit chunk stability and boundary-match premises. `QSB/CoreGetOp.lean` models Core's opcode-byte advance separately and proves parser and deletion-loop agreement for every byte script. `QSB/CoreFindAndDelete.lean` additionally models Core's delayed copy and return-original-on-no-match control flow and proves the same byte result, then applies it to the literal final and pin scriptCodes. These are source-shaped Lean theorems, not compiled Core refinement or arbitrary-witness signature selection. Transaction sighash remains open. |
| Pinning scriptCode on the literal lock | The fixed pinning signature ends in `SIGHASH_ALL`; its serialized direct push occurs exactly once. At every generated opcode boundary, a prefix match consumes that whole chunk. All three source-shaped FindAndDelete models therefore remove precisely that push. | `QSB/FindAndDelete.pin_scriptCode_scan`, `QSB/CoreGetOp.pin_scriptCode_scan`, and `QSB/CoreFindAndDelete.pin_scriptCode_run` check the actual 880-chunk fixture; `literal-find-and-delete.json` independently checks the regenerated source bytes. This does not prove compiled-C++ equivalence or that an arbitrary accepted transaction satisfies the ECDSA check. |
| SHA256 pinning and final puzzle scriptCodes | For every 32-byte signature, including SHA256 of either reached puzzle key, the source-shaped legacy FindAndDelete loop leaves the entire literal 9,923-byte lock unchanged: none of its 880 opcode chunks starts with the direct-push-32 opcode `0x20`. A successful source-shaped DER/checker gate therefore gives the checker that unmodified scriptCode. One successful arbitrary-stack byte-model run identifies both puzzle keys and the final key's later CHECKMULTISIG slot, and gives the two unchanged-scriptCode results together with the fixed pin-signature deletion candidate. | `QSB/PinPuzzleScriptCode.lean` proves the no-push-32 fixture fact, generic no-deletion theorem, and one-run compositions. `evidence/pin-puzzle-scriptcode-core.json` records six isolated pinned-Core positive/wrong-code pairs: a valid 32-byte signature under sighash trailing bytes `0x01`, `0x03`, and `0xff` passes with a key recovered for unchanged scriptCode when no push-32 is present, while an exact-push control passes only with the deleted code. Every wrong-code key fails. The experiment is not the full QSB lock. The theorem is source-shaped, and actual Core signature/sighash verification and arbitrary-scriptSig extraction remain unproved. |
| Source-shaped BASE CHECKSIGVERIFY success | Under the pinned Core 27.2 `VERIFY_ALL` flags, a successful source-shaped BASE check gives a nonempty strict-DER signature, a valid parsed key, and a successful external ECDSA/sighash checker call using the signature's actual last-byte hash type and FindAndDelete scriptCode. Applied to the reached pinning pair, the fixed signature uses `0x01` and the one-push-deleted lock; applied to either reached SHA256 puzzle, the hash type remains unconstrained and scriptCode is the full lock. The late puzzle key is the one later reached by the final multisignature. | `QSB/CoreChecksigEval.lean` proves these implications and composes them with successful arbitrary-stack byte-model traces. Its successful-checker premises are explicit. `validKey` and `verify` remain external; compiled Core equivalence, exact transaction sighash, ECDSA, scriptSig/consensus refinement, and any quantum probability bound are still unproved. |
| Source-shaped final ECDSA/sighash calls | Given a successful arbitrary-stack byte-model run and a successful source-shaped final ten-pair evaluation, every reached source-addressed signature has a strict-DER encoding and exposes its actual last-byte hash type, a valid parsed key, and a successful external ECDSA/sighash checker call. All ten calls use the one selected FindAndDelete scriptCode; the same conditional run yields seven opening matches, nine distinct selected positions, nine reached `SIGHASH_SINGLE` signatures, and the fixed tenth `SIGHASH_ALL` signature. | `QSB/CoreFinalChecksigEval.lean` composes the final source evaluator with a checker that explicitly strips each signature's last byte, and applies the reached-signature flag theorem under that same evaluator premise. The successful final evaluator, key validation, exact sighash/ECDSA function, and compiled-Core refinement remain external. |
| Pinning reached bytes and one-run puzzle keys | Every successful byte-model run from an arbitrary initial stack reaches the fixed pinning signature with the initial nonce key and reaches SHA256 of that same key with the initial puzzle key. Under explicit pair-verification and encoding-soundness premises, SHA256 of the pinning key is strict DER. Composing with the final-round witness theorem yields both DER puzzle keys, seven valid final openings, and the fixed final nonce check from one run. | `QSB/PinningScriptCode.lean` and `QSB/SourceWitness.lean` prove this for the generated byte model. The verifier predicates, their Core transaction sighashes, Core-to-byte-machine refinement, dynamic setup bytes, and the quantum event bound remain external. |
| Reached final signatures determine modeled scriptCode | In a successful full byte-model run with an externally supplied nonempty, `VERIFY_ALL`-encoding-sound ten-pair final scan, the reached signature cells are exactly the second bonus dummy, first bonus dummy, seven gathered dummies in reverse draw order, and fixed nonce. The first nine end with `SIGHASH_SINGLE`; the tenth is the fixed `SIGHASH_ALL` nonce. Applying the sequential byte deletion loop to those *reached bytes* yields the scriptCode selected by their nine distinct original positions. Equal-count matching forces all ten reached signature/key pairs to verify, including the fixed nonce against the last reached key. | `QSB/FinalScriptCode.lean` composes the conditional source theorem, abstract matching loop, and exact serialized-lock deletion theorem. No signature list is freely chosen in its conclusion. The scan premise, Core C++ refinement, transaction sighash/ECDSA checks, and hash-to-DER puzzle remain unproved. |
| Late puzzle key equals reached nonce key | For any successful full byte-model run, the key SHA256-hashed into the late puzzle CHECKSIGVERIFY signature is exactly the last reached final CHECKMULTISIG key. Under the conditional encoding-sound ten-pair final scan, this key is checked by the fixed nonce, and the final witness uses this reached key rather than a caller-selected key. If the reached puzzle CHECKSIGVERIFY is also encoding-sound, SHA256 of that key satisfies the source-shaped strict-DER predicate. | `QSB/ByteFinalCounts.accepted_final_setup_first_key`, `QSB/ByteLatePuzzle.accepted_whole_program_final_puzzle_key`, and `QSB/FinalRoundWitness.matched_run_reached_key_der_puzzle` check the same byte trace and actual key bytes. The two verifier-soundness/matching premises are external; these theorems do not establish Core C++ equivalence, the real ECDSA nonce equation, legacy sighash binding, or a quantum puzzle bound. |
| Literal final sighash bytes | All 150 generated final dummy signatures end in `0x03` (`SIGHASH_SINGLE`); the fixed final nonce signature ends in `0x01` (`SIGHASH_ALL`). | `QSB/ScriptCodeSelection.lean` checks the bytes of this lock for every dummy index and any selected list. The SINGLE out-of-range constant-message rule applies only when the actual input index is at least the transaction's output count; arbitrary accepted transactions may have more outputs. Core sighash refinement remains open. |
| Final matching with the empty-signature parser exception | The same conditional nine-position result follows if successful pair verification separately entails a nonempty signature and acceptance by the modeled `VERIFY_ALL` encoding gate. | `QSB/FinalBonusIndices.matched_full_run_nine_positions_verify_all` turns those two premises into strict-DER soundness using `DERSyntax.verifyAllEncoding_nonempty`. Core's actual ECDSA result, pair verifier, and full scan still require refinement. |
| Byte trace to abstract round-witness fields | From the conditional full-run trace, Lean constructs a `RoundWitness` with seven signed positions, two disjoint bonus positions, and actual recorded opening bytes that hash to their generated commitments. The source-shaped variant takes successful-pair nonemptiness and `VERIFY_ALL` encoding acceptance separately. | `QSB/FinalRoundWitness.lean` uses an executable lookup over trace pairs and proves `FinalRoundShape` and `OpeningsValid`. The earlier `matched_run_shape_and_openings_verify_all` accepts an arbitrary key; the newer reached-key theorem above replaces it with the actual modeled final key. Transaction-bound nonce/ECDSA semantics, a Core extractor, and a quantum bound remain open. |
| Combined modeled bare boundary | In one truthy modeled run after any partial scriptSig evaluator, the first signed comparison has lock-owned commitment origin and the final CHECKMULTISIG has both count operands 10 and a true supplied outcome. | `QSB/BareBoundary.accepted_bare_first_origin_and_final_counts` composes the two arbitrary-stack results for the same execution. The later byte-model theorem establishes all seven signed and two bonus source roles under supplied outcomes, with an explicit commitment bonus branch. Core refinement and a probability bound remain open. |
| Generated layout | Last final-round bonus index 152 selects locking-script commitment C[round 2,7], and the symbolic trace completes if final multisignature success is supplied | A concrete role escape in the stack model. Symbolic signature outcomes alone cannot establish final-round dummy-signature shape. |
| Generated layout | First final-round bonus index 152 also selects locking-script commitment C[round 2,7]; setting the second bonus index to 11 leaves a truthy symbolic trace with that commitment in a final signature slot | `QSB/FirstBonus.lean` checks the exact probe and final stack position. It assumes supplied signature outcomes and canonical preceding signed selections; the altered-lock Core experiment below tests the DER-shaped case. |
| Bonus region | After the canonical preceding eight final-round selections, the final bonus roll's 153 reachable cells are exactly eight gathered dummy signatures, the fixed nonce signature, the zero dummy, 142 unused dummy signatures, and commitment C[round 2,7] | `QSB/Bonus.lean` checks the exact generated prefix region and all 153 index roles. This is conditional on the preceding canonical stack; it does not prove arbitrary-witness extraction. |
| Bonus region | For indices 0–9, rolling the reachable region places a nonzero generated dummy at the prospective NULLDUMMY slot; indices 10–152 preserve zero there | Local stack-order theorem, not a complete Core-acceptance classification. Later pubkey rolls and arbitrary witness layouts still need refinement. |
| Byte index | A source-shaped four-byte sign-magnitude ScriptNum parser maps nonminimal `0a00` to 10, nonminimal `980000` to 152, `9880` to -152, and rejects five bytes. For every byte list, Lean proves that disjoint eight-bit-lane OR assembly equals arithmetic little-endian assembly and that the resulting word is below `256^length`. For every byte list passing the four-byte guard, a second source-shaped parser using the final byte's bitwise 0x80 test and Core's 64-bit complement mask returns the same result. Every successfully parsed value lies in `[-2147483647,2147483647]`, so Core's 32-bit `getint` saturation cannot affect such an operand. | `QSB/ByteIndex.lean` and `QSB/CoreScriptNum.lean` check these pure conversion facts and the listed local bonus-role consequences. The pinned-Core `OP_1ADD` differential probe checks 2,384 zero- to four-byte encodings (all 256 one-byte cases and every canonical value from −1023 through 1023) plus a five-byte rejection in `evidence/scriptnum-core.json`. The compiled C++ interpreter correspondence and full trace refinement remain unproved. |
| Byte index | The byte model now uses Core's repeated-low-byte ScriptNum magnitude loop. Lean proves that two independently named source-shaped serializers agree for every integer, including the five-byte magnitude guard; every sum and minimum of two parsed four-byte operands is defined. The loop decodes to its input magnitude below its fuel bound and is stable under extra fuel. The earlier finite round trips for −1023 through 1023 remain checked. | `QSB/ByteIndex.lean`, `QSB/ByteIndexRange.lean`, and `QSB/CoreSerialize.lean` establish these source-model facts. The byte model was revised and all dependent theorems rebuilt; this is not a universal equivalence to the former indexed-digit implementation or to compiled Core C++. The five-byte magnitude guard covers all `OP_ADD` and `OP_MIN` results from valid four-byte operands. |
| Numeric source path | For every pair of raw byte strings, the source-shaped `OP_MIN` and `OP_ADD` parse/serialize functions equal the byte model's numeric substeps. When the operands parse, both operations produce bytes; under the modeled opcode budget, they equal the corresponding `ByteMachine.step` stack transitions. The generated first signed `MIN 152; ADD 151` path therefore agrees for nonminimal, overshoot, and negative parsed indices. | `QSB/CoreNumericOps.lean` composes all-input parser and serializer equalities. The 17-case pinned-Core `OP_MIN; OP_ADD` differential in `evidence/min-add-core.json` includes negative encodings, nonminimal and overshoot inputs, a wrong-expected-byte control, and a five-byte rejection. Full compiled-interpreter trace refinement remains open. |
| `OP_ROLL` orientation | For every raw index and byte stack, a source-shaped bottom-first operation (parse, reject negative/out-of-range depth, select, erase, append) returns the reversal of Lean's top-first byte-model result. Under the modeled opcode-budget premise, this equals the stack projection of `ByteMachine.step .roll`. | `QSB/CoreRoll.lean` proves the reverse-index and reverse-erase identities and composes them with `QSB/CoreScriptNum.coreSetVch_eq_parseScriptNum`. The pinned adapter matches 11 finite bare-script cases in `evidence/roll-core.json`, including negative zero, nonminimal 152, out-of-range, and five-byte rejection. The theorem models one source-level opcode, not compiled Core, whole-script resource checks, or signature semantics. |
| Non-signature interpreter segments | For every initial byte stack, hash functions, supplied outcomes, and opcode count, a bottom-first source-shaped interpreter agrees with `ByteMachine.run` over each of the six signature-free intervals of the literal lock, including 520-byte push, 201-opcode, and post-step 1000-cell limits. Lean checks that those intervals plus signature opcodes at positions 2, 5, 423, 446, 856, and 879 reconstruct all 880 instructions. | `QSB/CoreOpcodeStep.lean` proves one-step and list-run reversal simulation, reusing source-shaped numeric and roll operations. This is mathematical correspondence to the inspected Core 27.2 opcode cases with minimal-data enforcement absent; it is not compiled-C++ refinement. The six signature sites, Core's checker/outcomes, scriptSig execution, and consensus transaction acceptance remain outside the theorem. |
| Whole source-shaped structural interpreter | For any initial post-scriptSig byte stack and supplied signature-outcome list, a successful bottom-first source-shaped run of all 880 literal lock opcodes projects to the same top-first byte-model run, including signature-site count parsing, stack capacity, NULLDUMMY, CHECKSIGVERIFY pops, opcode budget, and post-step 1000-cell limit. The false first-round multisignature result remains a valid structural transition. | `QSB/CoreMultisigStep.lean` proves a successful source multisignature step projects to the byte step for arbitrary count encodings and either supplied result; `QSB/CoreChecksigStep.lean` does the same for CHECKSIGVERIFY. `QSB/CoreStructuralRun.lean` composes these with the nonsignature source steps for any opcode list and the literal lock. The source models still take cryptographic scan Booleans as inputs; compiled Core-to-source equivalence, real scriptSig execution, exact checker/sighash outcomes, and consensus acceptance remain unproved. |
| One-run source-shaped extraction certificate | `QSB/CoreSourceExtraction.lean` evaluates four necessary signature checks at the actual reached bottom-first source stacks: fixed pin, early SHA256 puzzle, late SHA256 puzzle, and the enforcing final ten-pair scan. A truthy successful structural run with those checks yields one pinning key, seven final HORS openings, two disjoint bonus positions, strict-DER hashes of the pin and final keys, and the exact source-shaped `SIGHASH_ALL` checker calls for both fixed signatures. The pin sites are proved to read the expected bytes for every arbitrary initial stack that completes the prefix. | `necessarySignatureChecks` is executable over the Lean source model, not a Bitcoin Core acceptance predicate. The structural run still receives supplied signature Booleans; the first-round multisignature may be false and its fatal encoding failures are overapproximated. The compiled interpreter, real SHA256/HASH160, transaction parser, `SignatureHash`, ECDSA, dynamic setup, and joint QROM bound remain external. |
| Joint source hash/checker instantiation | One pair of arbitrary byte functions `H` and `R` now supplies every source hash role: the pin and final fixed-signature ECDSA calls receive `H(H(sourceAllPreimage))`, while seven reached opening equations use `R(H(opening))` against generated commitments. A successful SHA256-derived puzzle check exposes its actual last-byte hash type and the resulting legacy digest, including the out-of-range SINGLE constant-message case. | `QSB/JointSourceChecks.lean` specializes the prior necessary-check theorem and the all-hash-type serializer. It prevents an accidental independent-H idealization at this deterministic boundary, but does not model random sampling or coherent queries. The external ECDSA predicate, selected transaction/input and scriptCode refinement, supplied source-interpreter signature outcomes, and Core acceptance remain open. No probability bound follows. |
| Byte lock | The generated literal-byte lock has 880 instructions, ends in `CHECKMULTISIG`, and has 15 `EQUALVERIFY` opcodes, each immediately preceded by `HASH160` | `QSB/ByteLayout.lean` is generated from the pinned builder and checked against the existing exact script SHA-256. These are syntactic facts, not an arbitrary-witness run theorem. |
| Byte execution | For arbitrary stack tails, cost and later opcodes, successful execution after a reached `HASH160; EQUALVERIFY` pair implies that the hash of the actual opening bytes equals the compared bytes; `run_append` lifts this implication into any executed program prefix | `QSB/ByteMachine.lean` models byte equality with arbitrary hash functions. It does not show that the compared bytes are one of the intended HORS commitments. Signature outcomes, FindAndDelete, sighash and ECDSA remain external. |
| Byte trace | Erasing the equality-pair trace gives the same final state as the byte interpreter for every program and starting state | `QSB/ByteTrace.lean`; the trace records equal byte pairs, but a whole-lock theorem relating every pair to its intended commitment position is still missing. |
| Byte witness | One disposable 57-cell witness completes the 880-instruction byte interpreter with 201 counted operations, 569 final stack cells, and 15 reached hash comparisons; its final truth depends on the final multisignature Boolean, not the first | `QSB/ByteWitness.lean` uses a generated lookup HASH160, arbitrary constant SHA256, and externally supplied signature outcomes. It checks model consistency, not actual cryptography, Core acceptance or arbitrary witnesses. |
| Final count | For any underlying stack, successful execution of the lock's ten fixed final key rolls leaves the pushed signature count 10 at stack offset 10; the last push gives public-key count 10 | `QSB/KeyRolls.lean` proves the list invariant and checks the generated 23-instruction suffix. This does not identify which arbitrary cells were selected as keys or signatures. |
| Final matching | In a Core-shaped key-scanning model, success with equal signature/key counts implies every corresponding pair verifies | `QSB/Multisig.lean` proves this for arbitrary lists and verifiers; `QSB/KeyRolls.lean` applies it to the ten cells in the final stack. Equality with Core's actual DER, FindAndDelete, sighash and ECDSA behavior is a separate refinement obligation. |
| Core final stack addresses | Core's one-based `stacktop(-i)` on a bottom-first vector addresses the byte model's top-first key count at 0, signature count at 11, keys at 1–10, signatures at 12–21, and NULLDUMMY at 22 when both counts are ten. Every truthy successful run of the full literal byte program reaches those addresses. Under an explicit successful ten-pair abstract scan, every source-addressed signature/key pair verifies. | `QSB/CoreMultisigStack.lean` proves the reverse-index arithmetic for arbitrary stacks and composes it with the full byte-run count and dummy results. The native isolated 10-of-10 case is reproduced in `ten-signature-find-and-delete.json`. This remains byte-model/source-index reasoning: the Core parser, actual pair verifier, transaction sighash, and compiled interpreter are not refined. |
| Gated final multisignature source model | For an arbitrary initial byte stack of the literal generated lock, a successful full byte-model run whose reached final stack passes a source-shaped ten-pair evaluator yields seven actual HORS opening matches, two distinct bonus positions, one selected FindAndDelete scriptCode, and ten DER-valid source-addressed successful pairs against that same code. The evaluator checks the ten-count cells, stack capacity, DER gate, nonempty ECDSA input, and NULLDUMMY; a failed pair advances only the key cursor. | `QSB/CoreMultisigEval.lean` composes Core-shaped stack addresses, the ordered DER model, the source-shaped deletion loop, and the full byte-run source trace. The successful-evaluator premise is explicit: compiled Core's checker, sighash, ECDSA, and whole-interpreter refinement have not been proved. The 22-case isolated ten-signature experiment below is finite corroboration. |
| Multisignature source cleanup | For arbitrary key and signature counts, a bottom-first source-shaped cleanup checks the extra dummy under `NULLDUMMY`, removes exactly the counted argument cells and dummy, and pushes the Boolean result. Whenever it succeeds, its stack is the reverse of the byte model's `bool :: drop arguments` stack, including for a false first-round result. A successful final ten-pair source evaluator supplies the capacity and empty-dummy premises with 23 consumed cells; both literal count cells decode to ten under the source-shaped ScriptNum parser. | `QSB/CoreMultisigCleanup.lean` proves the generic reversal and final count/cleanup specialization. It models post-scan stack mutation and count parsing for the reached final cell values; pair-scan results and compiled Core-to-Lean refinement remain separate. |
| Attack extraction | For an owner-forbidden transaction, extracted pinning and final round imply a fresh final-round opening or a novel two-puzzle search result | The target events depend on owner authorization but not on Bitcoin acceptance. Actual arbitrary-witness extraction and a quantum query bound are still missing. |
| Final-round shape | Seven distinct signed positions plus two disjoint bonus positions give nine total | The shape is an explicit premise. The bonus-overshoot Core experiment shows that a DER-shaped HORS commitment can occupy a bonus signature role on an altered lock; unconditional arbitrary-witness extraction needs a bad-setup branch or a stronger shape definition. |
| Game | A Core-accepted target spend with changed ordered outputs is unauthorized when the owner bound those outputs | The Core acceptance and target-consumption predicates are explicit inputs; parsing and ledger acceptance remain unproved. |
| Game | Disclosure sets grow when more signing records are appended, regardless of whether they were mined | No assumption that cancellation, reorgs or backup restoration erase revealed material. |
| Game | The disclosed union has at most `t·r` positions after `r` records each opening at most `t`, capped by the finite index universe | Counts all records, so a per-vault/per-round transcript can give a tighter bound. The per-record cap is an explicit premise. |
| Reduction | An unauthorized spend under `SourceExtraction` and honest release implies a fresh final-round opening or `NovelTwoPuzzle` | `SourceExtraction` is an explicit **unproved** arbitrary-witness Script premise. It must be computed from the adversary's transaction, not selected from private challenger state. |
| Reduction | A bad spend is novel relative to honestly released QSB unlocking transcripts | Requires the release invariant: every released transaction's semantic projection remains in the *ever-authorized* set. Revocation after release is outside this unforgeability definition. |
| Reduction | Every unauthorized spend implies a fresh opening, a two-puzzle event, **or an extraction gap** | The gap has no small probability bound. The theorem does not prove QSB security. |
| Reduction | A constant-`none` extractor makes the gap event exactly the unauthorized-spend event | Nonvacuity check: a trivial extractor cannot make the missing source-refinement obligation disappear. |
| Reduction | For any terminal measure, bounds on those three events add | The fresh and puzzle events exclude owner-authorized projections; otherwise their probability could be one for a trivial replay. The theorem supplies no cryptographic event bounds and no zero-gap claim. |

The parameters and extraction interface currently accept general types; they do
not instantiate SHA-256 or HASH160 as concrete Lean functions. Their generic
status is intentional and appears in theorem types, rather than being hidden
behind a QSB-specific cryptographic axiom. Disclosure records and extracted
round witnesses carry preimage values **only for their opened positions** using
membership-indexed functions. This prevents their types from granting all
unopened HORS secrets to the adversary. The source extractor still requires a
proof that each carried value comes from the adversary's transaction bytes.

## Native evidence

`round-results.json` records 18 cases through the app's actual Core adapter.
The original seven are:

- Original synthetic witness against the **modified** lock: accepted.
- Invalid round-1 dummy signature/key pair: accepted.
- Invalid round-2 dummy signature/key pair: rejected.
- Incorrect round-1 HORS preimage: rejected.
- Incorrect round-2 HORS preimage: rejected.
- Changed destination with freshly recovered nonce keys: accepted.
- Changed destination with the **old round-1 nonce key**: accepted. The
  independent CPU check confirms that old key no longer verifies the
  first-round nonce signature on the new transaction. Pinning and round 2 do.

The eleven added cases use two outputs, so the signed input's nine final
`SIGHASH_SINGLE` checks are in range. Core accepts the full disposable lock
with all ten final keys recovered against one shared scriptCode. It rejects
each of ten controls that changes one final key to one recovered after
incorrectly retaining that key's own signature push in scriptCode. The
independent EC check confirms each wrong key fails on the correct digest;
the report records both scriptCode hashes and both sighash scalars. The
seven earlier outcomes and their transaction hashes are unchanged.

The lock has exactly three puzzle CHECKSIGVERIFY sites replaced by OP_2DROP.
The pinning signature check, both CHECKMULTISIG instructions, and all HASH160
comparisons remain real. Signature encodings are well formed. The invalid pair
is independently checked as invalid by the CPU EC implementation. This rules
out treating first-round success as a necessary condition in this experiment.
It does not solve the real hash puzzles or change a real payment destination.

`core-semantics.json` records isolated fixed-signature scripts, with no relaxed
opcodes. Compressed, uncompressed, and correct-parity hybrid encodings verify;
wrong-parity hybrid encoding fails. Changing the destination with a fixed ALL
signature and the same key fails; recomputing the key by public recovery passes.
The same ALL digest and key also pass with the corresponding strict-DER high-S
variant of the signature, consistent with Core's low-S normalization before
ECDSA verification. The previous ten outcomes remain byte-identical.
The SINGLE-bug signature continues to verify after destination and amount change.
Adding a second output makes the spending input's SINGLE sighash in range:
the old recovered key then fails and a key publicly recovered for the new
message passes. The isolated test shows that the constant-message shortcut
cannot be assumed for arbitrary transaction layouts, and that changing the
supplied key can restore verification for this fixed signature.
These are component facts, not an accepted QSB forgery.

`bare-script-boundary.json` records five isolated native tests of the
`scriptSig`/bare-output boundary. A non-push-only `OP_1 OP_1 OP_ADD` scriptSig
passes a value of 2 to `OP_2 OP_EQUAL`, and each script can separately use
201 counted `OP_NOP`s; 202 in either script fails. The source-level mapping in
`CORE-BARE-BOUNDARY.md` explains why arbitrary scriptSig stack production can
be abstracted for the first modeled commitment-origin theorem. This is not a
Core-to-Lean execution refinement or a QSB-lock acceptance test.

`sighash-types.json` records 256 isolated `CHECKSIG` transactions with fixed
valid DER integers, one for each possible trailing sighash byte. For each byte,
the test recomputed the legacy sighash, publicly recovered a verification key,
and used the pinned Core consensus adapter. All 256 verified under its
`VERIFY_ALL` consensus flags. This supports using 256 possibilities in the
syntactic DER count for this pinned legacy context; it does not prove a
uniformity or quantum query bound for SHA-256 outputs.

`all-sighash-commitments.json` records an isolated fixed-signature ALL probe
with two inputs and two baseline outputs. Ten changes to output or other committed
fields changed the source-shaped preimage and observed SHA256d digest; Core
rejected the old key and accepted a freshly recovered key in every case. Two
`scriptSig`-only changes kept that preimage and digest; Core accepted the old
key. The source contract and exact limitations are in `CORE-SIGHASH-ALL.md`.
This finite result does not prove universal old-key rejection, Core-to-Lean
serialization equivalence for arbitrary transactions, or QSB full-lock acceptance.

`wire-vectors.json` records five CompactSize and one amount byte vector from
the pinned app; all match the corresponding kernel-checked Lean examples,
including the 253, 65,536, and `2^32` branch boundaries. This is finite
cross-checking of the concrete encoders, not a C++ equivalence theorem.

`core-sighash-vectors.json` records a differential check against Core 27.2's
published legacy sighash corpus. All 500 expected digests match independent
source-shaped preimage hashing and the pinned app's sighash: 467 ALL-like, 16
NONE, and 17 in-range SINGLE cases, including 229 ANYONECANPAY cases. Of the
scripts, 210 contain opcode-boundary `OP_CODESEPARATOR`; Core's simple-script
generator makes that removal unambiguous. The published corpus has neither
literal `0x01` nor out-of-range SINGLE; separate native probes cover those
cases. These finite checks do not prove Core-to-Lean equivalence for arbitrary
accepted witnesses.

`der20-parser.json` records 73 isolated Core 27.2 `CHECKSIG; DROP; TRUE`
cases against the same pinned consensus library and `VERIFY_ALL` flags. The
script discards the ECDSA Boolean, so a nonempty malformed DER signature aborts
while a syntax-valid one may finish even if ECDSA fails. The corpus covers all
12 admissible R lengths in a 20-byte signature, sign-padding cases, malformed
tags/lengths/leading integers, selected trailing sighash bytes, size
boundaries, deterministic random negatives, and the empty signature. All 73
outcomes match Lean's `DERSyntax.verifyAllEncoding`; both Lean strict-DER
models agree on all cases, as also proved for every byte list. Strict DER
accepts 42
cases and the encoding gate accepts 43 because Core permits empty signatures.
This is finite differential evidence for the parser boundary, not a proof for
all byte strings, final multisignature success, or a QSB-lock spend.

`find-and-delete-boundary.json` records eight isolated legacy `CHECKSIG` lock
shapes, each with a matching recovered key and a mismatching negative control.
Core accepts the eight keys recovered from the app's opcode-boundary
`find_and_delete` scriptCode and rejects all eight recovered from deliberately
wrong scriptCodes. Canonical pushes are removed, including separated and
adjacent double occurrences;
a signature-push pattern embedded within another push and noncanonical
`PUSHDATA1/2/4` pushes remain. The final case uses the literal 56-byte pinning
signature in an isolated lock. This corroborates selected source-level behavior,
not a complete FindAndDelete equivalence or the QSB final scriptCode. The
exact refinement contract is in `CORE-FINAL-MATCH.md`.

`ten-signature-find-and-delete.json` checks one isolated 10-of-10 bare
multisignature lock containing all 151 final fixture signature pushes in a
nonexecuted branch. With two outputs, both SINGLE and ALL sighashes depend on
the transaction and shared scriptCode. The pinned Core adapter accepts the
keys recovered after deleting all ten selected pushes, rejects a wrong SINGLE
key and a wrong ALL key, and rejects ten full-key controls that retain one
selected push each. A `CHECKMULTISIG; DROP; TRUE` variant additionally accepts
an empty first-scanned signature, whose false verification can be discarded,
but rejects a malformed nonempty first-scanned signature, consistent with the
source DER gate; the adapter does not return its error code. Seven further
cases accept nonminimal encodings of either or both numeric ten-count cells,
and reject a nonempty NULLDUMMY, negative or 21-key count, and eleven
signatures against ten keys. These 22 outcomes corroborate the count,
cleanup, encoding, and simultaneous-deletion source distinctions;
the base test lock is 1,560 bytes and does not execute the full QSB lock.

`literal-find-and-delete.json` regenerates the disposable Config A lock and
checks its 9,923-byte script SHA-256 against the byte-layout fixture. At its
880 opcode boundaries, each of the 150 final dummy signatures and the fixed
final nonce occurs as one serialized direct push. Every boundary prefix match
of these 151 patterns consumes its complete opcode. For every signature, the
app's single-signature FindAndDelete removes exactly that push. In 35 selected
ten-signature sets, forward, reverse, and shuffled app deletion orders match
the same whole-chunk filter. Since direct-push opcode lengths fix the parsed
chunk size, this exhaustive fixture inventory also supports a source-level
argument for arbitrary subsets of these 151 literal patterns. The 35-set
execution is a regression check, not exhaustive enumeration of subsets or
a Lean/Core binary equivalence proof.
The same inventory also checks that the literal pinning signature's unique
57-byte serialized push is at offset zero and that deleting it yields the
recorded pinning scriptCode hash.

`selection-prefix.json` independently checks first-selection reachability with
Core v27.2. Disposable test locks are **truncated** at selected instructions
from the first signed-pool `OP_ROLL` (byte offset 4783) through the next
`OP_MIN` (byte offset 4798).
The first hash puzzle check is replaced with `OP_2DROP`, while pinning remains
real. With index 152 and an inserted external 20-byte marker, the first prefix
accepts a nonzero marker and rejects an all-zero marker. A second prefix accepts
an attacker-chosen `HASH160(0x0a)` marker and rejects a mismatched marker.
Only the marker changes within each of the first two pairs. With the matching
marker, Core accepts a prefix ending after the next fixed index roll and a
prefix ending after its following numeric push; adding the single `OP_MIN`
changes acceptance to rejection. The pinning signature is recovered for each
truncated lock, while one puzzle `CHECKSIGVERIFY` is replaced by `OP_2DROP`.
The before/after-`OP_MIN` pair gives the same result with nonminimal index
bytes `980000` (numeric 152) and `ffffff7f` (numeric 2³¹−1).
This corroborates the byte-model parse failure in the tested witness, not
acceptance by the complete QSB script or an attack on funds.

`bonus-overshoot.json` tests the complete **puzzle-relaxed** lock with actual
Core signature checks. A canonical witness accepts with either the natural
or a crafted 20-byte round-2 commitment at position 7. Setting **either**
final-round bonus index to 152 rejects with the natural commitment, but accepts
when that commitment is replaced with a deliberately DER-valid 20-byte
signature and the corresponding publicly recovered verification key is
supplied. For the first bonus, the second index is adjusted to 11 to collect
the remaining dummy. The crafted commitment was **not** generated as
`HASH160(secret)`; it is an altered setup, not a production-vault forgery.
It demonstrates that DER syntax and setup distribution must be part of the
source-extraction argument. The other three hash-to-signature puzzle checks
were replaced by `OP_2DROP` in this experiment.

`bonus-indices.json` tests the last bonus index at the role boundaries using
the same pinned Core adapter and the same three relaxed puzzle checks. With
natural commitments, indices 10, 11 and 151 accept when the corresponding
selected dummy signature and recovered key are supplied; indices 0, 7, 8, 9
and 152 reject. The negative controls use canonical pubkeys, so their Core
rejection alone does not isolate the cause; the Lean local stack theorem shows
the nonfresh indices also shift a nonzero dummy into the prospective NULLDUMMY
slot under the canonical preceding trace. At index 152, the deliberately
DER-shaped altered commitment accepts, reproducing the encoding exception.
None of these runs accepts the unrelaxed QSB lock.
The same full-lock adapter accepts nonminimal index bytes `0a00` for numeric 10
and `980000` for numeric 152, while a five-byte 152 encoding and negative 152
reject. The negative cases have multiple possible failure causes; the positive
nonminimal cases directly show that a source extractor must decode values rather
than require canonical index serialization.

`min-add-core.json` compares the first signed numeric `OP_MIN 152; OP_ADD 151`
path with independently encoded expected bytes for 17 raw ScriptNums. They
include empty and negative-zero encodings, nonminimal positive and negative
values, values on both sides of the cap, and both four-byte extrema. One combined
bare script accepts all 17 comparisons; a wrong expected byte and a five-byte
operand each reject. This finite differential tests the numeric source path,
not the full QSB lock or all possible byte inputs.
Lean also proves that adding any two successfully parsed four-byte operands
stays inside Core's signed 64-bit arithmetic range.

`final-signed-boundary.json` tests the first final-round signed index on the
complete puzzle-relaxed lock. The canonical index 2 accepts; indices 0, 1,
152, and nonminimal `980000` (numeric 152) reject under the pinned Core 27.2
adapter. Pinning, HORS comparisons, and both CHECKMULTISIGs remain real; only
the three hash-to-signature puzzle checks are replaced with `OP_2DROP`.
The rejections alone do not isolate a Core failure opcode. The full-run Lean
byte-model theorem independently excludes negative values, 0, 1, and values
at least 152; every modeled success matches a second-round commitment to
an opening's HASH160. Core refinement is still open.

`second-final-signed-boundary.json` uses the same pinned Core adapter and
puzzle-relaxed complete lock with the second signed index varied. Canonical 3
and nonminimal `0300` accept; 0, 1, 2, -1, canonical 152, and nonminimal
`980000` reject. The original first-index probe was also rerun and reproduced
its recorded evidence byte-for-byte. The native rejections do not isolate
their failure opcode, and these cases do not establish Core refinement.

The source of `consensus/verify.cpp` in the native build's named revision
`9a7c2ab` has the same SHA-256 as the analyzed app revision:
`54ddb7c6049a21f4aaad23ef1a5e1fe15249eb2ade1cb5082ef15f90c2847fee`.
The library was separately matched to the official archive. This is provenance
and component evidence, not a reproducible compilation proof of the wrapper.

## Source-to-model map

Paths below are relative to the app revision in the inventory unless prefixed
with `solver:`. Line anchors refer to that revision.

| Source | Concrete responsibility | Formal / evidence connection |
|---|---|---|
| public/qsb/bridge.py:16 | Only Config A is admitted; rebuilds exact lock and checks commitments | Security-game configuration boundary; not mechanized. |
| worker/cpu/bitcoin_tx.py:415 | 20-byte secrets and HASH160 commitments | `OpeningsValid`, `FreshOpening`; concrete hash correctness unproved. |
| worker/cpu/qsb_pipeline.py:253 | (150,8,1,7,2), single SHA-256 configuration | `Parameters`; comments about security levels are not adopted. |
| worker/cpu/qsb_pipeline.py:291 | Public fixed nonce construction, signature hashtype 1 | `Nonce`; precise group instantiation pending. |
| worker/cpu/bitcoin_tx.py:485 | Pinning: fixed signature check, hash key, puzzle signature check | Arbitrary-stack byte-model reached-pair and pin scriptCode theorems; Core verifier/sighash refinement pending. |
| worker/cpu/bitcoin_tx.py:545 | OP_MIN/ROLL/HASH160 selection and bonus logic | `Selection` local lemmas and the literal-byte interpreter; complete arbitrary-witness invariant pending. |
| worker/cpu/bitcoin_tx.py:598 | CHECKMULTISIG ending each round | First-round result experiment; final-round binding needs extraction. |
| worker/cpu/bitcoin_tx.py:749 | Concatenation of the two rounds, with first result left on stack | Structural first-round finding. |
| worker/cpu/bitcoin_tx.py:131 | Legacy sighash and SINGLE bug | Isolated Core mutation evidence; serialization injectivity pending. |
| worker/cpu/bitcoin_tx.py:199 | FindAndDelete implementation | Must match Core boundary semantics; not replaced by abstract subset deletion in any claimed full proof. |
| worker/cpu/secp256k1.py | Curve operations and DER/recoverability checks | CPU experiment oracle; full Lean correctness not claimed. |
| worker/cpu/secp256k1.py:135 | App `ecdsa_recover` reconstructs only x=`r` with a parity flag | An adversary-facing bound cannot inherit this helper's omission of the possible x=`r+n` branch. `evidence/ecdsa-replay-targets.json` includes a public scalar-zero x=`r+n` ECDSA verification whose key the helper cannot recover. The conditional four-point Lean bound includes both x candidates; no Core transaction or SHA256d preimage is shown. |
| worker/cpu/qsb_pipeline.py:1033 | Round key recovery after deleting selected signatures | Intended `nonceRelation`; adversarial witness equivalence unproved. |
| src/lib/backup.ts:46 | Persisted authorization and reuse guards | Honest-client game rules, not on-chain enforcement. |
| src/lib/transactions.ts:309 | Exact-spend checks | Owner authorization boundary; server rejection does not bound Bitcoin attackers. |
| src/TransactionDialog.tsx:650 | Browser intent, assembly and wallet-signing flow | Local reminders are not on-chain constraints; HORS preimages enter the scriptSig before helper-wallet signing, so external-signer delivery is a disclosure boundary. |
| sdk/client.ts:299,782,849 | SDK's default in-memory guard, saved intent and assembly binding | Auth game must allow older backup restores; CLI's file-backed guard is a separate honest-client behavior. |
| sdk/signer.ts:26 | SDK wallet/address restriction | Service-flow helper signing, not a Script-enforced requirement. |
| docs/KEY-CUSTODY.md:5 | Original wallet is a service requirement | Helper-input adversary scope. |
| consensus/verify.cpp:29 | Ordered spent outputs and VERIFY_ALL for each input | Native evidence with official Core library; ledger state external. |
| solver:worker/prepare_kernels.py:35 | Production DER predicate adaptation | Distinguishes benchmark scoring from actual puzzle target. |
| solver:README.md:3 | Public, untrusted solver / independent verifier boundary | No claim based on image identity, GPU speed, or honest enumeration. |

## Assumption and dependency inventory

No cryptographic axiom has been declared in Lean. The checked theorems use only
standard Lean foundations as reported by `#print axioms`: propositional
extensionality (`propext`), quotient soundness (`Quot.sound`), and classical choice
where listed. They have explicit mathematical premises rather than hidden
security assumptions. Closed DER arithmetic uses kernel reduction.

For a future end-to-end theorem, all of the following need a proof, an explicitly
scoped external assumption, or a counterexample:

1. Correct owner authorization and fresh local randomness; honest-device and
   backup-confidentiality boundaries; bounded disclosure history.
2. Full arbitrary-witness extraction from the real legacy script, including
   bonus indices, stack roles, NULLDUMMY, the seven-plus-two distinct final-round
   shape, and the unchecked first-round result. The extractor must be efficiently
   computable from the adversary's transaction bytes. The generated local probe
   shows that the first signed `OP_MIN` cap of 152 plus offset 151 can select an
   attacker-supplied initial-stack cell beyond the 150 intended commitments.
   Later checks reject the tested full probe; any pool-confinement proof needs
   a global stack invariant, rather than a cap-only argument. A separate last-
   bonus probe reaches a locking-script commitment and can pass real final
   `CHECKMULTISIG` if that 20-byte commitment is DER-shaped. The synthetic
   positive case violates ordinary HORS commitment generation, so a valid-setup
   theorem must account for the corresponding rare-event condition.
3. Bitcoin byte parsing, ScriptNum semantics, integer ranges, resource limits,
   FindAndDelete, sighash serialization, and ALL binding to authorization.
   The full source-shaped ALL serializer now has an output-parser round trip
   for valid byte-model transactions, including varying prepared input scripts;
   a pinned 139-byte fixture matches the app's baseline preimage.
   `CORE-SIGHASH-ALL.md` maps the source and records finite Core checks.
   Arbitrary accepted QSB witnesses still need the C++/Lean serializer and
   reached-scriptCode refinement. Same-key verification
   of a new message must be charged against all admissible ECDSA recovery
   targets, not merely SHA256d collisions.
   The new byte interpreter is an intermediate model with explicit hash
   functions and Boolean signature outcomes. For the bare output, Core's
   `scriptSig` can be abstracted as an arbitrary initial byte stack with a
   fresh lock opcode counter; the Lean composition proves the first modeled
   commitment origin for any such preceding evaluator. It does not establish
   that Core's execution of the generated lock refines `ByteMachine`, nor
   justify the Boolean outcomes.
4. Curve equations, accepted encodings, at most the appropriate number of
   recovery candidates, scalar reduction modulo N, and degenerate cases.
5. A correctly specified joint QROM model for SHA-256, SHA256d, and HASH160,
   including setup/signing transcripts and shared hash inputs.
6. A multi-target unopened-commitment bound with adaptive disclosures.
7. A fresh-message, covered-subset puzzle-search bound that applies to QSB's
   variable-subset FindAndDelete construction, with bonus choices and pinning.
   Its target event admits reused keys if a novel transaction hits any
   fixed-signature ECDSA recovery target, even without a sighash collision;
   the bound must cover those routes too. It cannot
   be computed by multiplying two independent DER-hit probabilities. The pin
   and final-round key byte strings can also be equal in the current model;
   distinct-input QROM bounds need a separate equality-case reduction.
8. Composition across multiple vaults/targets without unproved independence.
9. Refinement from the model to deployed implementations and binaries, plus
   the selected ledger's unspent-output, value, locktime, and consensus rules.

Items 2 and 7 are the immediate critical path. The first-round finding prevents
silently satisfying item 2 with the intended two-enforced-round model. The
current source is not changed to make the desired theorem true.

## Quantitative status

The exact syntactic DER-32 counting expression evaluates to target density
`780555 / 36893488147419103232`, approximately 2^-45.425859. It allows zero scalar
encodings and does not require an on-curve recovery value; real puzzle acceptance
is a subset. These facts still do not establish a query-success bound for the
protocol. The counting expression's combinatorial interpretation remains an
external argument until the BIP66 parser/counting correspondence is formalized.
The corresponding 20-byte DER expression has density
`390405 / 36893488147419103232`, approximately 2^-46.425388. If all 300 HORS
commitments are each marginally uniform 160-bit strings and the parser count
matches Core, a plain union bound gives at most
`300·390405 / 36893488147419103232` for **some** DER-shaped commitment; the
conditional union step is checked in Lean. A separate checked finite
random-function theorem supplies those marginals when R160 is sampled as a
whole uniform function independently of all input-selecting setup material,
even though the 300 evaluations share R160 and can collide. The mapping of
Core's 20-byte DER predicate to the counted target set remains unproved. This
does not bound the extraction gap: it has other possible causes, and the
Core-positive overshoot example used a crafted commitment rather than a
sampled one.
Separately, the checked cardinality injection bounds the **Lean** strict-DER
predicate by `12/256^6` on uniform twenty-byte outputs. Under the same
independent whole-function setup assumption, the 150 final-round commitments
have a conservative syntax-event union bound `150·12/256^6`. This avoids the
unproved exact DER count but still requires Core parser refinement and does not
bound unauthorized-spend probability.

The checked game-level measure theorem is a conditional implication, with
`NovelTwoPuzzle` as the source-shaped candidate target:

    Pr[UnauthorizedSpend] ≤ εFresh + εTwoPuzzle + εExtractionGap,

provided the three **explicit** event bounds hold for the same terminal game
distribution and honest release is respected. Fresh-opening and two-puzzle
events require an owner-forbidden projection, but not Bitcoin acceptance; they
remain computational targets separate from the QSB Script predicate. The gap
event records a bad transaction for which the source extractor fails to provide
a shaped pin/final
witness. No nontrivial upper bounds for εFresh, εTwoPuzzle, or εExtractionGap
are established. A zero gap would require the missing Bitcoin execution
refinement. Reporting a numerical QSB quantum security level now would be
unsupported.
The checked refinement separates the two-puzzle event by equality of the
extracted pinning and final-round key bytes:

    Pr[UnauthorizedSpend] ≤ εFresh + εDistinctKey + εSameKey + εExtractionGap.

The distinct-input QROM theorem cited in `RESEARCH.md` does not cover the
same-key event, and its transcript and relation hypotheses have not been
established for the distinct event. These are explicit event-bound premises,
not derived QSB probabilities.
