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
| Final CHECKMULTISIG signature-source roles, arbitrary byte stack | Every successful full generated byte-model run reaches the pre-CHECKMULTISIG state with ten signature-source cells in order: second bonus, first bonus, seven gathered generated dummy bytes, and fixed nonce; the next dummy cell is empty. The two bonus bytes obey the classified dummy/commitment source branches, and seven signed openings match distinct original HORS commitments. The sole possible bonus commitment is identified by an original HORS position absent from those seven openings. | `QSB/FinalBonusSecond.accepted_whole_program_final_signature_origins` combines the exact two-roll shallow-cell invariant with `QSB/ByteLatePuzzle.accepted_generated_final_witness_origins`, retaining the actual reached post-bonus and pre-CHECKMULTISIG states. The signed-pool trace now retains a permutation of opened and surviving original positions; `first_remaining_commitment_unopened` proves the exception's unopened origin. Signature outcomes remain supplied Booleans; this is not Core DER/FindAndDelete/sighash/ECDSA verification or a quantum success bound. |
| Conditional bonus setup exception | If both reached final bonus signature slots satisfy an externally supplied syntax predicate, and all 150 generated second-round HORS commitments fail that predicate, both bonus depths are strictly below 152. | `QSB/FinalBonusSecond.no_bonus_commitment_of_signature_syntax` derives this from the same full byte-model run, its exact pre-CHECKMULTISIG prefix, and the unopened commitment origin. The model does not establish the syntax premise: Core signature parsing and successful multisignature verification still require refinement. The hash-distribution probability of the bad setup remains a separate obligation. |
| Final bonus setup syntax probability | If each of the 150 second-round commitments has actual parser-syntax marginal at most `390405/2^65`, the probability that any of them is syntax-valid is at most `150·390405/2^65`. | `QSB.der20_final_bonus_setup_union_bound` is a checked measure union bound without independence. The marginal premise and Core parser/count correspondence remain external; this covers only this final bonus setup event, not all extraction gaps or unauthorized spends. |
| Core-shaped matching interface for bonus syntax | If the reached final ten-signature/ten-key scan succeeds under a per-pair verifier whose success entails signature syntax, and no generated second-round commitment satisfies that syntax, both bonus depths are below 152. | `QSB/FinalBonusSecond.matched_final_signature_has_syntax` derives syntax of each slot from the equal-count matching loop. `no_bonus_commitment_of_matching_verifier` composes it with the full byte-model source trace. Relating the external pair verifier and scan result to Core's actual parser, FindAndDelete, sighash, and ECDSA remains open. |
| Source-shaped strict DER predicate | A 20-byte byte string accepted by the Lean predicate has positive R and S byte lengths summing to 13, with the six required DER header/length bytes. The crafted overshoot signature passes; a wrong sequence-length variant fails. | `QSB/DERSyntax.lean` translates the checks in Core 27.2 `IsValidSignatureEncoding`, including the trailing sighash byte. This is a Lean predicate and structural theorem, not a proof of compiled-Core equivalence or a full cardinality/bijection theorem for the earlier DER-20 count expression. |
| Literal final-round setup | None of the 150 second-round HORS commitments in the one disposable generated lock passes the source-shaped strict DER predicate. Under a successful ten-pair scan with a DER-sound verifier, both bonus depths are therefore below 152 for that lock. | `QSB/FinalBonusDER.lean` checks all 150 literal bytes with kernel reduction and specializes the conditional matching theorem. It is not a statement about every generated vault; Core binary refinement and a random-setup bound remain open. |
| Combined modeled bare boundary | In one truthy modeled run after any partial scriptSig evaluator, the first signed comparison has lock-owned commitment origin and the final CHECKMULTISIG has both count operands 10 and a true supplied outcome. | `QSB/BareBoundary.accepted_bare_first_origin_and_final_counts` composes the two arbitrary-stack results for the same execution. The later byte-model theorem establishes all seven signed and two bonus source roles under supplied outcomes, with an explicit commitment bonus branch. Core refinement and a probability bound remain open. |
| Generated layout | Last final-round bonus index 152 selects locking-script commitment C[round 2,7], and the symbolic trace completes if final multisignature success is supplied | A concrete role escape in the stack model. Symbolic signature outcomes alone cannot establish final-round dummy-signature shape. |
| Generated layout | First final-round bonus index 152 also selects locking-script commitment C[round 2,7]; setting the second bonus index to 11 leaves a truthy symbolic trace with that commitment in a final signature slot | `QSB/FirstBonus.lean` checks the exact probe and final stack position. It assumes supplied signature outcomes and canonical preceding signed selections; the altered-lock Core experiment below tests the DER-shaped case. |
| Bonus region | After the canonical preceding eight final-round selections, the final bonus roll's 153 reachable cells are exactly eight gathered dummy signatures, the fixed nonce signature, the zero dummy, 142 unused dummy signatures, and commitment C[round 2,7] | `QSB/Bonus.lean` checks the exact generated prefix region and all 153 index roles. This is conditional on the preceding canonical stack; it does not prove arbitrary-witness extraction. |
| Bonus region | For indices 0–9, rolling the reachable region places a nonzero generated dummy at the prospective NULLDUMMY slot; indices 10–152 preserve zero there | Local stack-order theorem, not a complete Core-acceptance classification. Later pubkey rolls and arbitrary witness layouts still need refinement. |
| Byte index | A source-shaped four-byte sign-magnitude ScriptNum parser maps nonminimal `0a00` to 10, nonminimal `980000` to 152, `9880` to -152, and rejects five bytes | `QSB/ByteIndex.lean` checks these byte cases and their local bonus-role consequences. Equivalence to compiled Core for every byte sequence remains unproved; the native boundary cases corroborate the selected examples. |
| Byte index | A source-shaped ScriptNum serializer produces the checked encodings of zero, ten and both signs of 152, with checked round trips for zero and positive 152 | The serializer is scoped to at most five magnitude bytes; no all-values parser/serializer equivalence or Core refinement has been proved. |
| Byte lock | The generated literal-byte lock has 880 instructions, ends in `CHECKMULTISIG`, and has 15 `EQUALVERIFY` opcodes, each immediately preceded by `HASH160` | `QSB/ByteLayout.lean` is generated from the pinned builder and checked against the existing exact script SHA-256. These are syntactic facts, not an arbitrary-witness run theorem. |
| Byte execution | For arbitrary stack tails, cost and later opcodes, successful execution after a reached `HASH160; EQUALVERIFY` pair implies that the hash of the actual opening bytes equals the compared bytes; `run_append` lifts this implication into any executed program prefix | `QSB/ByteMachine.lean` models byte equality with arbitrary hash functions. It does not show that the compared bytes are one of the intended HORS commitments. Signature outcomes, FindAndDelete, sighash and ECDSA remain external. |
| Byte trace | Erasing the equality-pair trace gives the same final state as the byte interpreter for every program and starting state | `QSB/ByteTrace.lean`; the trace records equal byte pairs, but a whole-lock theorem relating every pair to its intended commitment position is still missing. |
| Byte witness | One disposable 57-cell witness completes the 880-instruction byte interpreter with 201 counted operations, 569 final stack cells, and 15 reached hash comparisons; its final truth depends on the final multisignature Boolean, not the first | `QSB/ByteWitness.lean` uses a generated lookup HASH160, arbitrary constant SHA256, and externally supplied signature outcomes. It checks model consistency, not actual cryptography, Core acceptance or arbitrary witnesses. |
| Final count | For any underlying stack, successful execution of the lock's ten fixed final key rolls leaves the pushed signature count 10 at stack offset 10; the last push gives public-key count 10 | `QSB/KeyRolls.lean` proves the list invariant and checks the generated 23-instruction suffix. This does not identify which arbitrary cells were selected as keys or signatures. |
| Final matching | In a Core-shaped key-scanning model, success with equal signature/key counts implies every corresponding pair verifies | `QSB/Multisig.lean` proves this for arbitrary lists and verifiers; `QSB/KeyRolls.lean` applies it to the ten cells in the final stack. Equality with Core's actual DER, FindAndDelete, sighash and ECDSA behavior is a separate refinement obligation. |
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

`round-results.json` records seven cases through the app's actual Core adapter:

- Original synthetic witness against the **modified** lock: accepted.
- Invalid round-1 dummy signature/key pair: accepted.
- Invalid round-2 dummy signature/key pair: rejected.
- Incorrect round-1 HORS preimage: rejected.
- Incorrect round-2 HORS preimage: rejected.
- Changed destination with freshly recovered nonce keys: accepted.
- Changed destination with the **old round-1 nonce key**: accepted. The
  independent CPU check confirms that old key no longer verifies the
  first-round nonce signature on the new transaction. Pinning and round 2 do.

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
The SINGLE-bug signature continues to verify after destination and amount change.
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
| worker/cpu/bitcoin_tx.py:485 | Pinning: fixed signature check, hash key, puzzle signature check | Isolated Core semantics; future pinning extraction. |
| worker/cpu/bitcoin_tx.py:545 | OP_MIN/ROLL/HASH160 selection and bonus logic | `Selection` local lemmas and the literal-byte interpreter; complete arbitrary-witness invariant pending. |
| worker/cpu/bitcoin_tx.py:598 | CHECKMULTISIG ending each round | First-round result experiment; final-round binding needs extraction. |
| worker/cpu/bitcoin_tx.py:749 | Concatenation of the two rounds, with first result left on stack | Structural first-round finding. |
| worker/cpu/bitcoin_tx.py:131 | Legacy sighash and SINGLE bug | Isolated Core mutation evidence; serialization injectivity pending. |
| worker/cpu/bitcoin_tx.py:199 | FindAndDelete implementation | Must match Core boundary semantics; not replaced by abstract subset deletion in any claimed full proof. |
| worker/cpu/secp256k1.py | Curve operations and DER/recoverability checks | CPU experiment oracle; full Lean correctness not claimed. |
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
   Its target event admits reused keys if a novel transaction collides under
   the fixed-signature sighash; the bound must cover that route too. It cannot
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
