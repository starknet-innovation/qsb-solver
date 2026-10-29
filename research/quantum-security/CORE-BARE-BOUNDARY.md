# Bare-script execution boundary (Core 27.2)

This note isolates one part of the real-to-Lean obligation. The inspected
Config A output is a **bare legacy script** (see `SPECIFICATION.md` and
`evidence/source-inventory.json`). The app's native adapter calls
`bitcoinconsensus_verify_script_with_spent_outputs` with the official Core
27.2 `VERIFY_ALL` flag set for both inputs. Its build script downloads the
checksummed Core 27.2 release. These facts identify the intended interpreter;
the experiments below use checksum-verified native builds.

## What Core does at this boundary

In [Core 27.2 `VerifyScript`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1805-L1915), the `SIGPUSHONLY` test is conditional
on its flag. The [consensus API `VERIFY_ALL` definition](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/bitcoinconsensus.h#L48-L62)
does **not** contain `SIGPUSHONLY`, `MINIMALDATA`, `NULLFAIL`, or `CLEANSTACK`.
The P2SH-specific push-only check and redeem-script stack pop occur only when
`scriptPubKey.IsPayToScriptHash()` is true. That branch is false for Config A's
bare output. Thus `scriptSig` need not be push-only for this adapter; its
opcodes may create any stack allowed by Core's other consensus checks.

`VerifyScript` first evaluates `scriptSig`, then evaluates `scriptPubKey` on the
same stack. Failure in the first call aborts verification. The
[Core 27.2 `EvalScript` body](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L378-L403)
creates its own `nOpCount = 0`, local altstack, and `pbegincodehash` at the
start of the supplied script on each invocation. The scriptSig's counted
operations therefore do not consume the bare lock's
201-opcode budget, and its altstack or `OP_CODESEPARATOR` position does not
carry into the lock. A successful scriptSig supplies an ordinary byte-vector
stack at the lock entrance. Core
checks the combined main/altstack size after each instruction
([source](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1124-L1129)).

For later oracle accounting, `QSB/ScriptSigQueryBudget.lean` gives a
source-shaped trace bound for one successful BASE `scriptSig` evaluation.
Core counts every opcode above `OP_16`, including those in skipped branches,
and caps this count at [201](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/script.h#L24-L31).
Its executed [hash cases](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L943-L969)
are SHA256, RIPEMD160, HASH160, HASH256, and SHA1; the first four cost at
most two combined idealized H/R calls each, while SHA1 is outside that pair.
One CHECKSIG attempt costs at most two H calls through legacy
[SignatureHash](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1495-L1508)
and [`HashWriter::GetHash`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/hash.h#L100-L118).
The [CHECKMULTISIG loop](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1022-L1089)
charges its declared key count to `nOpCount` before making at most that many
ECDSA attempts. Lean therefore proves `H_calls + R_calls ≤ 402` for a trace
classified by these source cases and satisfying the 201-count premise. This
does not extract an event trace from compiled Core, cover hashes outside this
one `EvalScript` invocation, or bound the adversary's coherent queries.

The [Core 27.2 `CScriptNum` constructor and `set_vch`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/script.h#L226-L396)
reject more than four operand bytes, optionally enforce minimal encoding, and
assemble the remaining little-endian bytes by OR-ing disjoint shifted lanes.
For this adapter, `MINIMALDATA` is absent from `VERIFY_ALL`, so that optional
minimality test is off. `QSB/ByteIndex.lean` now proves for **every** byte list
that an OR-based recursive assembly equals the arithmetic little-endian word
used by its parser, and that the word is below `256^length`. It also proves
that substituting the OR assembly into the source-shaped sign-magnitude
parser leaves every result unchanged. A further theorem bounds every parsed
value by ±2,147,483,647, so the `getint` saturation in Core's `OP_ROLL`
path cannot change a successfully parsed four-byte operand. This checks the
disjoint-byte-lane arithmetic. A separate theorem shows that, for each
negative one- to four-byte encoding, subtraction of the sign bit equals
retaining precisely the lower bits. `QSB/CoreScriptNum.lean` additionally
models the final-byte bitwise sign test and the 64-bit complement mask from
Core's source, proving this source-shaped conversion equals the Lean parser
for every byte list after the four-byte guard. Its assembled word is below
`2^63` whenever the guard passes, so the source-shaped accumulation fits the
signed storage type. Compiled C++ execution and the
whole opcode trace still need refinement to Lean.
`QSB/ByteIndexRange.lean` also proves that the optional Lean serializer is
defined for the sum and minimum of any two successfully parsed operands;
this removes a model-only failure branch from `OP_ADD` and `OP_MIN`.
`QSB/CoreSerialize.lean` models Core's repeated low-byte/divide magnitude
loop, proves its decoded value and fuel stability below the corresponding
power of 256, and proves equality with the byte model's source-shaped
serializer for every integer. The previous finite check from −1023 to 1023
remains as a round-trip regression. Equality with compiled C++ and the full
interpreter trace remain unproved.
`QSB/CoreRoll.lean` proves that the source-shaped bottom-first `OP_ROLL`
select/erase/append operation, including raw-index parsing, is the reverse
of the top-first `ByteMachine.step .roll` stack result when its opcode budget
passes. It quantifies over arbitrary byte stacks and encodings. The theorem
does not yet show that compiled Core executes that Lean operation at each
reached instruction of the generated lock. An 11-case pinned-Core bare-script
probe in `analysis/check_roll_core.py` and `evidence/roll-core.json` corroborates
the depth boundary, negative-zero and nonminimal encodings, and rejection of
negative, out-of-range, and five-byte indices. It does not cover every stack
or the full QSB lock.

`analysis/check_bare_script_boundary.py` reproduces fifteen isolated cases with
the pinned native adapter; results are in `evidence/bare-script-boundary.json`.
In particular, non-push-only `OP_1 OP_1 OP_ADD` leaves `2` for a bare
`OP_2 OP_EQUAL` lock, and 201 `OP_NOP`s in each of `scriptSig` and the bare lock
are accepted. A 202nd counted opcode in either script is rejected. These are
source corroboration and boundary tests, **not** full QSB acceptance or a
formal interpreter equivalence proof.

`analysis/check_scriptsig_isolation_core.py` adds seven isolated
`SIGHASH_ALL` CHECKSIG cases against the checksum-verified Core 27.2 macOS
consensus library (`evidence/scriptsig-isolation-core.json`). A fixed
signature and key verify with a push-only scriptSig, with
`OP_CODESEPARATOR` before or after the key, with executed `EQUALVERIFY` or
`ADD; DROP` before that separator, and with an extra lower stack cell. A
wrong-key control rejects. The app's source-shaped ALL digest stays equal
across all seven scriptSig variants; Core accepts the six valid-key cases.
This corroborates the separate-`EvalScript` boundary for these synthetic
inputs, not the generated QSB lock or a universal Core-to-Lean proof.

Seven of the earlier fifteen cases leave scriptSig-supplied bytes on top through a
bare `OP_NOP` lock and check [Core's final `CastToBool`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L32-L45)
decision, including empty, zero, negative-zero, and noncanonical truthy
encodings. `QSB/CoreFinalTruth.lean` models that source loop and proves a
general bridge: after any successful modeled program ending in
`CHECKMULTISIG`, the top cell is its canonical Boolean, so source-shaped
`CastToBool` equals the byte model's final truth check. The exact 880-opcode
lock satisfies that ending. This removes a final-result predicate mismatch
*inside the Lean models*; compiled-Core execution and signature outcomes
remain outside the theorem.

`analysis/check_scriptnum_core.py` adds a finite differential check of
`OP_1ADD` on 2,384 selected zero- to four-byte encodings, including every
one-byte encoding, every canonical signed integer from −1023 through 1023,
and sign/nonminimal four-byte boundaries. It checks Core's serialized result
against an independent sign-magnitude calculation in 27 locks below the
201-opcode limit, and checks one five-byte operand rejection.
The pinned adapter accepted all 27 batches and rejected the oversized
operand; exact binary/image hashes and transaction hashes are in
`evidence/scriptnum-core.json`. The test helper's `bitcoin_tx.py` hash still
matches the original source inventory even though the app checkout revision
has advanced. This supports the parser model at the tested
points; it is not a universal compiled-Core refinement theorem.

## What is checked in Lean

`QSB.PinningShape.accepted_arbitrary_initial_stack_first_origin` quantifies
over every byte stack and Boolean signature-outcome list at the start of the
generated 880-instruction byte model. `QSB.BareBoundary` composes it with **any**
partial `scriptSig` evaluator returning a byte stack and starts the generated
lock with a fresh modeled opcode counter. Consequently, every successful
*modeled* bare composition selects a first HORS commitment from the fixed lock
region, regardless of how the preceding evaluator made the stack. No
push-only or canonical scriptSig-layout hypothesis remains in that statement.
The combined theorem `accepted_bare_first_origin_and_final_counts` also fixes
the two final count operands to ten and requires the supplied final
multisignature outcome true in the **same** truthy modeled run.

The remaining bridge is concrete: for every Core-accepted transaction against
the exact Config A bare script, show that Core's lock `EvalScript` trace maps to
a successful `ByteMachine.run` trace with the same initial byte stack, actual
SHA-256/HASH160 values, and signature outcomes justified by Core. This entails
exact bytecode decoding, ScriptNum and `OP_ROLL`, 520-byte element and
1000-cell stack limits, the independent 201-opcode count, every
`CHECK(MULTI)SIG` stack effect, and final truth. `ByteMachine` currently uses
externally supplied Boolean signature outcomes and does not model
FindAndDelete, sighash, DER/hashtype/key parsing, or ECDSA. Therefore the
source inspection and this Lean composition do **not** set the game's
`ExtractionGap` to zero. Later full-run byte-model theorems now identify the
seven final HORS openings and the final signature-source slots from an
arbitrary initial byte stack. Core execution and signature-checker refinement,
the nonce and puzzle relations, and the joint quantum hash bound remain open.

`QSB/CoreCheckedWire.lean` supplies an exact-byte validation boundary for an
individual lock. Its executable `matchesWire` checks supplied script bytes
against the parameterized Lean serialization, and Lean proves that a truthy
checked execution of matching bytes has the joint source event. The literal
disposable 880-chunk fixture passes this check in Lean. This removes a
universal Python-builder theorem from the *individual validated-lock* path,
but a real transaction's spent-output bytes still need to be supplied and
checked, and compiled Core's execution must still refine the Lean parser,
stack transitions, and signature checker. `QSB/DynamicRoundWitness.lean`
computes the nine-position good-setup witness from that checked source-model
run and retains the two DER puzzle hits and fixed ALL verifier calls. The
computation has no arbitrary Core transaction parser or compiled-Core
refinement. Core 27.2's
[multisignature source case](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1022-L1120)
applies FindAndDelete for every reached signature to one scriptCode before the ordered
pair scan, then cleans up the counted arguments and checks NULLDUMMY. The
Lean source model follows that order; source inspection and the isolated
native cases do not prove the universal C++-to-Lean relation.
`QSB/DynamicRawSource.lean` now obtains the selected scriptSig from a complete
raw transaction through the Lean envelope parser. It accepts any evaluator
function for that scriptSig, including one capable of non-push opcodes, and
feeds its returned stack to the checked-source extractor. The exact missing
claim is that Core parses the same transaction and that its successful
scriptSig and bare-lock executions produce this modeled result. The spent
output's script bytes must also be supplied from the same ledger context.

The disposable witness has an exact modeled lower-stack capacity threshold:
`QSB.ByteStackFrame.canonical_arbitrary_bottom_tail` proves that any suffix
of at most 385 byte cells preserves final truth, while
`canonical_arbitrary_bottom_tail_byte_run_rejects` proves rejection for every
suffix of 386 or more cells. The proof includes `OP_ROLL` and
`CHECKMULTISIG`, and depends only on cell count, not cell contents.
`analysis/check_full_two_outputs_core.py` now also checks three pinned native
cases with nonempty lower cells: 385 distinct 20-byte values pass, 386 fail,
and 384 empty cells plus a 520-byte value pass. Their scriptSigs are 9,234,
9,255, and 2,056 bytes respectively. These cases corroborate the modeled
boundary for specific witnesses, not the universal compiled-Core bridge.

`QSB.CoreStructuralEquiv.run_eq_byte` proves exact agreement between the
bottom-first Core-shaped and top-first byte *Lean* interpreters for arbitrary
initial stacks and supplied signature outcomes, including rejection paths and
the false first-round multisignature result. Its lower-stack frame and overflow
corollaries also agree. This removes a one-way model-composition gap, but the
source-shaped interpreter is still a mathematical translation of inspected
Core cases, not a proof about the compiled C++ interpreter or ECDSA outcomes.

`QSB.LockOpcodeInventory.program_skeleton` proves that every parameterized
Lean Config A lock has the fixture's exact ordered opcode kinds. Its checked
counts are 699 pushes, 90 ROLL, 18 MIN, 17 DUP, 15 each of ADD, HASH160 and
EQUALVERIFY, four CHECKSIGVERIFY, three SHA256, two CHECKMULTISIG, and one
each of OVER and SWAP. These total 880 instructions; 181 exceed `OP_16` and
consume Core's ordinary opcode count. Reached CHECKMULTISIG key counts are
charged separately. This identifies the finite Core source cases that need
transition refinement for every admitted lock shape; it does not itself prove
that the compiled C++ interpreter implements the Lean steps.

`QSB.ByteMachineQueries.lock_queries_le_33` adds the hash-opcode oracle
accounting for the same inventory: the byte-model run of every parameterized
lock records at most 33 idealized calls. The new
`lock_queries_exact_of_success` proves that a successful run records exactly
33: 15 H plus 15 R from `HASH160` and 3 H from `SHA256`.
`run_congr` proves the run depends on the hash functions only at those
recorded inputs. `QSB.LockSignatureQueryBudget` instruments the source-shaped
multisignature scan without changing its result and proves at most one verifier
attempt per reached key. Every successful full parameterized checked run
reaches both static ten-key fragments, whose combined pair attempts are at
most 20 even if the first-round Boolean is false.
`QSB.JointLegacyDigestQueries` gives one modeled legacy digest an exact trace:
zero H calls for an invalid input or out-of-range SINGLE, and two ordered H
calls for a present preimage. The four `CHECKSIGVERIFY` sites and two ten-key
sites reserve at most 48 H calls when each verifier uses one such digest; with
the 33 opcode calls, the static lock allowance is 81. This is not a
combined query trace for the checked run: `validKey` and `verify` are external,
and their own oracle use, the scriptSig, and compiled Core remain outside it.
`QSB.LockOpcodeBudget.lock_run_ops_from_zero` proves that both ten-key
`CHECKMULTISIG` count pushes are static, so every successful byte-model run of
every parameterized lock ends with the opcode counter at exactly 201, Core's
cap, and `lock_rejects_extra_counted_op` shows that one further counted
opcode is rejected by the modeled cap. `lock_rejects_prepended_counted_op`
now models the prepended case as well: one counted opcode before the lock
leaves the counter at 191 before the final ten-key check, whose charge would
reach 202, so the modeled run fails, and the native prepended-`OP_NOP` case in
`evidence/full-two-outputs-opcount-core-macos.json` corroborates this for the
fixture only. The lock therefore sits exactly on
Core's `MAX_OPS_PER_SCRIPT` boundary: any discrepancy between the modeled
count and Core's `nOpCount`, including the key-count charge, would change
acceptance. Native acceptance of the fixture corroborates the count at that
boundary for the fixture only. These are statements about the Lean models,
not about compiled Core.

The optional lock-side extension to `analysis/check_full_two_outputs_core.py`
(`--extra-lock-opcount-cases`) probes that boundary from the lock side with
the same disposable puzzle-relaxed full lock. Each `OP_2DROP` relaxation
counts one opcode, as the replaced `CHECKSIGVERIFY` did, so the test lock also
totals 181 counted opcodes plus two ten-key charges. Each case rebuilds the
witness for its changed lock. The checksum-verified Core 27.2 macOS library
accepts the unchanged lock; rejects it with one `OP_NOP` appended after the
final `CHECKMULTISIG`, where that NOP is the 202nd ordinary count; rejects it
with one `OP_NOP` prepended before the first push, where every ordinary count
stays within the cap and only the final ten-key charge can exceed it; and
accepts an appended uncounted `OP_1`. The 32-case report is
`evidence/full-two-outputs-opcount-core-macos.json`. The harness without
either option still reproduces the 28-case macOS report byte-for-byte, and
with `--extra-scriptsig-cases` the 33-case report. This is a finite fixture
check that Core's `nOpCount`, including the key-count charge, reaches exactly
201 on this lock; it is not a universal refinement of the modeled count.

The optional full-lock `scriptSig` extension to
`analysis/check_full_two_outputs_core.py` tests the same canonical disposable
witness with five stack-preserving non-push tails. The checksum-verified
Core 27.2 macOS library accepts 201 trailing `OP_NOP`s, a trailing
`OP_CODESEPARATOR`, a skipped SHA256 branch, and a TOALTSTACK/FROMALTSTACK
round-trip; it rejects 202 trailing `OP_NOP`s. The 33-case report is
`evidence/full-two-outputs-scriptsig-core-macos.json`. Running the harness
without the option reproduces the original 28-case macOS report byte-for-byte.
Three puzzle CHECKSIGVERIFY sites are still replaced by OP_2DROP in this
experiment. These are finite checks of the scriptSig/lock separation on the
otherwise complete stack path, not a universal compiled-Core refinement.
