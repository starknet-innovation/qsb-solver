# Bare-script execution boundary (Core 27.2)

This note isolates one part of the real-to-Lean obligation. The inspected
Config A output is a **bare legacy script** (see `SPECIFICATION.md` and
`evidence/source-inventory.json`). The app's native adapter calls
`bitcoinconsensus_verify_script_with_spent_outputs` with the official Core
27.2 `VERIFY_ALL` flag set for both inputs. Its build script downloads the
checksummed Core 27.2 release. These facts identify the intended interpreter;
the experiment below uses the pinned local native binary and image.

## What Core does at this boundary

In [Core 27.2 `VerifyScript`](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1956-L2025), the `SIGPUSHONLY` test is conditional
on its flag. The [consensus API `VERIFY_ALL` definition](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/bitcoinconsensus.h#L48-L62)
does **not** contain `SIGPUSHONLY`, `MINIMALDATA`, `NULLFAIL`, or `CLEANSTACK`.
The P2SH-specific push-only check and redeem-script stack pop occur only when
`scriptPubKey.IsPayToScriptHash()` is true. That branch is false for Config A's
bare output. Thus `scriptSig` need not be push-only for this adapter; its
opcodes may create any stack allowed by Core's other consensus checks.

`VerifyScript` first evaluates `scriptSig`, then evaluates `scriptPubKey` on the
same stack. Failure in the first call aborts verification. The
[Core 27.2 `EvalScript` body](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L414-L467)
creates its own `nOpCount = 0` and local altstack on each invocation. The
scriptSig's counted operations therefore do not consume the bare lock's
201-opcode budget, and its altstack does not carry into the lock. A successful
scriptSig supplies an ordinary byte-vector stack at the lock entrance. Core
checks the combined main/altstack size after each instruction
([source](https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/interpreter.cpp#L1216-L1223)).

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

`analysis/check_bare_script_boundary.py` reproduces five isolated cases with
the pinned native adapter; results are in `evidence/bare-script-boundary.json`.
In particular, non-push-only `OP_1 OP_1 OP_ADD` leaves `2` for a bare
`OP_2 OP_EQUAL` lock, and 201 `OP_NOP`s in each of `scriptSig` and the bare lock
are accepted. A 202nd counted opcode in either script is rejected. These are
source corroboration and boundary tests, **not** full QSB acceptance or a
formal interpreter equivalence proof.

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
