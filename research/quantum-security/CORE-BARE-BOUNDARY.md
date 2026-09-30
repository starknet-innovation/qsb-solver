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

`analysis/check_bare_script_boundary.py` reproduces five isolated cases with
the pinned native adapter; results are in `evidence/bare-script-boundary.json`.
In particular, non-push-only `OP_1 OP_1 OP_ADD` leaves `2` for a bare
`OP_2 OP_EQUAL` lock, and 201 `OP_NOP`s in each of `scriptSig` and the bare lock
are accepted. A 202nd counted opcode in either script is rejected. These are
source corroboration and boundary tests, **not** full QSB acceptance or a
formal interpreter equivalence proof.

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
`ExtractionGap` to zero. Later HORS selections, final signature provenance,
and the joint quantum hash bound remain independent open obligations.
