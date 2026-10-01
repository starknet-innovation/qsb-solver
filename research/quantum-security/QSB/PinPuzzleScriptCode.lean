import QSB.CoreFindAndDelete
import QSB.DERSyntax
import QSB.PinningScriptCode
import QSB.ByteLatePuzzle

/-!
The second pinning and late final `OP_CHECKSIGVERIFY` instructions use
`SHA256(key)` as a signature. Each is always 32 bytes. Core's BASE
`EvalChecksigPreTapscript`
constructs `CScript() << sig` and applies `FindAndDelete` to the current
scriptCode. A 32-byte direct push starts with opcode 0x20. The literal QSB
lock has no opcode at a parsed boundary with that byte, so source-shaped
FindAndDelete cannot remove anything, for any key. The separate
`EncodedScript.no_code_separator` theorem establishes that the full lock is
the starting legacy scriptCode for this literal fixture.

The theorem concerns the exact generated lock and source-shaped parser and
deletion models. Compiled-Core refinement, the signature checker, and the
transaction sighash remain separate obligations.
-/
namespace QSB.PinPuzzleScriptCode
open ByteMachine
open ScriptCodeSelection
open FindAndDelete

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def literalScript : Bytes := EncodedLayout.chunks.flatten

def puzzleScriptCode (sig : Bytes) : Bytes :=
  CoreFindAndDelete.run 880 literalScript (directPushPattern sig)

/-- There is no direct push of a 32-byte value in any of the 880 parsed
opcode chunks. This is a literal-lock certificate, not a general QSB
construction theorem. -/
theorem literal_no_push32 :
    EncodedLayout.chunks.all (fun chunk => chunk.head? != some 0x20) = true := by
  decide

theorem push32_head (sig : Bytes) (width : sig.length = 32) :
    (directPushPattern sig).head? = some 0x20 := by
  simp [directPushPattern, width]

theorem push32_rigid (sig : Bytes) (width : sig.length = 32) :
    rigidChunks (directPushPattern sig) EncodedLayout.chunks := by
  intro chunk present suffix
  have noHead : chunk.head? ≠ some 0x20 := by
    have noHeadBool := (List.all_eq_true.mp literal_no_push32) chunk present
    simpa using noHeadBool
  have patternHead := push32_head sig width
  constructor
  · intro matched
    have sameFirst := EncodedScript.head_eq_of_prefix_match
      (directPushPattern sig) chunk suffix
      (by simp [directPushPattern])
      (EncodedScript.literal_chunks_nonempty chunk present) matched
    exact False.elim (noHead (sameFirst.trans patternHead))
  · intro same
    subst chunk
    exact False.elim (noHead patternHead)

/-- Even if `sig` is chosen adaptively, no 32-byte signature is deleted from
the literal lock by the source-shaped legacy FindAndDelete loop. -/
theorem puzzleScriptCode_eq_literal (sig : Bytes)
    (width : sig.length = 32) :
    puzzleScriptCode sig = literalScript := by
  have noPattern : ∀ chunk ∈ EncodedLayout.chunks,
      chunk ≠ directPushPattern sig := by
    intro chunk present same
    have noHead := (List.all_eq_true.mp literal_no_push32) chunk present
    have equalHead : chunk.head? = some 0x20 :=
      (congrArg List.head? same).trans (push32_head sig width)
    simp [equalHead] at noHead
  have kept :
      EncodedLayout.chunks.filter (· ≠ directPushPattern sig) =
        EncodedLayout.chunks :=
    List.filter_eq_self.mpr (by
      intro chunk present
      simp [noPattern chunk present])
  have enough : EncodedLayout.chunks.length ≤ 880 := by
    simp [EncodedLayout.chunks_length]
  unfold puzzleScriptCode literalScript
  rw [CoreFindAndDelete.run_eq_model_scan]
  rw [scan_eq_chunk_filter (directPushPattern sig) EncodedLayout.chunks
    EncodedScript.literal_chunks_nonempty literal_stable_chunks
    (push32_rigid sig width) 880 enough]
  rw [kept]

/-- In particular, the SHA256 output of every initial pinning key selects
the unmodified generated lock as its BASE scriptCode in this source model. -/
theorem pin_hash_scriptCode_eq_literal (hashes : Hashes) (nonceKey : Bytes) :
    puzzleScriptCode (hashes.h256 nonceKey) = literalScript :=
  puzzleScriptCode_eq_literal (hashes.h256 nonceKey)
    (hashes.h256_width nonceKey)

/-- One successful arbitrary-stack byte-model execution reaches the fixed
nonce signature and the SHA256-derived puzzle signature. Its source-shaped
legacy deletion candidates are respectively the pin-deleted script and the
unmodified literal script. The supplied signature outcomes still need Core
checker refinement. -/
theorem accepted_pinning_scriptCodes (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : ByteMachine.State)
    (accepted : ByteMachine.run hashes ByteLayout.program
      (ByteMachine.State.mk stack outcomes 0) = some final) :
    ∃ nonceKey puzzleKey raw tail later,
      stack = nonceKey :: puzzleKey :: raw :: tail ∧
      outcomes = true :: true :: later ∧
      CoreFindAndDelete.run 880 literalScript FindAndDelete.pinPattern =
        stripEncodedChunks [FindAndDelete.pinPattern] EncodedLayout.chunks ∧
      puzzleScriptCode (hashes.h256 nonceKey) = literalScript := by
  obtain ⟨nonceKey, puzzleKey, raw, tail, later,
    shape, checks, _prefix, _flag, _pinCode⟩ :=
    PinningScriptCode.accepted_pinning_reached_bytes
      hashes stack outcomes final accepted
  exact ⟨nonceKey, puzzleKey, raw, tail, later, shape, checks,
    CoreFindAndDelete.pin_scriptCode_run,
    pin_hash_scriptCode_eq_literal hashes nonceKey⟩

/-- Both reached SHA256-derived puzzle signatures in the same successful
arbitrary-stack byte-model run have the full literal lock as their
source-shaped BASE scriptCode. The final key is the one later placed in the
last final CHECKMULTISIG key slot. Supplied signature outcomes remain an
explicit gap to actual Core verification. -/
theorem accepted_both_puzzle_scriptCodes (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : ByteMachine.State)
    (accepted : ByteMachine.run hashes ByteLayout.program
      (ByteMachine.State.mk stack outcomes 0) = some final) :
    ∃ pinKey finalKey beforeVerify beforeCheck,
      stack.head? = some pinKey ∧
      ByteMachine.run hashes (ByteLayout.program.take 856)
        (ByteMachine.State.mk stack outcomes 0) = some beforeVerify ∧
      beforeVerify.stack[1]? = some (hashes.h256 finalKey) ∧
      ByteMachine.run hashes (ByteLayout.program.take 879)
        (ByteMachine.State.mk stack outcomes 0) = some beforeCheck ∧
      beforeCheck.stack[10]? = some finalKey ∧
      puzzleScriptCode (hashes.h256 pinKey) = literalScript ∧
      puzzleScriptCode (hashes.h256 finalKey) = literalScript := by
  obtain ⟨pinKey, _puzzleKey, _raw, _tail, _later,
    shape, _checks, _pinCode, pinHashCode⟩ :=
    accepted_pinning_scriptCodes hashes stack outcomes final accepted
  obtain ⟨finalKey, beforeVerify, _beforeSuffix, beforeCheck,
    prefixRun, reached, _verify, sigAt, keyAt⟩ :=
    ByteLatePuzzle.accepted_whole_program_final_puzzle_key
      hashes (ByteMachine.State.mk stack outcomes 0) final accepted
  exact ⟨pinKey, finalKey, beforeVerify, beforeCheck,
    by simp [shape], prefixRun, sigAt, reached, keyAt,
    pinHashCode, pin_hash_scriptCode_eq_literal hashes finalKey⟩

/-- The source-shaped successful pinning puzzle gate forces strict DER and
passes the external ECDSA/sighash checker the unmodified lock scriptCode.
The checker result is a premise encoded in `success`; this is not a claim
about compiled Core accepting a transaction. -/
theorem successful_puzzle_gate (hashes : Hashes) (nonceKey puzzleKey : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool)
    (success : DERSyntax.verifyAllEncoding (hashes.h256 nonceKey) &&
      checker (hashes.h256 nonceKey) puzzleKey
        (puzzleScriptCode (hashes.h256 nonceKey)) = true) :
    DERSyntax.valid (hashes.h256 nonceKey) = true ∧
      checker (hashes.h256 nonceKey) puzzleKey literalScript = true := by
  have parts := success
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true] at parts
  have nonempty : hashes.h256 nonceKey ≠ [] := by
    intro empty
    have width := hashes.h256_width nonceKey
    simp [empty] at width
  rw [DERSyntax.verifyAllEncoding_nonempty _ nonempty] at parts
  simpa [pin_hash_scriptCode_eq_literal hashes nonceKey] using parts

end QSB.PinPuzzleScriptCode
