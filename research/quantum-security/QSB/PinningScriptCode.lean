import QSB.PinningShape
import QSB.FindAndDelete
import QSB.DERSyntax

/-!
Pinning witnesses for an arbitrary initial byte-model stack. The exact
six-opcode prefix reaches the fixed ALL signature and the SHA256 of the same
initial key. The verifiers remain explicit, because ByteMachine's supplied
Booleans do not establish Bitcoin Core's signature checks.
-/
namespace QSB.PinningScriptCode
open ByteMachine
open FirstOvershoot

/-- A successful full byte-model run fixes both keys and both signature
bytes reached by the pinning CHECKSIGVERIFY opcodes. It also gives the
post-pinning state without assuming a canonical scriptSig stack. -/
theorem accepted_pinning_reached_bytes (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final) :
    ∃ nonceKey puzzleKey raw tail later,
      stack = nonceKey :: puzzleKey :: raw :: tail ∧
      outcomes = true :: true :: later ∧
      run hashes (ByteLayout.program.take 6)
        (State.mk stack outcomes 0) =
        some (State.mk (raw :: tail) later 5) ∧
      pinSignature.getLast? = some 0x01 ∧
      FindAndDelete.scan 880 EncodedLayout.chunks.flatten
        FindAndDelete.pinPattern =
        ScriptCodeSelection.stripEncodedChunks
          [FindAndDelete.pinPattern] EncodedLayout.chunks := by
  obtain ⟨nonceKey, puzzleKey, raw, tail, later, shape, checks⟩ :=
    PinningShape.accepted_initial_shape hashes stack outcomes final accepted
  subst stack
  subst outcomes
  have smallTail := FirstAcceptedOrigin.accepted_postindex_tail_small
    hashes nonceKey puzzleKey raw tail later final accepted
  have small : (raw :: tail).length ≤ 996 := by
    simp only [List.length_cons]
    omega
  exact ⟨nonceKey, puzzleKey, raw, tail, later, rfl, rfl,
    modeled_pinning_consumes_two_keys hashes nonceKey puzzleKey
      (raw :: tail) later small,
    FindAndDelete.pin_signature_sighash_all,
    FindAndDelete.pin_scriptCode_scan⟩

/-- With an external successful-pair bridge and the VERIFY_ALL encoding gate,
SHA256 of the actual pinning nonce key is strict DER. The bridge must prove
that Core checks the two reached pairs against their transaction sighashes;
this theorem does not replace that requirement. -/
theorem matched_run_pinning_der_puzzle (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final)
    (nonceVerify puzzleVerify : Bytes → Bytes → Bool)
    (matched : ∀ nonceKey puzzleKey raw tail,
      stack = nonceKey :: puzzleKey :: raw :: tail →
      nonceVerify pinSignature nonceKey = true ∧
      puzzleVerify (hashes.h256 nonceKey) puzzleKey = true)
    (puzzleVerifyEncoding : ∀ sig key,
      puzzleVerify sig key = true →
      DERSyntax.verifyAllEncoding sig = true) :
    ∃ nonceKey puzzleKey raw tail later,
      stack = nonceKey :: puzzleKey :: raw :: tail ∧
      outcomes = true :: true :: later ∧
      nonceVerify pinSignature nonceKey = true ∧
      puzzleVerify (hashes.h256 nonceKey) puzzleKey = true ∧
      DERSyntax.valid (hashes.h256 nonceKey) = true := by
  obtain ⟨nonceKey, puzzleKey, raw, tail, later, shape, checks,
    _prefix, _flag, _scriptCode⟩ :=
    accepted_pinning_reached_bytes hashes stack outcomes final accepted
  obtain ⟨nonceMatched, puzzleMatched⟩ :=
    matched nonceKey puzzleKey raw tail shape
  have encoded := puzzleVerifyEncoding _ _ puzzleMatched
  have nonempty : hashes.h256 nonceKey ≠ [] := by
    intro empty
    have width := hashes.h256_width nonceKey
    simp [empty] at width
  rw [DERSyntax.verifyAllEncoding_nonempty _ nonempty] at encoded
  exact ⟨nonceKey, puzzleKey, raw, tail, later, shape, checks,
    nonceMatched, puzzleMatched, encoded⟩

end QSB.PinningScriptCode
