import QSB.PinPuzzleScriptCode
import QSB.CorePushSerialize

/-!
A source-shaped BASE `EvalChecksigPreTapscript` model for the pinned Core
27.2 `bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL` mask. That public mask has
DERSIG, but omits LOW_S, STRICTENC, NULLFAIL, CONST_SCRIPTCODE, and
MINIMALDATA. Core first applies legacy FindAndDelete to the current
scriptCode, then the DER encoding gate, then `CheckECDSASignature`. The latter
rejects an invalid public key or empty signature, removes the signature's
last byte as `nHashType`, computes `SignatureHash`, and checks ECDSA.

`validKey` and `verify` are explicit external functions. In particular,
`verify` must eventually be refined to Core's parsed secp256k1 key, exact
legacy sighash for its `hashType`, and ECDSA verifier. This module proves
source-model consequences, not compiled-C++ equivalence or spend acceptance.
-/
namespace QSB.CoreChecksigEval
open ByteMachine

abbrev VerifyECDSA := Bytes → Bytes → Bytes → UInt8 → Bool

/-- The source-shaped return value of `EvalChecksigPreTapscript` in BASE mode.
`none` represents a DER-gate script failure; `some false` represents a valid
encoding whose ECDSA check failed, which `OP_CHECKSIGVERIFY` then rejects. -/
def evalBaseVerifyAll (fuel : Nat) (script sig key : Bytes)
    (validKey : Bytes → Bool) (verify : VerifyECDSA) : Option Bool :=
  let scriptCode := CoreFindAndDelete.run fuel script
    (ScriptCodeSelection.directPushPattern sig)
  if DERSyntax.verifyAllEncoding sig then
    match sig.getLast? with
    | none => some false
    | some hashType =>
        some (validKey key && verify sig.dropLast key scriptCode hashType)
  else none

/-- The literal source-order variant uses Core's full `CScript() << sig`
serialization, including PUSHDATA1/2 for long signatures. -/
def evalBaseVerifyAllCore (fuel : Nat) (script sig key : Bytes)
    (validKey : Bytes → Bool) (verify : VerifyECDSA) : Option Bool :=
  let scriptCode := CoreFindAndDelete.run fuel script
    (CorePushSerialize.pushPattern sig)
  if DERSyntax.verifyAllEncoding sig then
    match sig.getLast? with
    | none => some false
    | some hashType =>
        some (validKey key && verify sig.dropLast key scriptCode hashType)
  else none

/-- Long signatures fail the pinned DERSIG gate, so the old direct-only
deletion shortcut and the full Core push serializer have the same *result*
under VERIFY_ALL, even though they can compute different intermediate
scriptCodes before that fatal gate. -/
theorem evalBaseVerifyAll_eq_core (fuel : Nat) (script sig key : Bytes)
    (validKey : Bytes → Bool) (verify : VerifyECDSA) :
    evalBaseVerifyAll fuel script sig key validKey verify =
      evalBaseVerifyAllCore fuel script sig key validKey verify := by
  by_cases short : sig.length < 76
  · simp [evalBaseVerifyAll, evalBaseVerifyAllCore,
      CorePushSerialize.pushPattern_direct sig short]
  · have nonempty : sig ≠ [] := by
      intro empty
      subst sig
      simp at short
    have invalid : DERSyntax.valid sig = false := by
      cases der : DERSyntax.valid sig with
      | false => rfl
      | true => exact False.elim (short
          (DERSyntax.valid_direct_push_width sig der))
    have gate : DERSyntax.verifyAllEncoding sig = false := by
      cases sig with
      | nil => exact False.elim (nonempty rfl)
      | cons b rest => simp [DERSyntax.verifyAllEncoding] at invalid ⊢
                       exact invalid
    simp [evalBaseVerifyAll, evalBaseVerifyAllCore, gate]

/-- A successful source-shaped CHECKSIGVERIFY evaluation exposes the actual
last-byte sighash type, strict-DER signature, key-validity result, and the
checker call on the deleted scriptCode. No SIGHASH_ALL restriction follows. -/
theorem successful_base_check (fuel : Nat) (script sig key : Bytes)
    (validKey : Bytes → Bool) (verify : VerifyECDSA)
    (success : evalBaseVerifyAll fuel script sig key validKey verify =
      some true) :
    ∃ hashType,
      sig.getLast? = some hashType ∧
      DERSyntax.valid sig = true ∧
      validKey key = true ∧
      verify sig.dropLast key
        (CoreFindAndDelete.run fuel script
          (ScriptCodeSelection.directPushPattern sig)) hashType = true := by
  unfold evalBaseVerifyAll at success
  by_cases encoded : DERSyntax.verifyAllEncoding sig
  · simp only [encoded, ↓reduceIte] at success
    cases last : sig.getLast? with
    | none => simp [last] at success
    | some hashType =>
        simp only [last] at success
        have parts : validKey key = true ∧
            verify sig.dropLast key
              (CoreFindAndDelete.run fuel script
                (ScriptCodeSelection.directPushPattern sig)) hashType = true := by
          simpa only [Option.some.injEq,
            Bool.and_eq_true_eq_eq_true_and_eq_true] using success
        have nonempty : sig ≠ [] := by
          intro empty
          simp [empty] at last
        have der : DERSyntax.valid sig = true := by
          simpa [DERSyntax.verifyAllEncoding_nonempty sig nonempty] using encoded
        exact ⟨hashType, rfl, der, parts.1, parts.2⟩
  · simp [encoded] at success

/-- For either reached SHA256-derived puzzle signature, the source-shaped
checker receives the *unmodified literal lock* and the signature's actual
last byte, which may be any consensus-admitted sighash type. -/
theorem successful_hash_puzzle (hashes : Hashes) (hashKey puzzleKey : Bytes)
    (validKey : Bytes → Bool) (verify : VerifyECDSA)
    (success : evalBaseVerifyAll 880 PinPuzzleScriptCode.literalScript
      (hashes.h256 hashKey) puzzleKey validKey verify = some true) :
    ∃ hashType,
      (hashes.h256 hashKey).getLast? = some hashType ∧
      DERSyntax.valid (hashes.h256 hashKey) = true ∧
      validKey puzzleKey = true ∧
      verify (hashes.h256 hashKey).dropLast puzzleKey
        PinPuzzleScriptCode.literalScript hashType = true := by
  obtain ⟨hashType, last, der, keyValid, checked⟩ :=
    successful_base_check 880 PinPuzzleScriptCode.literalScript
      (hashes.h256 hashKey) puzzleKey validKey verify success
  change verify (hashes.h256 hashKey).dropLast puzzleKey
    (PinPuzzleScriptCode.puzzleScriptCode (hashes.h256 hashKey)) hashType =
      true at checked
  rw [PinPuzzleScriptCode.pin_hash_scriptCode_eq_literal hashes hashKey] at checked
  exact ⟨hashType, last, der, keyValid, checked⟩

/-- In one successful arbitrary-stack byte-model run, if the two reached
pinning pairs pass this source-shaped BASE checker, the fixed pin signature
is checked under ALL against its one-push-deleted scriptCode, while the
SHA256-derived puzzle signature is checked under its *actual* last byte
against the unmodified lock. The pair-success premise still requires Core
interpreter/checker refinement. -/
theorem accepted_pinning_source_checks (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : ByteMachine.State)
    (validKey : Bytes → Bool) (verify : VerifyECDSA)
    (accepted : ByteMachine.run hashes ByteLayout.program
      (ByteMachine.State.mk stack outcomes 0) = some final)
    (matched : ∀ nonceKey puzzleKey raw tail,
      stack = nonceKey :: puzzleKey :: raw :: tail →
      evalBaseVerifyAll 880 PinPuzzleScriptCode.literalScript
        FirstOvershoot.pinSignature nonceKey validKey verify = some true ∧
      evalBaseVerifyAll 880 PinPuzzleScriptCode.literalScript
        (hashes.h256 nonceKey) puzzleKey validKey verify = some true) :
    ∃ nonceKey puzzleKey raw tail later puzzleHashType,
      stack = nonceKey :: puzzleKey :: raw :: tail ∧
      outcomes = true :: true :: later ∧
      validKey nonceKey = true ∧
      verify FirstOvershoot.pinSignature.dropLast nonceKey
        (ScriptCodeSelection.stripEncodedChunks
          [FindAndDelete.pinPattern] EncodedLayout.chunks) 0x01 = true ∧
      (hashes.h256 nonceKey).getLast? = some puzzleHashType ∧
      DERSyntax.valid (hashes.h256 nonceKey) = true ∧
      validKey puzzleKey = true ∧
      verify (hashes.h256 nonceKey).dropLast puzzleKey
        PinPuzzleScriptCode.literalScript puzzleHashType = true := by
  obtain ⟨nonceKey, puzzleKey, raw, tail, later,
    shape, outcomesShape, _prefix, _flag, _code⟩ :=
    PinningScriptCode.accepted_pinning_reached_bytes
      hashes stack outcomes final accepted
  obtain ⟨pinMatched, puzzleMatched⟩ :=
    matched nonceKey puzzleKey raw tail shape
  obtain ⟨pinHashType, pinLast, _pinDER, pinKeyValid, pinVerified⟩ :=
    successful_base_check 880 PinPuzzleScriptCode.literalScript
      FirstOvershoot.pinSignature nonceKey validKey verify pinMatched
  have pinFlag := FindAndDelete.pin_signature_sighash_all
  have pinType : pinHashType = 0x01 :=
    Option.some.inj (pinLast.symm.trans pinFlag)
  subst pinHashType
  change verify FirstOvershoot.pinSignature.dropLast nonceKey
    (CoreFindAndDelete.run 880 PinPuzzleScriptCode.literalScript
      FindAndDelete.pinPattern) 0x01 = true at pinVerified
  unfold PinPuzzleScriptCode.literalScript at pinVerified
  rw [CoreFindAndDelete.pin_scriptCode_run] at pinVerified
  obtain ⟨puzzleHashType, puzzleLast, puzzleDER,
    puzzleKeyValid, puzzleVerified⟩ :=
    successful_hash_puzzle hashes nonceKey puzzleKey validKey verify
      puzzleMatched
  exact ⟨nonceKey, puzzleKey, raw, tail, later, puzzleHashType,
    shape, outcomesShape, pinKeyValid, pinVerified,
    puzzleLast, puzzleDER, puzzleKeyValid, puzzleVerified⟩

/-- The late puzzle's source checker is applied to the actual reached
SHA256-derived signature and the actual reached public-key bytes. That
signature hashes the key later occupying the last final multisignature key
slot. The matched-checker premise is the outstanding Core refinement. -/
theorem accepted_late_source_check (hashes : Hashes)
    (initial final : ByteMachine.State)
    (validKey : Bytes → Bool) (verify : VerifyECDSA)
    (accepted : ByteMachine.run hashes ByteLayout.program initial =
      some final)
    (matched : ∀ finalKey puzzleKey beforeVerify,
      ByteMachine.run hashes (ByteLayout.program.take 856) initial =
        some beforeVerify →
      beforeVerify.stack[0]? = some puzzleKey →
      beforeVerify.stack[1]? = some (hashes.h256 finalKey) →
      evalBaseVerifyAll 880 PinPuzzleScriptCode.literalScript
        (hashes.h256 finalKey) puzzleKey validKey verify = some true) :
    ∃ finalKey puzzleKey beforeVerify beforeCheck hashType,
      ByteMachine.run hashes (ByteLayout.program.take 856) initial =
        some beforeVerify ∧
      beforeVerify.stack[0]? = some puzzleKey ∧
      beforeVerify.stack[1]? = some (hashes.h256 finalKey) ∧
      ByteMachine.run hashes (ByteLayout.program.take 879) initial =
        some beforeCheck ∧
      beforeCheck.stack[10]? = some finalKey ∧
      (hashes.h256 finalKey).getLast? = some hashType ∧
      DERSyntax.valid (hashes.h256 finalKey) = true ∧
      validKey puzzleKey = true ∧
      verify (hashes.h256 finalKey).dropLast puzzleKey
        PinPuzzleScriptCode.literalScript hashType = true := by
  obtain ⟨finalKey, beforeVerify, beforeSuffix, beforeCheck,
    prefixRun, precheckRun, verifyRun, sigAt, keyAt⟩ :=
    ByteLatePuzzle.accepted_whole_program_final_puzzle_key
      hashes initial final accepted
  obtain ⟨puzzleKey, _sig, _tail, verifyShape, _afterShape⟩ :=
    ByteLatePuzzle.accepted_checksigverify_tail hashes
      beforeVerify beforeSuffix verifyRun
  have pubAt : beforeVerify.stack[0]? = some puzzleKey := by
    rw [verifyShape]
    rfl
  have sourceSuccess :=
    matched finalKey puzzleKey beforeVerify prefixRun pubAt sigAt
  obtain ⟨hashType, last, der, keyValid, checked⟩ :=
    successful_hash_puzzle hashes finalKey puzzleKey validKey verify
      sourceSuccess
  exact ⟨finalKey, puzzleKey, beforeVerify, beforeCheck, hashType,
    prefixRun, pubAt, sigAt, precheckRun, keyAt,
    last, der, keyValid, checked⟩

end QSB.CoreChecksigEval
