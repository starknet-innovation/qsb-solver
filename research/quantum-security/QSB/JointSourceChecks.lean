import QSB.CoreSourceExtraction
import QSB.LegacySighashWire

/-!
One pair of byte functions supplies all source-shaped QSB hash roles:
SHA256(x) = H(x), SHA256d(x) = H(H(x)), and HASH160(x) = R(H(x)).
This prevents the source-model statement from silently replacing the shared
H256 uses by independent functions. No probability distribution, quantum
oracle access, or ECDSA implementation is proved here. The external `ecdsa`
function and the source interpreter's signature outcomes still require Core
refinement.
-/
namespace QSB.JointSourceChecks

open ByteMachine

structure Functions where
  H : Bytes → Bytes
  R : Bytes → Bytes
  H_width : ∀ x, (H x).length = 32
  R_width : ∀ x, (R x).length = 20

def hashes (functions : Functions) : Hashes where
  h256 := functions.H
  h160 := fun x => functions.R (functions.H x)
  h256_width := functions.H_width
  h160_width := fun x => functions.R_width (functions.H x)

/-- A missing input index is outside the checker domain. For an in-range
input, a missing preimage means the legacy out-of-range SINGLE exception;
Core returns raw internal `uint256::ONE` bytes rather than hashing a preimage.
The hash-type argument is a low-byte sighash flag in checker uses. -/
def legacyDigest (functions : Functions) (tx : SighashAllWire.TxFields)
    (selected : Nat) (scriptCode : Bytes) (hashType : Nat) : Option Bytes :=
  if selected ≥ tx.inputs.length then none
  else
    match LegacySighashWire.sourcePreimage tx selected scriptCode hashType with
    | some preimage => some (functions.H (functions.H preimage))
    | none => some LegacySighashWire.singleBugDigest

theorem legacyDigest_all (functions : Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (inputValid : selected < tx.inputs.length) :
    legacyDigest functions tx selected scriptCode 1 =
      some (functions.H (functions.H
        (SighashAllWire.sourceAllPreimage tx selected scriptCode))) := by
  simp [legacyDigest, Nat.not_le.mpr inputValid,
    LegacySighashWire.all_preimage tx selected scriptCode inputValid]

theorem legacyDigest_single_bug (functions : Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat)
    (inputValid : selected < tx.inputs.length)
    (single : LegacySighashWire.baseType hashType = 3)
    (outputMissing : tx.outputs.length ≤ selected) :
    legacyDigest functions tx selected scriptCode hashType =
      some LegacySighashWire.singleBugDigest := by
  simp [legacyDigest, Nat.not_le.mpr inputValid,
    LegacySighashWire.single_out_of_range tx selected scriptCode
      hashType inputValid single outputMissing]

/-- The ECDSA predicate is supplied externally. CoreChecksigEval separately
checks key validity and DER encoding before calling this function. -/
def checker (functions : Functions) (tx : SighashAllWire.TxFields)
    (selected : Nat) (ecdsa : Bytes → Bytes → Bytes → Bool) :
    CoreChecksigEval.VerifyECDSA :=
  fun sig key scriptCode hashType =>
    match legacyDigest functions tx selected scriptCode hashType.toNat with
    | some digest => ecdsa sig key digest
    | none => false

theorem checker_all (functions : Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (sig key scriptCode : Bytes)
    (inputValid : selected < tx.inputs.length) :
    checker functions tx selected ecdsa sig key scriptCode 0x01 =
      ecdsa sig key (functions.H (functions.H
        (SighashAllWire.sourceAllPreimage tx selected scriptCode))) := by
  simp [checker, legacyDigest_all functions tx selected scriptCode inputValid]

theorem checker_single_bug (functions : Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (sig key scriptCode : Bytes) (hashType : UInt8)
    (inputValid : selected < tx.inputs.length)
    (single : LegacySighashWire.baseType hashType.toNat = 3)
    (outputMissing : tx.outputs.length ≤ selected) :
    checker functions tx selected ecdsa sig key scriptCode hashType =
      ecdsa sig key LegacySighashWire.singleBugDigest := by
  simp [checker, legacyDigest_single_bug functions tx selected scriptCode
    hashType.toNat inputValid single outputMissing]

/-- Either reached SHA256-derived CHECKSIGVERIFY puzzle is bound to its
actual last-byte hash type and the digest produced by the same H used in its
DER-shaped signature. This does not assume that digest is a SHA256d preimage
hash: SINGLE may instead select the constant-message exception. -/
theorem successful_hash_puzzle_joint (functions : Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (hashKey puzzleKey : Bytes)
    (success : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript
      (functions.H hashKey) puzzleKey validKey
      (checker functions tx selected ecdsa) = some true) :
    ∃ hashType digest,
      (functions.H hashKey).getLast? = some hashType ∧
      DERSyntax.valid (functions.H hashKey) = true ∧
      validKey puzzleKey = true ∧
      legacyDigest functions tx selected
        PinPuzzleScriptCode.literalScript hashType.toNat = some digest ∧
      ecdsa (functions.H hashKey).dropLast puzzleKey digest = true := by
  obtain ⟨hashType, last, der, keyValid, checked⟩ :=
    CoreChecksigEval.successful_hash_puzzle (hashes functions)
      hashKey puzzleKey validKey (checker functions tx selected ecdsa) success
  unfold checker at checked
  cases digestEq : legacyDigest functions tx selected
      PinPuzzleScriptCode.literalScript hashType.toNat with
  | none => simp [digestEq] at checked
  | some digest =>
      simp only [digestEq] at checked
      exact ⟨hashType, digest, last, der, keyValid, digestEq, checked⟩

/-- The reached pin and final nonce checks share the same H, including its
inner and outer SHA256d calls. The seven opening equations in the conclusion
use R(H(opening)) against the literal lock commitments. The accepted run and
necessary checker successes are source-model premises, not Core acceptance. -/
theorem necessary_checks_fixed_all_joint (functions : Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (stack : List Bytes) (outcomes : List Bool)
    (sourceFinal : CoreOpcodeStep.State)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (inputValid : selected < tx.inputs.length)
    (sourceRun : CoreStructuralRun.run (hashes functions) ByteLayout.program
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) = some sourceFinal)
    (truth : ByteMachine.finalTruth
      ⟨sourceFinal.stack.reverse, sourceFinal.outcomes,
        sourceFinal.ops⟩ = true)
    (checks : CoreSourceExtraction.necessarySignatureChecks
      (hashes functions) (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩)
      validKey (checker functions tx selected ecdsa) = true) :
    ∃ (pinKey : Bytes) (w : RoundWitness (Fin 150) Bytes Bytes)
      (beforeCheck : CoreOpcodeStep.State),
      FinalRoundShape w ∧
      OpeningsValid (fun x => functions.R (functions.H x))
        FinalSignedLoop.generatedCommitmentAt w.signed w.opening ∧
      FinalRoundWitness.extractMatchedWitness (hashes functions)
        ⟨stack, outcomes, 0⟩ = some w ∧
      DERSyntax.valid (functions.H pinKey) = true ∧
      DERSyntax.valid (functions.H w.key) = true ∧
      validKey pinKey = true ∧
      ecdsa FirstOvershoot.pinSignature.dropLast pinKey
        (functions.H (functions.H (SighashAllWire.sourceAllPreimage tx selected
          (ScriptCodeSelection.stripEncodedChunks
            [FindAndDelete.pinPattern] EncodedLayout.chunks)))) = true ∧
      validKey w.key = true ∧
      ecdsa PoolRollInvariant.finalNonce.dropLast w.key
        (functions.H (functions.H (SighashAllWire.sourceAllPreimage tx selected
          (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
            beforeCheck.stack.reverse)))) = true := by
  obtain ⟨pinKey, w, beforeCheck, shape, openings, computedWitness,
    pinDER, finalDER, pinValid, pinChecked, finalValid, finalChecked⟩ :=
    CoreSourceExtraction.necessary_checks_fixed_all_calls
      (hashes functions) stack outcomes sourceFinal validKey
      (checker functions tx selected ecdsa) sourceRun truth checks
  rw [checker_all functions tx selected ecdsa _ _ _ inputValid] at pinChecked
  rw [checker_all functions tx selected ecdsa _ _ _ inputValid] at finalChecked
  exact ⟨pinKey, w, beforeCheck, shape, openings, computedWitness,
    pinDER, finalDER, pinValid, pinChecked, finalValid, finalChecked⟩

end QSB.JointSourceChecks
