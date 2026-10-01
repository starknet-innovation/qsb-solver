import QSB.DynamicCheckedCertificate
import QSB.JointSourceChecks

/-!
Transaction-dependent final signature calls from the checked parameterized
source certificate. The same H supplies SHA256, SHA256d, and the inner hash of
HASH160. Successful final CHECKMULTISIG checks ten reached DER signatures
against one Core-shaped scriptCode after all ten reached pushes are deleted.
Each digest is selected by the signature's actual final hash-type byte; the
statement does not assume all ten signatures use SIGHASH_ALL.

The ECDSA predicate and key-validity function remain external. The theorem
does not infer this certificate from compiled Bitcoin Core acceptance or
establish a quantum-query bound.
-/
namespace QSB.DynamicJointTransaction

open ByteMachine

def reachedPinSignature (beforePin : CoreOpcodeStep.State) : Bytes :=
  beforePin.stack.reverse[1]?.getD []

def reachedPinKey (beforePin : CoreOpcodeStep.State) : Bytes :=
  beforePin.stack.reverse[0]?.getD []

def reachedPinScriptCode (lock : DynamicCheckedCertificate.Lock)
    (beforePin : CoreOpcodeStep.State) : Bytes :=
  CoreFindAndDelete.run 880 (DynamicCheckedCertificate.wire lock)
    (CorePushSerialize.pushPattern (reachedPinSignature beforePin))

/-- The same checked certificate forces a reached pinning signature call at
the selected transaction input. Its signature, key, and scriptCode come from
the actual pre-CHECKSIGVERIFY stack. Strict DER makes the source-model direct
push deletion equal Core's full push serialization. -/
theorem search_reached_pin_joint_call
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final)) :
    ∃ beforePin : CoreOpcodeStep.State,
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 2)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforePin ∧
      ∃ hashType digest,
        (reachedPinSignature beforePin).getLast? = some hashType ∧
        DERSyntax.valid (reachedPinSignature beforePin) = true ∧
        validKey (reachedPinKey beforePin) = true ∧
        JointSourceChecks.legacyDigest functions tx selected
          (reachedPinScriptCode lock beforePin) hashType.toNat =
            some digest ∧
        ecdsa (reachedPinSignature beforePin).dropLast
          (reachedPinKey beforePin) digest = true ∧
        selected < tx.inputs.length ∧
        ((∃ preimage,
            LegacySighashWire.sourcePreimage tx selected
              (reachedPinScriptCode lock beforePin) hashType.toNat =
                some preimage ∧
            digest = functions.H (functions.H preimage)) ∨
          (LegacySighashWire.sourcePreimage tx selected
              (reachedPinScriptCode lock beforePin) hashType.toNat = none ∧
            LegacySighashWire.baseType hashType.toNat = 3 ∧
            tx.outputs.length ≤ selected ∧
            digest = LegacySighashWire.singleBugDigest)) := by
  have sites :=
    (DynamicCheckedCertificate.search_sound
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found).2.2.1
  obtain ⟨beforePin, reached, checked⟩ :=
    DynamicCheckedCertificate.source_sites_pin
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound sites
  let sig := reachedPinSignature beforePin
  let key := reachedPinKey beforePin
  obtain ⟨hashType, last, der, keyValid, verified⟩ :=
    CoreChecksigEval.successful_base_check 880
      (DynamicCheckedCertificate.wire lock) sig key validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      (by simpa [sig, key, reachedPinSignature, reachedPinKey] using checked)
  have short := DERSyntax.valid_direct_push_width sig der
  have codeEq : reachedPinScriptCode lock beforePin =
      CoreFindAndDelete.run 880 (DynamicCheckedCertificate.wire lock)
        (ScriptCodeSelection.directPushPattern sig) := by
    simp [reachedPinScriptCode, sig,
      CorePushSerialize.pushPattern_direct sig short]
  unfold JointSourceChecks.checker at verified
  cases digestEq : JointSourceChecks.legacyDigest functions tx selected
      (CoreFindAndDelete.run 880 (DynamicCheckedCertificate.wire lock)
        (ScriptCodeSelection.directPushPattern sig)) hashType.toNat with
  | none => simp [digestEq] at verified
  | some digest =>
      simp only [digestEq] at verified
      rw [← codeEq] at digestEq
      have cases := JointSourceChecks.legacyDigest_some_cases
        functions tx selected (reachedPinScriptCode lock beforePin)
        hashType.toNat digest digestEq
      exact ⟨beforePin, reached, hashType, digest, last, der,
        keyValid, digestEq, verified, cases.1, cases.2⟩

/-- If the parameterized fixed pin signature ends in the builder's ALL flag,
the returned source certificate checks that exact lock-pushed signature under
SHA256d of the selected transaction's ALL preimage and its reached pin
scriptCode. The public key is still drawn from the arbitrary scriptSig stack;
its parsing and ECDSA result are external to this theorem. -/
theorem search_fixed_pin_all_call
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final))
    (pinAll : lock.pin.getLast? = some 0x01) :
    ∃ beforePin : CoreOpcodeStep.State,
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 2)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforePin ∧
      reachedPinSignature beforePin = lock.pin ∧
      DERSyntax.valid lock.pin = true ∧
      validKey (reachedPinKey beforePin) = true ∧
      ecdsa lock.pin.dropLast (reachedPinKey beforePin)
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (reachedPinScriptCode lock beforePin)))) = true := by
  obtain ⟨beforePin, reached, hashType, digest, last, der,
    keyValid, digestEq, verified, inputValid, _digestCases⟩ :=
    search_reached_pin_joint_call functions tx selected lock stack
      validKey ecdsa firstRound final found
  have fixed : reachedPinSignature beforePin = lock.pin := by
    have slot := DynamicCheckedCertificate.reached_pin_fixed_signature
      (JointSourceChecks.hashes functions) lock stack firstRound
      beforePin reached
    simpa [reachedPinSignature] using
      congrArg (fun value : Option Bytes => value.getD []) slot
  rw [fixed] at last verified
  have flag : hashType = 0x01 := Option.some.inj (last.symm.trans pinAll)
  subst hashType
  have allDigest := JointSourceChecks.legacyDigest_all functions tx selected
    (reachedPinScriptCode lock beforePin) inputValid
  have digestEq' : JointSourceChecks.legacyDigest functions tx selected
      (reachedPinScriptCode lock beforePin) 1 = some digest := by
    simpa using digestEq
  rw [allDigest] at digestEq'
  have sameDigest := Option.some.inj digestEq'
  rw [← sameDigest] at verified
  exact ⟨beforePin, reached, fixed, by simpa [fixed] using der,
    keyValid, verified⟩

theorem search_reached_final_joint_calls
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final)) :
    ∃ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      (∀ j : Fin 10, ∃ sig key hashType digest,
        CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val = some sig ∧
        CoreMultisigStack.keyAt beforeCheck.stack j.val = some key ∧
        CoreDEREncoding.valid sig = true ∧
        sig.getLast? = some hashType ∧
        validKey key = true ∧
        JointSourceChecks.legacyDigest functions tx selected
          (CoreMultisigSourceScan.deletedScript
            (DynamicCheckedCertificate.wire lock)
            beforeCheck.stack.reverse 10 10)
          hashType.toNat = some digest ∧
        ecdsa sig.dropLast key digest = true ∧
        selected < tx.inputs.length ∧
        ((∃ preimage,
            LegacySighashWire.sourcePreimage tx selected
              (CoreMultisigSourceScan.deletedScript
                (DynamicCheckedCertificate.wire lock)
                beforeCheck.stack.reverse 10 10)
              hashType.toNat = some preimage ∧
            digest = functions.H (functions.H preimage)) ∨
          (LegacySighashWire.sourcePreimage tx selected
              (CoreMultisigSourceScan.deletedScript
                (DynamicCheckedCertificate.wire lock)
                beforeCheck.stack.reverse 10 10)
              hashType.toNat = none ∧
            LegacySighashWire.baseType hashType.toNat = 3 ∧
            tx.outputs.length ≤ selected ∧
            digest = LegacySighashWire.singleBugDigest))) := by
  have checked :=
    (DynamicCheckedCertificate.search_sound
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found).2.2.2
  obtain ⟨beforeCheck, reached, finalEval⟩ :=
    DynamicCheckedCertificate.final_checked_sound
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound checked
  refine ⟨beforeCheck, reached, ?_⟩
  let sourceChecker :=
    CoreFinalChecksigEval.checker validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
  have short : ∀ sig ∈ CoreMultisigSourceScan.reachedSignatures
      beforeCheck.stack.reverse 10 10, sig.length < 76 := by
    simpa [CoreMultisigSourceScan.reachedSignatures,
      FinalScriptCode.reachedSignatures] using
      CoreMultisigEval.finalTenEval_success_all_short
        (DynamicCheckedCertificate.wire lock) sourceChecker
        beforeCheck.stack.reverse finalEval
  have codeEq := CoreMultisigSourceScan.deletedScript_ten
    (DynamicCheckedCertificate.wire lock) beforeCheck.stack.reverse short
  intro j
  obtain ⟨sig, key, sigAt, keyAt, der, checkedPair⟩ :=
    CoreMultisigEval.finalTenEval_success_pairs
      (DynamicCheckedCertificate.wire lock) sourceChecker
      beforeCheck.stack.reverse finalEval j
  obtain ⟨hashType, last, keyValid, verified⟩ :=
    CoreFinalChecksigEval.checker_success validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      sig key
      (CoreMultisigEval.deletedScript
        (DynamicCheckedCertificate.wire lock) beforeCheck.stack.reverse)
      checkedPair
  unfold JointSourceChecks.checker at verified
  cases digestEq : JointSourceChecks.legacyDigest functions tx selected
      (CoreMultisigEval.deletedScript
        (DynamicCheckedCertificate.wire lock) beforeCheck.stack.reverse)
      hashType.toNat with
  | none => simp [digestEq] at verified
  | some digest =>
      simp only [digestEq] at verified
      rw [← codeEq] at digestEq
      have digestCases := JointSourceChecks.legacyDigest_some_cases
        functions tx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          beforeCheck.stack.reverse 10 10)
        hashType.toNat digest digestEq
      exact ⟨sig, key, hashType, digest, by simpa using sigAt,
        by simpa using keyAt, der, last, keyValid, digestEq, verified,
        digestCases.1, digestCases.2⟩

/-- The tenth reached final CHECKMULTISIG pair checks the lock-pushed nonce
under the selected transaction's exact ALL preimage whenever that nonce ends
in the builder's `0x01` flag. The key and ECDSA verdict still come from the
external checker, and the source certificate is not compiled-Core acceptance.
-/
theorem search_fixed_final_nonce_all_call
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final))
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    ∃ (beforeCheck : CoreOpcodeStep.State) (key : Bytes),
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some key ∧
      CoreDEREncoding.valid lock.nonce1 = true ∧
      validKey key = true ∧
      selected < tx.inputs.length ∧
      ecdsa lock.nonce1.dropLast key
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨beforeCheck, reached, pairs⟩ :=
    search_reached_final_joint_calls functions tx selected lock stack
      validKey ecdsa firstRound final found
  obtain ⟨beforeFixed, fixedReached, fixedSlot⟩ :=
    DynamicCheckedCertificate.search_final_fixed_nonce_slot
      (JointSourceChecks.hashes functions) lock secondWidth stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found
  have same : beforeFixed = beforeCheck :=
    Option.some.inj (fixedReached.symm.trans reached)
  subst beforeFixed
  obtain ⟨sig, key, hashType, digest, sigAt, keyAt, der, last,
    keyValid, digestEq, verified, inputValid, _digestCases⟩ :=
    pairs ⟨9, by omega⟩
  have sigEq : sig = lock.nonce1 :=
    Option.some.inj (sigAt.symm.trans fixedSlot)
  subst sig
  have flag : hashType = 0x01 :=
    Option.some.inj (last.symm.trans nonceAll)
  subst hashType
  have digestEq' : JointSourceChecks.legacyDigest functions tx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicCheckedCertificate.wire lock)
        beforeCheck.stack.reverse 10 10) 1 = some digest := by
    simpa using digestEq
  rw [JointSourceChecks.legacyDigest_all functions tx selected
    (CoreMultisigSourceScan.deletedScript
      (DynamicCheckedCertificate.wire lock)
      beforeCheck.stack.reverse 10 10) inputValid] at digestEq'
  have sameDigest := Option.some.inj digestEq'
  rw [← sameDigest] at verified
  exact ⟨beforeCheck, key, reached, fixedSlot, keyAt, der,
    keyValid, inputValid, verified⟩

end QSB.DynamicJointTransaction
