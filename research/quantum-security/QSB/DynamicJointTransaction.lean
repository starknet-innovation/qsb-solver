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

/-- Complete transaction-layout split for the first nine reached final
signature calls on a good setup. Every one is a generated SINGLE dummy; an
in-range selected output gives `H(H(single preimage))`, while an out-of-range
selection gives Core's raw constant digest. Both branches use the same
reached final FindAndDelete scriptCode. This is a source-certificate theorem,
not a compiled-Core acceptance implication. -/
theorem search_good_setup_nine_single_cases
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
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false) :
    ∃ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      ∀ j : Fin 9, ∃ (id : Fin 150) (key : Bytes),
        CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val =
          some (FinalSignedLoop.generatedDummyAt id) ∧
        CoreMultisigStack.keyAt beforeCheck.stack j.val = some key ∧
        CoreDEREncoding.valid (FinalSignedLoop.generatedDummyAt id) = true ∧
        validKey key = true ∧
        selected < tx.inputs.length ∧
        ((selected < tx.outputs.length ∧
          ∃ preimage,
            LegacySighashWire.sourcePreimage tx selected
              (CoreMultisigSourceScan.deletedScript
                (DynamicCheckedCertificate.wire lock)
                beforeCheck.stack.reverse 10 10) 3 = some preimage ∧
            ecdsa (FinalSignedLoop.generatedDummyAt id).dropLast key
              (functions.H (functions.H preimage)) = true) ∨
         (tx.outputs.length ≤ selected ∧
          ecdsa (FinalSignedLoop.generatedDummyAt id).dropLast key
            LegacySighashWire.singleBugDigest = true)) := by
  obtain ⟨beforeSlots, slotsReached, slots⟩ :=
    DynamicCheckedCertificate.search_good_setup_nine_dummy_signatures
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found secondWidth noCommitmentDER
  obtain ⟨beforeCalls, callsReached, calls⟩ :=
    search_reached_final_joint_calls functions tx selected lock stack
      validKey ecdsa firstRound final found
  have same : beforeCalls = beforeSlots :=
    Option.some.inj (callsReached.symm.trans slotsReached)
  subst beforeCalls
  refine ⟨beforeSlots, slotsReached, ?_⟩
  intro j
  obtain ⟨id, slot⟩ := slots j
  obtain ⟨sig, key, hashType, digest, sigAt, keyAt, der, last,
    keyValid, digestEq, verified, inputValid, digestCases⟩ :=
    calls ⟨j.val, by omega⟩
  have sigEq : sig = FinalSignedLoop.generatedDummyAt id :=
    Option.some.inj (sigAt.symm.trans slot)
  subst sig
  have flag : hashType = 0x03 :=
    Option.some.inj (last.symm.trans
      (ScriptCodeSelection.generatedDummyAt_sighash_single id))
  subst hashType
  refine ⟨id, key, slot, keyAt, der, keyValid, inputValid, ?_⟩
  by_cases inRange : selected < tx.outputs.length
  · rcases digestCases with ⟨preimage, preimageEq, digestValue⟩ |
        ⟨_missing, _single, outputMissing, _constant⟩
    · refine Or.inl ⟨inRange, preimage, by simpa using preimageEq, ?_⟩
      simpa [← digestValue] using verified
    · omega
  · have outputMissing : tx.outputs.length ≤ selected :=
      Nat.le_of_not_gt inRange
    have digestEq' : JointSourceChecks.legacyDigest functions tx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          beforeSlots.stack.reverse 10 10) 3 = some digest := by
      simpa using digestEq
    rw [JointSourceChecks.legacyDigest_single_bug functions tx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicCheckedCertificate.wire lock)
        beforeSlots.stack.reverse 10 10) 3 inputValid (by decide)
      outputMissing] at digestEq'
    have sameDigest : LegacySighashWire.singleBugDigest = digest :=
      Option.some.inj digestEq'
    exact Or.inr ⟨outputMissing, by simpa [sameDigest] using verified⟩

/-- The nine generated dummy signatures are checked against one common
transaction digest, not nine independently sampled messages. This holds for
both in-range SINGLE and the out-of-range bug branch because the reached
scriptCode, selected input, and `0x03` flag are shared by all nine calls. -/
theorem search_good_setup_nine_common_single_digest
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
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false) :
    ∃ (beforeCheck : CoreOpcodeStep.State) (digest : Bytes),
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      JointSourceChecks.legacyDigest functions tx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          beforeCheck.stack.reverse 10 10) 3 = some digest ∧
      ∀ j : Fin 9, ∃ (id : Fin 150) (key : Bytes),
        CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val =
          some (FinalSignedLoop.generatedDummyAt id) ∧
        CoreMultisigStack.keyAt beforeCheck.stack j.val = some key ∧
        CoreDEREncoding.valid (FinalSignedLoop.generatedDummyAt id) = true ∧
        validKey key = true ∧
        ecdsa (FinalSignedLoop.generatedDummyAt id).dropLast key
          digest = true := by
  obtain ⟨beforeCheck, reached, cases⟩ :=
    search_good_setup_nine_single_cases functions tx selected lock stack
      validKey ecdsa firstRound final found secondWidth noCommitmentDER
  obtain ⟨_id0, _key0, _slot0, _keyAt0, _der0, _keyValid0,
    inputValid, _verdict0⟩ := cases ⟨0, by omega⟩
  let code := CoreMultisigSourceScan.deletedScript
    (DynamicCheckedCertificate.wire lock) beforeCheck.stack.reverse 10 10
  obtain ⟨digest, digestEq⟩ :
      ∃ digest, JointSourceChecks.legacyDigest functions tx selected code 3 =
        some digest := by
    unfold JointSourceChecks.legacyDigest
    simp only [show ¬selected ≥ tx.inputs.length from
      Nat.not_le.mpr inputValid, ↓reduceIte]
    cases preimageEq : LegacySighashWire.sourcePreimage tx selected code 3 with
    | none => exact ⟨LegacySighashWire.singleBugDigest, by simp⟩
    | some preimage =>
        exact ⟨functions.H (functions.H preimage), by simp⟩
  refine ⟨beforeCheck, digest, reached, digestEq, ?_⟩
  intro j
  obtain ⟨id, key, slot, keyAt, der, keyValid, _inputValid,
    verdict⟩ := cases j
  refine ⟨id, key, slot, keyAt, der, keyValid, ?_⟩
  rcases verdict with ⟨_inRange, preimage, preimageEq, verified⟩ |
      ⟨outputMissing, verified⟩
  · have callDigest : JointSourceChecks.legacyDigest functions tx selected
        code 3 = some (functions.H (functions.H preimage)) := by
      have preimageAtCode :
          LegacySighashWire.sourcePreimage tx selected code 3 =
            some preimage := by simpa [code] using preimageEq
      simp [JointSourceChecks.legacyDigest,
        Nat.not_le.mpr inputValid, preimageAtCode]
    have same : digest = functions.H (functions.H preimage) :=
      Option.some.inj (digestEq.symm.trans callDigest)
    simpa [same] using verified
  · have callDigest := JointSourceChecks.legacyDigest_single_bug
      functions tx selected code 3 inputValid (by decide) outputMissing
    have same : digest = LegacySighashWire.singleBugDigest :=
      Option.some.inj (digestEq.symm.trans callDigest)
    simpa [same] using verified

/-- Under the explicit no-DER-commitment setup condition, the first nine
reached final multisignature pairs use generated `SIGHASH_SINGLE` dummy
signatures. If the selected input is beyond the final output, all nine
ECDSA calls receive Core's raw constant SINGLE-bug digest, independently of
the shared final FindAndDelete scriptCode. The tenth fixed nonce pair remains
separate and may bind the transaction through `SIGHASH_ALL`. -/
theorem search_good_setup_nine_single_bug_calls
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
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false)
    (outputMissing : tx.outputs.length ≤ selected) :
    ∃ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      ∀ j : Fin 9, ∃ (id : Fin 150) (key : Bytes),
        CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val =
          some (FinalSignedLoop.generatedDummyAt id) ∧
        CoreMultisigStack.keyAt beforeCheck.stack j.val = some key ∧
        CoreDEREncoding.valid (FinalSignedLoop.generatedDummyAt id) = true ∧
        validKey key = true ∧
        selected < tx.inputs.length ∧
        ecdsa (FinalSignedLoop.generatedDummyAt id).dropLast key
          LegacySighashWire.singleBugDigest = true := by
  obtain ⟨beforeCheck, reached, cases⟩ :=
    search_good_setup_nine_single_cases functions tx selected lock stack
      validKey ecdsa firstRound final found secondWidth noCommitmentDER
  refine ⟨beforeCheck, reached, ?_⟩
  intro j
  obtain ⟨id, key, slot, keyAt, der, keyValid, inputValid,
    verdict⟩ := cases j
  rcases verdict with ⟨inRange, _⟩ | ⟨_, verified⟩
  · omega
  · exact ⟨id, key, slot, keyAt, der, keyValid, inputValid,
      verified⟩

/-- In the complementary layout, each reached dummy checks SHA256d of an
in-range SINGLE preimage against the same deleted scriptCode. That preimage
contains the selected output, while the fixed nonce's ALL call remains the
separate whole-transaction binding. -/
theorem search_good_setup_nine_single_in_range_calls
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
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false)
    (outputInRange : selected < tx.outputs.length) :
    ∃ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      ∀ j : Fin 9, ∃ (id : Fin 150) (key preimage : Bytes),
        CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val =
          some (FinalSignedLoop.generatedDummyAt id) ∧
        CoreMultisigStack.keyAt beforeCheck.stack j.val = some key ∧
        CoreDEREncoding.valid (FinalSignedLoop.generatedDummyAt id) = true ∧
        validKey key = true ∧
        selected < tx.inputs.length ∧
        LegacySighashWire.sourcePreimage tx selected
          (CoreMultisigSourceScan.deletedScript
            (DynamicCheckedCertificate.wire lock)
            beforeCheck.stack.reverse 10 10) 3 = some preimage ∧
        ecdsa (FinalSignedLoop.generatedDummyAt id).dropLast key
          (functions.H (functions.H preimage)) = true := by
  obtain ⟨beforeCheck, reached, cases⟩ :=
    search_good_setup_nine_single_cases functions tx selected lock stack
      validKey ecdsa firstRound final found secondWidth noCommitmentDER
  refine ⟨beforeCheck, reached, ?_⟩
  intro j
  obtain ⟨id, key, slot, keyAt, der, keyValid, inputValid,
    verdict⟩ := cases j
  rcases verdict with ⟨_, preimage, preimageEq, verified⟩ |
      ⟨outputMissing, _⟩
  · exact ⟨id, key, preimage, slot, keyAt, der, keyValid,
      inputValid, preimageEq, verified⟩
  · omega

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

/-- Deterministic joint final puzzle event from one parameterized source
certificate. The same `H` produces a DER-shaped signature from the final
nonce key and hashes the ALL preimage twice for that key's fixed-signature
ECDSA call. No independence, quantum query bound, or Core refinement is
asserted. -/
theorem search_final_nonce_joint_hit
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
    ∃ (beforeLate beforeCheck : CoreOpcodeStep.State) (key : Bytes),
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 856)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeLate ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      beforeLate.stack.reverse[1]? = some (functions.H key) ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some key ∧
      DERSyntax.valid (functions.H key) = true ∧
      selected < tx.inputs.length ∧
      ecdsa lock.nonce1.dropLast key
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨key, beforeLate, beforeFromPuzzle, lateReached,
    puzzleReached, puzzleSig, puzzleKey, derHit⟩ :=
    DynamicCheckedCertificate.search_late_puzzle_final_key_der
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found
  obtain ⟨beforeFromNonce, nonceKey, nonceReached, nonceSlot,
    nonceKeyAt, _nonceDer, _keyValid, inputValid, verified⟩ :=
    search_fixed_final_nonce_all_call functions tx selected lock
      secondWidth stack validKey ecdsa firstRound final found nonceAll
  have sameBefore : beforeFromPuzzle = beforeFromNonce :=
    Option.some.inj (puzzleReached.symm.trans nonceReached)
  subst beforeFromPuzzle
  have sameKey : key = nonceKey :=
    Option.some.inj (puzzleKey.symm.trans nonceKeyAt)
  subst nonceKey
  exact ⟨beforeLate, beforeFromNonce, key, lateReached, nonceReached,
    puzzleSig, nonceSlot, nonceKeyAt, derHit, inputValid, verified⟩

/-- Both correlated hash-to-DER puzzles and both fixed-signature ALL calls
come from the same checked source certificate. The keys may be equal; this
statement makes no independence or quantum success claim. -/
theorem search_two_key_joint_hit
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
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    ∃ (pinKey finalKey : Bytes)
      (beforePin beforeCheck : CoreOpcodeStep.State),
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 2)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforePin ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      reachedPinSignature beforePin = lock.pin ∧
      reachedPinKey beforePin = pinKey ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some finalKey ∧
      DERSyntax.valid (functions.H pinKey) = true ∧
      DERSyntax.valid (functions.H finalKey) = true ∧
      selected < tx.inputs.length ∧
      ecdsa lock.pin.dropLast pinKey
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (reachedPinScriptCode lock beforePin)))) = true ∧
      ecdsa lock.nonce1.dropLast finalKey
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨pinKey, beforeFromPuzzle, _beforeEarly,
    puzzleReached, _earlyReached, pinKeyAt, _puzzleSig, pinDER⟩ :=
    DynamicCheckedCertificate.search_early_puzzle_pin_key_der
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found
  obtain ⟨beforeFromPin, pinReached, fixedPin, _pinDer,
    _pinValid, pinVerified⟩ :=
    search_fixed_pin_all_call functions tx selected lock stack
      validKey ecdsa firstRound final found pinAll
  have samePin : beforeFromPuzzle = beforeFromPin :=
    Option.some.inj (puzzleReached.symm.trans pinReached)
  subst beforeFromPuzzle
  have reachedKey : reachedPinKey beforeFromPin = pinKey := by
    simpa [reachedPinKey] using
      congrArg (fun value : Option Bytes => value.getD []) pinKeyAt
  obtain ⟨_beforeLate, beforeCheck, finalKey, _lateReached,
    checkReached, _puzzleSig, nonceSlot, finalKeyAt, finalDER,
    inputValid, finalVerified⟩ :=
    search_final_nonce_joint_hit functions tx selected lock secondWidth
      stack validKey ecdsa firstRound final found nonceAll
  rw [reachedKey] at pinVerified
  exact ⟨pinKey, finalKey, beforeFromPin, beforeCheck, pinReached,
    checkReached, fixedPin, reachedKey, nonceSlot, finalKeyAt,
    pinDER, finalDER, inputValid, pinVerified, finalVerified⟩

/-- On a good setup, the same checked source certificate supplies all seven
`R(H(opening))` equations and the correlated final `H(key)`/`H(H(ALL))`
puzzle. The trace is read from the actual modeled witness. This is the
deterministic event a later shared-query quantum analysis must bound; it is
not itself a probability estimate or a Core acceptance implication. -/
theorem search_good_setup_joint_final_event
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final))
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false)
    (nonceAll : lock.nonce1.getLast? = some 0x01) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : CoreOpcodeStep.State) (key : Bytes),
      DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions)
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment)
        ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace,
        functions.R (functions.H p.2) = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      DERSyntax.valid (functions.H key) = true ∧
      selected < tx.inputs.length ∧
      ecdsa lock.nonce1.dropLast key
        (functions.H (functions.H
          (SighashAllWire.sourceAllPreimage tx selected
            (CoreMultisigSourceScan.deletedScript
              (DynamicCheckedCertificate.wire lock)
              beforeCheck.stack.reverse 10 10)))) = true := by
  obtain ⟨trace, a, b, extracted, seven, hits, distinct, count⟩ :=
    DynamicCheckedCertificate.search_good_setup_nine_positions
      (JointSourceChecks.hashes functions) lock firstWidth secondWidth
      pinShort nonce0Short nonce1Short stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found noCommitmentDER
  obtain ⟨_beforeLate, beforeCheck, key, _lateReached,
    checkReached, _puzzleSig, _nonceSlot, _keyAt, derHit,
    inputValid, verified⟩ :=
    search_final_nonce_joint_hit functions tx selected lock secondWidth
      stack validKey ecdsa firstRound final found nonceAll
  exact ⟨trace, a, b, beforeCheck, key, extracted, seven,
    by simpa [JointSourceChecks.hashes] using hits, distinct, count,
    checkReached, derHit, inputValid, verified⟩

end QSB.DynamicJointTransaction
