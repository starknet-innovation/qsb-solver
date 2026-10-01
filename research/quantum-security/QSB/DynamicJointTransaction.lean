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

end QSB.DynamicJointTransaction
