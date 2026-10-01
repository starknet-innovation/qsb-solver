import QSB.CoreChecksigEval
import QSB.CoreMultisigEval

/-!
The final ten-pair BASE CHECKMULTISIG source model uses one scriptCode after
sequential deletion of all reached signature pushes. Each successful pair
passes the last byte of its signature to the external ECDSA/sighash checker.
The source evaluator's success is an explicit premise, not an assertion of
compiled Core equivalence or actual transaction acceptance.
-/
namespace QSB.CoreFinalChecksigEval
open ByteMachine

/-- Source-shaped successful-pair portion of Core's ECDSA checker. The
signature's final byte is its actual sighash type; key parsing and exact
`SignatureHash`/ECDSA behavior remain external. -/
def checker (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (sig key scriptCode : Bytes) : Bool :=
  match sig.getLast? with
  | none => false
  | some hashType =>
      validKey key && verify sig.dropLast key scriptCode hashType

theorem checker_success (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (sig key scriptCode : Bytes)
    (success : checker validKey verify sig key scriptCode = true) :
    ∃ hashType, sig.getLast? = some hashType ∧
      validKey key = true ∧
      verify sig.dropLast key scriptCode hashType = true := by
  unfold checker at success
  cases last : sig.getLast? with
  | none => simp [last] at success
  | some hashType =>
      simp only [last] at success
      have parts : validKey key = true ∧
          verify sig.dropLast key scriptCode hashType = true := by
        simpa only [Bool.and_eq_true_eq_eq_true_and_eq_true] using success
      exact ⟨hashType, rfl, parts.1, parts.2⟩

/-- The reached final ten-pair source evaluation exposes every actual
source-addressed ECDSA/sighash checker call, with one selected scriptCode.
The first nine signature hash-type bytes are independently proved to be
`SIGHASH_SINGLE` and the fixed tenth one `SIGHASH_ALL` in
`FinalScriptCode.reached_signature_flags`. -/
theorem successful_byte_run_typed_final_pairs (hashes : Hashes)
    (initial final : State)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (accepted : run hashes ByteLayout.program initial = some final)
    (source : ∃ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      CoreMultisigEval.finalTenEval EncodedLayout.chunks.flatten
        (checker validKey verify) beforeCheck.stack = some true) :
    ∃ (beforeCheck : State) (trace : List (Fin 150 × Bytes))
      (a b : Fin 150),
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      trace.length = 7 ∧
      (∀ p ∈ trace,
        hashes.h160 p.2 = FinalSignedLoop.generatedCommitmentAt p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
        beforeCheck.stack =
          EncodedScript.finalEncodedScriptCode
            (a :: b :: trace.map Prod.fst) ∧
      (∀ j : Fin 10, ∃ sig key hashType,
        CoreMultisigStack.signatureAt beforeCheck.stack.reverse 10 j.val =
          some sig ∧
        CoreMultisigStack.keyAt beforeCheck.stack.reverse j.val = some key ∧
        CoreDEREncoding.valid sig = true ∧
        sig.getLast? = some hashType ∧
        validKey key = true ∧
        verify sig.dropLast key
          (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
            beforeCheck.stack) hashType = true) := by
  obtain ⟨beforeCheck, trace, a, b, reached, seven, hits,
    distinct, code, pairs⟩ :=
    CoreMultisigEval.successful_byte_run_source_check hashes initial final
      (checker validKey verify) accepted source
  refine ⟨beforeCheck, trace, a, b, reached, seven, hits,
    distinct, code, ?_⟩
  intro j
  obtain ⟨sig, key, sigAt, keyAt, der, checked⟩ := pairs j
  obtain ⟨hashType, last, keyValid, verified⟩ :=
    checker_success validKey verify sig key
      (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
        beforeCheck.stack) checked
  exact ⟨sig, key, hashType, sigAt, keyAt, der,
    last, keyValid, verified⟩

end QSB.CoreFinalChecksigEval
