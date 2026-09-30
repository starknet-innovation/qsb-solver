import QSB.PinningScriptCode
import QSB.FinalRoundWitness

/-!
One-run byte-model extraction shell. Both the pinning key and the final-round
key come from the same successful execution on an arbitrary initial stack.
The signature verifiers and their links to Core's transaction sighashes are
premises, so this is not yet a consensus-accepted-spend theorem.
-/
namespace QSB.SourceWitness
open ByteMachine

theorem matched_run_pin_and_final_der_puzzles (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool) (final : State)
    (accepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final)
    (pinNonceVerify pinPuzzleVerify finalVerify finalPuzzleVerify :
      Bytes → Bytes → Bool)
    (pinMatched : ∀ nonceKey puzzleKey raw tail,
      stack = nonceKey :: puzzleKey :: raw :: tail →
      pinNonceVerify FirstOvershoot.pinSignature nonceKey = true ∧
      pinPuzzleVerify (hashes.h256 nonceKey) puzzleKey = true)
    (pinPuzzleEncoding : ∀ sig key,
      pinPuzzleVerify sig key = true →
      DERSyntax.verifyAllEncoding sig = true)
    (finalNonempty : ∀ sig key,
      finalVerify sig key = true → sig ≠ [])
    (finalEncoding : ∀ sig key,
      finalVerify sig key = true →
      DERSyntax.verifyAllEncoding sig = true)
    (finalMatched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879)
        (State.mk stack outcomes 0) = some beforeCheck →
      Multisig.matchSigs finalVerify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true)
    (finalPuzzleEncoding : ∀ sig key,
      finalPuzzleVerify sig key = true →
      DERSyntax.verifyAllEncoding sig = true)
    (finalPuzzleMatched : ∀ beforeVerify : State,
      run hashes (ByteLayout.program.take 856)
        (State.mk stack outcomes 0) = some beforeVerify →
      finalPuzzleVerify (beforeVerify.stack[1]?.getD [])
        (beforeVerify.stack[0]?.getD []) = true) :
    ∃ (pinKey puzzleKey raw : Bytes) (tail : List Bytes) (later : List Bool)
      (w : RoundWitness (Fin 150) Bytes Bytes),
      stack = pinKey :: puzzleKey :: raw :: tail ∧
      outcomes = true :: true :: later ∧
      pinNonceVerify FirstOvershoot.pinSignature pinKey = true ∧
      DERSyntax.valid (hashes.h256 pinKey) = true ∧
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      finalVerify PoolRollInvariant.finalNonce w.key = true ∧
      DERSyntax.valid (hashes.h256 w.key) = true := by
  obtain ⟨pinKey, puzzleKey, raw, tail, later,
    shape, checks, pinVerified, _pinPuzzleVerified, pinDER⟩ :=
    PinningScriptCode.matched_run_pinning_der_puzzle
      hashes stack outcomes final accepted
      pinNonceVerify pinPuzzleVerify pinMatched pinPuzzleEncoding
  obtain ⟨w, roundShape, openings, finalNonceVerified, finalDER⟩ :=
    FinalRoundWitness.matched_run_reached_key_der_puzzle
      hashes (State.mk stack outcomes 0) final accepted
      finalVerify finalPuzzleVerify finalNonempty finalEncoding
      finalMatched finalPuzzleEncoding finalPuzzleMatched
  exact ⟨pinKey, puzzleKey, raw, tail, later, w,
    shape, checks, pinVerified, pinDER,
    roundShape, openings, finalNonceVerified, finalDER⟩

end QSB.SourceWitness
