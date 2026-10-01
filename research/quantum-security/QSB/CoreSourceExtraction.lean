import QSB.CoreStructuralRun
import QSB.SourceWitness
import QSB.CoreFinalChecksigEval
import QSB.CoreMultisigSourceScan

/-!
One-run extraction from the bottom-first source-shaped interpreter. The
signature checks refer to reached source stacks, including the first-round
multisignature scan, which may validly return false. The structural run still
uses supplied Booleans. A compiled-Core refinement must establish both that
run and these checker premises from a consensus-accepted transaction.
-/
namespace QSB.CoreSourceExtraction
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

private def puzzleChecked (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) (sig key : Bytes) : Bool :=
  decide (CoreChecksigEval.evalBaseVerifyAll 880
    PinPuzzleScriptCode.literalScript sig key validKey verify = some true)

private def finalPairChecked (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) (scriptCode sig key : Bytes) : Bool :=
  DERSyntax.verifyAllEncoding sig &&
    CoreMultisigEval.nonemptyVerify
      (CoreFinalChecksigEval.checker validKey verify) scriptCode sig key

/-- The first multisignature result in the structural run must equal the
source-shaped count, FindAndDelete, encoding, and key-scan result at its
reached stack. `none` is fatal, while `some false` is a valid result. -/
def firstRoundSignatureCheck (hashes : Hashes)
    (initial : CoreOpcodeStep.State) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) : Bool :=
  match CoreStructuralRun.run hashes (ByteLayout.program.take 446) initial with
  | none => false
  | some first =>
      match CoreMultisigSourceScan.scanAtStack
          EncodedLayout.chunks.flatten
          (CoreFinalChecksigEval.checker validKey verify) first.stack,
          first.outcomes.head? with
      | some actual, some supplied => actual == supplied
      | _, _ => false

/-- The other five necessary reached signature-site conditions: fixed pin,
early, first-round, and late hash puzzles, plus enforcing final multisignature.
The reached CHECKSIGVERIFY at instruction 423 is checked here; the structural
interpreter's supplied `true` is not evidence of ECDSA success. -/
def otherSignatureChecks (hashes : Hashes)
    (initial : CoreOpcodeStep.State) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) : Bool :=
  match CoreStructuralRun.run hashes (ByteLayout.program.take 2) initial,
      CoreStructuralRun.run hashes (ByteLayout.program.take 5) initial,
      CoreStructuralRun.run hashes (ByteLayout.program.take 423) initial,
      CoreStructuralRun.run hashes (ByteLayout.program.take 856) initial,
      CoreStructuralRun.run hashes (ByteLayout.program.take 879) initial with
  | some pin, some early, some firstPuzzle, some late, some final =>
      decide (
        CoreChecksigEval.evalBaseVerifyAll 880
          PinPuzzleScriptCode.literalScript
          (pin.stack.reverse[1]?.getD [])
          (pin.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreChecksigEval.evalBaseVerifyAll 880
          PinPuzzleScriptCode.literalScript
          (early.stack.reverse[1]?.getD [])
          (early.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreChecksigEval.evalBaseVerifyAll 880
          PinPuzzleScriptCode.literalScript
          (firstPuzzle.stack.reverse[1]?.getD [])
          (firstPuzzle.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreChecksigEval.evalBaseVerifyAll 880
          PinPuzzleScriptCode.literalScript
          (late.stack.reverse[1]?.getD [])
          (late.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreMultisigEval.finalTenEval EncodedLayout.chunks.flatten
          (CoreFinalChecksigEval.checker validKey verify)
          final.stack.reverse = some true)
  | _, _, _, _, _ => false

/-- Executable necessary signature-site conditions for a source-shaped run.
The first-round scan is checked even when false; an attempted malformed
signature or missing supplied outcome makes the certificate fail. This
predicate alone is not compiled Bitcoin Core Script acceptance. -/
def necessarySignatureChecks (hashes : Hashes)
    (initial : CoreOpcodeStep.State) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) : Bool :=
  otherSignatureChecks hashes initial validKey verify &&
    firstRoundSignatureCheck hashes initial validKey verify

/-- A successful certificate identifies a reached first-round source stack
and a concrete scan Boolean equal to the structural outcome. No premise
forces that Boolean to be true. -/
theorem necessary_checks_first_round_scan (hashes : Hashes)
    (initial : CoreOpcodeStep.State) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (checks : necessarySignatureChecks hashes initial validKey verify = true) :
    ∃ first actual,
      CoreStructuralRun.run hashes (ByteLayout.program.take 446) initial =
        some first ∧
      CoreMultisigSourceScan.scanAtStack
        EncodedLayout.chunks.flatten
        (CoreFinalChecksigEval.checker validKey verify) first.stack =
          some actual ∧
      first.outcomes.head? = some actual := by
  have parts : otherSignatureChecks hashes initial validKey verify = true ∧
      firstRoundSignatureCheck hashes initial validKey verify = true := by
    simpa only [necessarySignatureChecks,
      Bool.and_eq_true_eq_eq_true_and_eq_true] using checks
  have firstCheck := parts.2
  unfold firstRoundSignatureCheck at firstCheck
  cases reached : CoreStructuralRun.run hashes
      (ByteLayout.program.take 446) initial with
  | none => simp [reached] at firstCheck
  | some first =>
      cases scanned : CoreMultisigSourceScan.scanAtStack
          EncodedLayout.chunks.flatten
          (CoreFinalChecksigEval.checker validKey verify) first.stack with
      | none => simp [reached, scanned] at firstCheck
      | some actual =>
          cases supplied : first.outcomes.head? with
          | none => simp [reached, scanned, supplied] at firstCheck
          | some result =>
              have same : actual = result := by
                simpa [reached, scanned, supplied] using firstCheck
              subst result
              exact ⟨first, actual, rfl, scanned, supplied⟩

/-- The reached first-round puzzle CHECKSIGVERIFY is an actual source-shaped
checker obligation, in addition to the four other necessary checks. The
structural run alone would only consume a supplied `true` at this site. -/
theorem necessary_checks_first_puzzle (hashes : Hashes)
    (initial : CoreOpcodeStep.State) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (checks : necessarySignatureChecks hashes initial validKey verify = true) :
    ∃ beforePuzzle,
      CoreStructuralRun.run hashes (ByteLayout.program.take 423) initial =
        some beforePuzzle ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        (beforePuzzle.stack.reverse[1]?.getD [])
        (beforePuzzle.stack.reverse[0]?.getD [])
        validKey verify = some true := by
  have other : otherSignatureChecks hashes initial validKey verify = true := by
    have both : otherSignatureChecks hashes initial validKey verify = true ∧
        firstRoundSignatureCheck hashes initial validKey verify = true := by
      simpa only [necessarySignatureChecks,
        Bool.and_eq_true_eq_eq_true_and_eq_true] using checks
    exact both.1
  cases hPin : CoreStructuralRun.run hashes
      (ByteLayout.program.take 2) initial with
  | none => simp [otherSignatureChecks, hPin] at other
  | some pin =>
      cases hEarly : CoreStructuralRun.run hashes
          (ByteLayout.program.take 5) initial with
      | none => simp [otherSignatureChecks, hPin, hEarly] at other
      | some early =>
          cases hFirst : CoreStructuralRun.run hashes
              (ByteLayout.program.take 423) initial with
          | none =>
              simp [otherSignatureChecks, hPin, hEarly, hFirst] at other
          | some beforePuzzle =>
              cases hLate : CoreStructuralRun.run hashes
                  (ByteLayout.program.take 856) initial with
              | none =>
                  simp [otherSignatureChecks, hPin, hEarly,
                    hFirst, hLate] at other
              | some late =>
                  cases hFinal : CoreStructuralRun.run hashes
                      (ByteLayout.program.take 879) initial with
                  | none =>
                      simp [otherSignatureChecks, hPin, hEarly,
                        hFirst, hLate, hFinal] at other
                  | some beforeFinal =>
                      have facts :
                          CoreChecksigEval.evalBaseVerifyAll 880
                            PinPuzzleScriptCode.literalScript
                            (pin.stack.reverse[1]?.getD [])
                            (pin.stack.reverse[0]?.getD [])
                            validKey verify = some true ∧
                          CoreChecksigEval.evalBaseVerifyAll 880
                            PinPuzzleScriptCode.literalScript
                            (early.stack.reverse[1]?.getD [])
                            (early.stack.reverse[0]?.getD [])
                            validKey verify = some true ∧
                          CoreChecksigEval.evalBaseVerifyAll 880
                            PinPuzzleScriptCode.literalScript
                            (beforePuzzle.stack.reverse[1]?.getD [])
                            (beforePuzzle.stack.reverse[0]?.getD [])
                            validKey verify = some true ∧
                          CoreChecksigEval.evalBaseVerifyAll 880
                            PinPuzzleScriptCode.literalScript
                            (late.stack.reverse[1]?.getD [])
                            (late.stack.reverse[0]?.getD [])
                            validKey verify = some true ∧
                          CoreMultisigEval.finalTenEval
                            EncodedLayout.chunks.flatten
                            (CoreFinalChecksigEval.checker validKey verify)
                            beforeFinal.stack.reverse = some true := by
                        simpa [otherSignatureChecks,
                          hPin, hEarly, hFirst, hLate, hFinal] using other
                      exact ⟨beforePuzzle, rfl, facts.2.2.1⟩

/-- A single successful source-shaped structural execution and its reached
source-shaped signature checks yield the pin and enforced final-round
witnesses. The final truth premise corresponds to bare-script acceptance;
the checker-success premises are deliberately distinct from the structural
Booleans until compiled Core has been refined to this model. -/
theorem checked_source_run_pin_and_final (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool)
    (sourceFinal sourceBeforeCheck sourceBeforeLate :
      CoreOpcodeStep.State)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (sourceRun : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) = some sourceFinal)
    (truth : ByteMachine.finalTruth
      ⟨sourceFinal.stack.reverse, sourceFinal.outcomes,
        sourceFinal.ops⟩ = true)
    (finalPrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 879)
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) =
        some sourceBeforeCheck)
    (finalChecked : CoreMultisigEval.finalTenEval
      EncodedLayout.chunks.flatten
      (CoreFinalChecksigEval.checker validKey verify)
      sourceBeforeCheck.stack.reverse = some true)
    (pinChecked : ∀ nonceKey puzzleKey raw tail,
      stack = nonceKey :: puzzleKey :: raw :: tail →
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        FirstOvershoot.pinSignature nonceKey validKey verify = some true ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        (hashes.h256 nonceKey) puzzleKey validKey verify = some true)
    (latePrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 856)
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) =
        some sourceBeforeLate)
    (lateChecked : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript
      (sourceBeforeLate.stack.reverse[1]?.getD [])
      (sourceBeforeLate.stack.reverse[0]?.getD [])
      validKey verify = some true) :
    ∃ (pinKey puzzleKey raw : Bytes) (tail : List Bytes)
      (w : RoundWitness (Fin 150) Bytes Bytes),
      stack = pinKey :: puzzleKey :: raw :: tail ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        FirstOvershoot.pinSignature pinKey validKey verify = some true ∧
      DERSyntax.valid (hashes.h256 pinKey) = true ∧
      FinalRoundWitness.extractMatchedWitness hashes
        ⟨stack, outcomes, 0⟩ = some w ∧
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      DERSyntax.valid (hashes.h256 w.key) = true ∧
      sourceBeforeCheck.outcomes.head? = some true ∧
      CoreFinalChecksigEval.checker validKey verify
        PoolRollInvariant.finalNonce w.key
        (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
          sourceBeforeCheck.stack.reverse) = true := by
  let initial : ByteMachine.State := ⟨stack, outcomes, 0⟩
  obtain ⟨byteFinal, accepted, finalShape⟩ :=
    CoreStructuralRun.literal_lock_refines_byte hashes initial
      sourceFinal sourceRun
  obtain ⟨byteBeforeCheck, byteFinalPrefix, beforeCheckShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes
      (ByteLayout.program.take 879) initial sourceBeforeCheck finalPrefix
  obtain ⟨byteBeforeLate, byteLatePrefix, beforeLateShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes
      (ByteLayout.program.take 856) initial sourceBeforeLate latePrefix
  have byteTruth : ByteMachine.finalTruth byteFinal = true := by
    rw [finalShape] at truth
    simpa [CoreOpcodeStep.ofByte] using truth
  have finalSplit : ByteLayout.program =
      ByteLayout.program.take 879 ++ [.checkmultisig] := by decide
  have lastStep : ByteMachine.run hashes [.checkmultisig]
      byteBeforeCheck = some byteFinal := by
    rw [finalSplit, ByteMachine.run_append] at accepted
    simpa [byteFinalPrefix] using accepted
  have lastTrue :=
    ByteFinalCounts.successful_last_multisig_requires_true_outcome
      hashes byteBeforeCheck byteFinal lastStep byteTruth
  have sourceLastTrue : sourceBeforeCheck.outcomes.head? = some true := by
    rw [beforeCheckShape]
    exact lastTrue
  have finalStack : byteBeforeCheck.stack =
      sourceBeforeCheck.stack.reverse := by
    rw [beforeCheckShape]
    simp [CoreOpcodeStep.ofByte]
  have lateStack : byteBeforeLate.stack =
      sourceBeforeLate.stack.reverse := by
    rw [beforeLateShape]
    simp [CoreOpcodeStep.ofByte]
  let scriptCode := CoreMultisigEval.deletedScript
    EncodedLayout.chunks.flatten byteBeforeCheck.stack
  let pairVerify : Bytes → Bytes → Bool :=
    finalPairChecked validKey verify scriptCode
  have pairNonempty : ∀ sig key,
      pairVerify sig key = true → sig ≠ [] := by
    intro sig key checked
    have parts : DERSyntax.verifyAllEncoding sig = true ∧
        CoreMultisigEval.nonemptyVerify
          (CoreFinalChecksigEval.checker validKey verify)
          scriptCode sig key = true := by
      simpa only [pairVerify, finalPairChecked,
        Bool.and_eq_true_eq_eq_true_and_eq_true] using checked
    exact (CoreMultisigEval.nonemptyVerify_sound _ _ _ _ parts.2).1
  have pairEncoding : ∀ sig key,
      pairVerify sig key = true →
      DERSyntax.verifyAllEncoding sig = true := by
    intro sig key checked
    have parts : DERSyntax.verifyAllEncoding sig = true ∧
        CoreMultisigEval.nonemptyVerify
          (CoreFinalChecksigEval.checker validKey verify)
          scriptCode sig key = true := by
      simpa only [pairVerify, finalPairChecked,
        Bool.and_eq_true_eq_eq_true_and_eq_true] using checked
    exact parts.1
  have pairMatched : ∀ beforeCheck : ByteMachine.State,
      ByteMachine.run hashes (ByteLayout.program.take 879) initial =
        some beforeCheck →
      Multisig.matchSigs pairVerify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true := by
    intro beforeCheck reached
    have same : beforeCheck = byteBeforeCheck :=
      Option.some.inj (reached.symm.trans byteFinalPrefix)
    subst beforeCheck
    change Multisig.matchSigs
      (fun sig key => DERSyntax.verifyAllEncoding sig &&
        CoreMultisigEval.nonemptyVerify
          (CoreFinalChecksigEval.checker validKey verify)
          (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
            byteBeforeCheck.stack) sig key)
      ((byteBeforeCheck.stack.drop 12).take 10)
      ((byteBeforeCheck.stack.drop 1).take 10) = true
    exact CoreMultisigEval.finalTenEval_success_match
      EncodedLayout.chunks.flatten
      (CoreFinalChecksigEval.checker validKey verify)
      byteBeforeCheck.stack (by rw [finalStack]; exact finalChecked)
  have pinMatched : ∀ nonceKey puzzleKey raw tail,
      stack = nonceKey :: puzzleKey :: raw :: tail →
      puzzleChecked validKey verify FirstOvershoot.pinSignature nonceKey = true ∧
      puzzleChecked validKey verify (hashes.h256 nonceKey) puzzleKey = true := by
    intro nonceKey puzzleKey raw tail shape
    obtain ⟨fixed, puzzle⟩ := pinChecked nonceKey puzzleKey raw tail shape
    simp [puzzleChecked, fixed, puzzle]
  have puzzleEncoding : ∀ sig key,
      puzzleChecked validKey verify sig key = true →
      DERSyntax.verifyAllEncoding sig = true := by
    intro sig key checked
    have source : CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript sig key validKey verify =
        some true := by simpa [puzzleChecked] using checked
    obtain ⟨_hashType, _last, der, _key, _verified⟩ :=
      CoreChecksigEval.successful_base_check 880
        PinPuzzleScriptCode.literalScript sig key validKey verify source
    have nonempty : sig ≠ [] := by
      intro empty
      subst sig
      simp [DERSyntax.valid] at der
    simpa [DERSyntax.verifyAllEncoding_nonempty sig nonempty] using der
  have puzzleMatched : ∀ beforeVerify : ByteMachine.State,
      ByteMachine.run hashes (ByteLayout.program.take 856) initial =
        some beforeVerify →
      puzzleChecked validKey verify
        (beforeVerify.stack[1]?.getD [])
        (beforeVerify.stack[0]?.getD []) = true := by
    intro beforeVerify reached
    have same : beforeVerify = byteBeforeLate :=
      Option.some.inj (reached.symm.trans byteLatePrefix)
    subst beforeVerify
    simp [puzzleChecked, lateStack, lateChecked]
  obtain ⟨pinKey, puzzleKey, raw, tail, _later, w,
    stackShape, _outcomeShape, fixedChecked, pinDER,
    computedWitness, roundShape, openings,
    nonceChecked, finalDER⟩ :=
    SourceWitness.matched_run_pin_and_final_der_puzzles hashes
      stack outcomes byteFinal accepted
      (puzzleChecked validKey verify)
      (puzzleChecked validKey verify)
      pairVerify (puzzleChecked validKey verify)
      pinMatched puzzleEncoding pairNonempty pairEncoding pairMatched
      puzzleEncoding puzzleMatched
  have fixedSource : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript
      FirstOvershoot.pinSignature pinKey validKey verify = some true := by
    simpa [puzzleChecked] using fixedChecked
  have checkerSuccess : CoreFinalChecksigEval.checker validKey verify
      PoolRollInvariant.finalNonce w.key scriptCode = true := by
    have parts : DERSyntax.verifyAllEncoding
        PoolRollInvariant.finalNonce = true ∧
        CoreMultisigEval.nonemptyVerify
          (CoreFinalChecksigEval.checker validKey verify)
          scriptCode PoolRollInvariant.finalNonce w.key = true := by
      simpa only [pairVerify, finalPairChecked,
        Bool.and_eq_true_eq_eq_true_and_eq_true] using nonceChecked
    exact (CoreMultisigEval.nonemptyVerify_sound _ _ _ _ parts.2).2
  exact ⟨pinKey, puzzleKey, raw, tail, w,
    stackShape, fixedSource, pinDER,
    computedWitness, roundShape, openings, finalDER, sourceLastTrue,
    by rw [← finalStack]; exact checkerSuccess⟩

/-- The first two pinning checker sites read exactly the fixed nonce signature
and the SHA256 of its reached key, regardless of cells below the first raw
index. The successful-prefix premises carry Core's stack limit. -/
private theorem reached_pin_site_stacks (hashes : Hashes)
    (nonce puzzle raw : Bytes) (tail : List Bytes)
    (later : List Bool) (first second : ByteMachine.State)
    (firstReached : ByteMachine.run hashes (ByteLayout.program.take 2)
      ⟨nonce :: puzzle :: raw :: tail, true :: true :: later, 0⟩ =
        some first)
    (secondReached : ByteMachine.run hashes (ByteLayout.program.take 5)
      ⟨nonce :: puzzle :: raw :: tail, true :: true :: later, 0⟩ =
        some second) :
    first.stack = nonce :: FirstOvershoot.pinSignature ::
      nonce :: puzzle :: raw :: tail ∧
    second.stack = puzzle :: hashes.h256 nonce :: raw :: tail := by
  have firstOps : ByteLayout.program.take 2 =
      [.push FirstOvershoot.pinSignature, .over] := by decide
  have secondOps : ByteLayout.program.take 5 =
      [.push FirstOvershoot.pinSignature, .over,
        .checksigverify, .sha256, .swap] := by decide
  have small : tail.length ≤ 995 := by
    by_contra tooLarge
    have large : 996 ≤ tail.length := by omega
    have fails := FirstOvershoot.oversized_initial_stack_fails_first_two
      hashes nonce puzzle raw tail later large
    rw [fails] at firstReached
    cases firstReached
  have pushStep : ByteMachine.step hashes
      (.push FirstOvershoot.pinSignature)
      ⟨nonce :: puzzle :: raw :: tail, true :: true :: later, 0⟩ =
      some ⟨FirstOvershoot.pinSignature :: nonce :: puzzle :: raw :: tail,
        true :: true :: later, 0⟩ := by
    unfold ByteMachine.step
    simp [FirstOvershoot.pin_signature_fits]
  have overStep : ByteMachine.step hashes .over
      ⟨FirstOvershoot.pinSignature :: nonce :: puzzle :: raw :: tail,
        true :: true :: later, 0⟩ =
      some ⟨nonce :: FirstOvershoot.pinSignature :: nonce ::
        puzzle :: raw :: tail, true :: true :: later, 1⟩ := by
    unfold ByteMachine.step
    simp
  have firstExact : ByteMachine.run hashes (ByteLayout.program.take 2)
      ⟨nonce :: puzzle :: raw :: tail, true :: true :: later, 0⟩ =
      some ⟨nonce :: FirstOvershoot.pinSignature :: nonce ::
        puzzle :: raw :: tail, true :: true :: later, 1⟩ := by
    rw [firstOps]
    simp [ByteMachine.run, pushStep, overStep]
    omega
  have checkStep : ByteMachine.step hashes .checksigverify
      ⟨nonce :: FirstOvershoot.pinSignature :: nonce ::
        puzzle :: raw :: tail, true :: true :: later, 1⟩ =
      some ⟨nonce :: puzzle :: raw :: tail, true :: later, 2⟩ := by
    unfold ByteMachine.step
    simp
  have hashStep : ByteMachine.step hashes .sha256
      ⟨nonce :: puzzle :: raw :: tail, true :: later, 2⟩ =
      some ⟨hashes.h256 nonce :: puzzle :: raw :: tail,
        true :: later, 3⟩ := by
    unfold ByteMachine.step
    simp
  have swapStep : ByteMachine.step hashes .swap
      ⟨hashes.h256 nonce :: puzzle :: raw :: tail,
        true :: later, 3⟩ =
      some ⟨puzzle :: hashes.h256 nonce :: raw :: tail,
        true :: later, 4⟩ := by
    unfold ByteMachine.step
    simp
  have secondExact : ByteMachine.run hashes (ByteLayout.program.take 5)
      ⟨nonce :: puzzle :: raw :: tail, true :: true :: later, 0⟩ =
      some ⟨puzzle :: hashes.h256 nonce :: raw :: tail,
        true :: later, 4⟩ := by
    rw [secondOps]
    simp [ByteMachine.run, pushStep, overStep, checkStep,
      hashStep, swapStep]
    omega
  constructor
  · have same := Option.some.inj (firstReached.symm.trans firstExact)
    exact congrArg ByteMachine.State.stack same
  · have same := Option.some.inj (secondReached.symm.trans secondExact)
    exact congrArg ByteMachine.State.stack same

/-- This version reads both pinning checks from the reached bottom-first
source stacks, rather than assuming a verifier statement over a proposed
initial-stack decomposition. The late puzzle and final scan are likewise
evaluated at their reached source prefixes. -/
theorem checked_reached_source_run_pin_and_final (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool)
    (sourceFinal sourceBeforeFirst sourceBeforeSecond
      sourceBeforeCheck sourceBeforeLate : CoreOpcodeStep.State)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (sourceRun : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) = some sourceFinal)
    (truth : ByteMachine.finalTruth
      ⟨sourceFinal.stack.reverse, sourceFinal.outcomes,
        sourceFinal.ops⟩ = true)
    (firstPrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 2)
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) =
        some sourceBeforeFirst)
    (secondPrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 5)
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) =
        some sourceBeforeSecond)
    (firstChecked : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript
      (sourceBeforeFirst.stack.reverse[1]?.getD [])
      (sourceBeforeFirst.stack.reverse[0]?.getD [])
      validKey verify = some true)
    (secondChecked : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript
      (sourceBeforeSecond.stack.reverse[1]?.getD [])
      (sourceBeforeSecond.stack.reverse[0]?.getD [])
      validKey verify = some true)
    (finalPrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 879)
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) =
        some sourceBeforeCheck)
    (finalChecked : CoreMultisigEval.finalTenEval
      EncodedLayout.chunks.flatten
      (CoreFinalChecksigEval.checker validKey verify)
      sourceBeforeCheck.stack.reverse = some true)
    (latePrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 856)
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) =
        some sourceBeforeLate)
    (lateChecked : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript
      (sourceBeforeLate.stack.reverse[1]?.getD [])
      (sourceBeforeLate.stack.reverse[0]?.getD [])
      validKey verify = some true) :
    ∃ (pinKey puzzleKey raw : Bytes) (tail : List Bytes)
      (w : RoundWitness (Fin 150) Bytes Bytes),
      stack = pinKey :: puzzleKey :: raw :: tail ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        FirstOvershoot.pinSignature pinKey validKey verify = some true ∧
      DERSyntax.valid (hashes.h256 pinKey) = true ∧
      FinalRoundWitness.extractMatchedWitness hashes
        ⟨stack, outcomes, 0⟩ = some w ∧
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      DERSyntax.valid (hashes.h256 w.key) = true ∧
      sourceBeforeCheck.outcomes.head? = some true ∧
      CoreFinalChecksigEval.checker validKey verify
        PoolRollInvariant.finalNonce w.key
        (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
          sourceBeforeCheck.stack.reverse) = true := by
  let initial : ByteMachine.State := ⟨stack, outcomes, 0⟩
  obtain ⟨byteFinal, accepted, _finalShape⟩ :=
    CoreStructuralRun.literal_lock_refines_byte hashes initial
      sourceFinal sourceRun
  obtain ⟨nonce, puzzle, raw, tail, later,
    initialShape, outcomeShape⟩ :=
    PinningShape.accepted_initial_shape hashes stack outcomes
      byteFinal accepted
  obtain ⟨byteFirst, firstReached, firstShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes
      (ByteLayout.program.take 2) initial sourceBeforeFirst firstPrefix
  obtain ⟨byteSecond, secondReached, secondShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes
      (ByteLayout.program.take 5) initial sourceBeforeSecond secondPrefix
  have firstRun : ByteMachine.run hashes (ByteLayout.program.take 2)
      ⟨nonce :: puzzle :: raw :: tail, true :: true :: later, 0⟩ =
        some byteFirst := by
    simpa [initial, initialShape, outcomeShape] using firstReached
  have secondRun : ByteMachine.run hashes (ByteLayout.program.take 5)
      ⟨nonce :: puzzle :: raw :: tail, true :: true :: later, 0⟩ =
        some byteSecond := by
    simpa [initial, initialShape, outcomeShape] using secondReached
  obtain ⟨firstStack, secondStack⟩ :=
    reached_pin_site_stacks hashes nonce puzzle raw tail later
      byteFirst byteSecond firstRun secondRun
  have sourceFirstStack : sourceBeforeFirst.stack.reverse =
      nonce :: FirstOvershoot.pinSignature :: nonce ::
        puzzle :: raw :: tail := by
    rw [firstShape]
    simpa [CoreOpcodeStep.ofByte] using firstStack
  have sourceSecondStack : sourceBeforeSecond.stack.reverse =
      puzzle :: hashes.h256 nonce :: raw :: tail := by
    rw [secondShape]
    simpa [CoreOpcodeStep.ofByte] using secondStack
  have fixedChecked : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript FirstOvershoot.pinSignature
      nonce validKey verify = some true := by
    simpa [sourceFirstStack] using firstChecked
  have puzzleChecked : CoreChecksigEval.evalBaseVerifyAll 880
      PinPuzzleScriptCode.literalScript (hashes.h256 nonce)
      puzzle validKey verify = some true := by
    simpa [sourceSecondStack] using secondChecked
  have pinMatched : ∀ nonceKey puzzleKey index rest,
      stack = nonceKey :: puzzleKey :: index :: rest →
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        FirstOvershoot.pinSignature nonceKey validKey verify = some true ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        (hashes.h256 nonceKey) puzzleKey validKey verify = some true := by
    intro nonceKey puzzleKey index rest shape
    have same : nonce :: puzzle :: raw :: tail =
        nonceKey :: puzzleKey :: index :: rest :=
      initialShape.symm.trans shape
    simp only [List.cons.injEq] at same
    rcases same with ⟨rfl, rfl, rfl, _⟩
    exact ⟨fixedChecked, puzzleChecked⟩
  exact checked_source_run_pin_and_final hashes stack outcomes
    sourceFinal sourceBeforeCheck sourceBeforeLate validKey verify
    sourceRun truth finalPrefix finalChecked pinMatched
    latePrefix lateChecked

/-- The compact acceptance boundary: a truthy successful source-shaped
structural run whose four necessary reached checker evaluations succeed
provides one pinning key and a seven-plus-two final witness. This is the
strongest checked source-model extraction here. The premise is still not a
claim about compiled Bitcoin Core or a quantum probability bound. -/
theorem necessary_checks_extract_pin_and_final (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool)
    (sourceFinal : CoreOpcodeStep.State)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (sourceRun : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) = some sourceFinal)
    (truth : ByteMachine.finalTruth
      ⟨sourceFinal.stack.reverse, sourceFinal.outcomes,
        sourceFinal.ops⟩ = true)
    (checks : necessarySignatureChecks hashes
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩)
      validKey verify = true) :
    ∃ (pinKey puzzleKey raw : Bytes) (tail : List Bytes)
      (w : RoundWitness (Fin 150) Bytes Bytes)
      (sourceBeforeCheck : CoreOpcodeStep.State),
      stack = pinKey :: puzzleKey :: raw :: tail ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        FirstOvershoot.pinSignature pinKey validKey verify = some true ∧
      DERSyntax.valid (hashes.h256 pinKey) = true ∧
      FinalRoundWitness.extractMatchedWitness hashes
        ⟨stack, outcomes, 0⟩ = some w ∧
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      DERSyntax.valid (hashes.h256 w.key) = true ∧
      CoreStructuralRun.run hashes (ByteLayout.program.take 879)
        (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) =
          some sourceBeforeCheck ∧
      sourceBeforeCheck.outcomes.head? = some true ∧
      CoreFinalChecksigEval.checker validKey verify
        PoolRollInvariant.finalNonce w.key
        (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
          sourceBeforeCheck.stack.reverse) = true := by
  have otherChecks : otherSignatureChecks hashes
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩)
      validKey verify = true := by
    have parts : otherSignatureChecks hashes
        (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩)
        validKey verify = true ∧
        firstRoundSignatureCheck hashes
          (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩)
          validKey verify = true := by
      simpa only [necessarySignatureChecks,
        Bool.and_eq_true_eq_eq_true_and_eq_true] using checks
    exact parts.1
  let initial : CoreOpcodeStep.State :=
    CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩
  cases hPin : CoreStructuralRun.run hashes
      (ByteLayout.program.take 2) initial with
  | none => simp [otherSignatureChecks, initial, hPin] at otherChecks
  | some pin =>
      cases hEarly : CoreStructuralRun.run hashes
          (ByteLayout.program.take 5) initial with
      | none =>
          simp [otherSignatureChecks, initial, hPin, hEarly] at otherChecks
      | some early =>
          have ⟨firstPuzzle, hFirst⟩ :
              ∃ firstPuzzle, CoreStructuralRun.run hashes
                (ByteLayout.program.take 423) initial =
                  some firstPuzzle := by
            cases h : CoreStructuralRun.run hashes
                (ByteLayout.program.take 423) initial with
            | none =>
                simp [otherSignatureChecks, initial, hPin, hEarly, h]
                  at otherChecks
            | some reached => exact ⟨reached, rfl⟩
          cases hLate : CoreStructuralRun.run hashes
              (ByteLayout.program.take 856) initial with
          | none =>
              simp [otherSignatureChecks, initial, hPin,
                hEarly, hFirst, hLate] at otherChecks
          | some late =>
              cases hFinal : CoreStructuralRun.run hashes
                  (ByteLayout.program.take 879) initial with
              | none =>
                  simp [otherSignatureChecks, initial, hPin,
                    hEarly, hFirst, hLate, hFinal] at otherChecks
              | some beforeCheck =>
                  have allFacts :
                      CoreChecksigEval.evalBaseVerifyAll 880
                        PinPuzzleScriptCode.literalScript
                        (pin.stack.reverse[1]?.getD [])
                        (pin.stack.reverse[0]?.getD [])
                        validKey verify = some true ∧
                      CoreChecksigEval.evalBaseVerifyAll 880
                        PinPuzzleScriptCode.literalScript
                        (early.stack.reverse[1]?.getD [])
                        (early.stack.reverse[0]?.getD [])
                        validKey verify = some true ∧
                      CoreChecksigEval.evalBaseVerifyAll 880
                        PinPuzzleScriptCode.literalScript
                        (firstPuzzle.stack.reverse[1]?.getD [])
                        (firstPuzzle.stack.reverse[0]?.getD [])
                        validKey verify = some true ∧
                      CoreChecksigEval.evalBaseVerifyAll 880
                        PinPuzzleScriptCode.literalScript
                        (late.stack.reverse[1]?.getD [])
                        (late.stack.reverse[0]?.getD [])
                        validKey verify = some true ∧
                      CoreMultisigEval.finalTenEval
                        EncodedLayout.chunks.flatten
                        (CoreFinalChecksigEval.checker validKey verify)
                        beforeCheck.stack.reverse = some true := by
                    simpa [otherSignatureChecks, initial,
                      hPin, hEarly, hFirst, hLate, hFinal] using otherChecks
                  have facts :
                      CoreChecksigEval.evalBaseVerifyAll 880
                        PinPuzzleScriptCode.literalScript
                        (pin.stack.reverse[1]?.getD [])
                        (pin.stack.reverse[0]?.getD [])
                        validKey verify = some true ∧
                      CoreChecksigEval.evalBaseVerifyAll 880
                        PinPuzzleScriptCode.literalScript
                        (early.stack.reverse[1]?.getD [])
                        (early.stack.reverse[0]?.getD [])
                        validKey verify = some true ∧
                      CoreChecksigEval.evalBaseVerifyAll 880
                        PinPuzzleScriptCode.literalScript
                        (late.stack.reverse[1]?.getD [])
                        (late.stack.reverse[0]?.getD [])
                        validKey verify = some true ∧
                      CoreMultisigEval.finalTenEval
                        EncodedLayout.chunks.flatten
                        (CoreFinalChecksigEval.checker validKey verify)
                        beforeCheck.stack.reverse = some true := by
                    exact ⟨allFacts.1, allFacts.2.1,
                      allFacts.2.2.2.1, allFacts.2.2.2.2⟩
                  obtain ⟨pinKey, puzzleKey, raw, tail, w,
                    stackShape, fixed, pinDER, computedWitness, roundShape,
                    openings, finalDER, finalOutcome, nonce⟩ :=
                    checked_reached_source_run_pin_and_final
                      hashes stack outcomes sourceFinal pin early
                      beforeCheck late validKey verify
                      sourceRun truth
                      (by simpa [initial] using hPin)
                      (by simpa [initial] using hEarly)
                      facts.1 facts.2.1
                      (by simpa [initial] using hFinal)
                      facts.2.2.2
                      (by simpa [initial] using hLate)
                      facts.2.2.1
                  exact ⟨pinKey, puzzleKey, raw, tail, w, beforeCheck,
                    stackShape, fixed, pinDER, computedWitness, roundShape, openings,
                    finalDER, by simp [initial] at hFinal ⊢,
                    finalOutcome, nonce⟩

/-- The same reached-source certificate identifies the two fixed-signature
SIGHASH_ALL calls on their exact source-shaped legacy scriptCodes. The
`verify` function still requires refinement to Core's SHA256d and ECDSA
checker, and this statement does not assert a transaction binding. -/
theorem necessary_checks_fixed_all_calls (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool)
    (sourceFinal : CoreOpcodeStep.State)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (sourceRun : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩) = some sourceFinal)
    (truth : ByteMachine.finalTruth
      ⟨sourceFinal.stack.reverse, sourceFinal.outcomes,
        sourceFinal.ops⟩ = true)
    (checks : necessarySignatureChecks hashes
      (CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩)
      validKey verify = true) :
    ∃ (pinKey : Bytes) (w : RoundWitness (Fin 150) Bytes Bytes)
      (beforeCheck : CoreOpcodeStep.State),
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      FinalRoundWitness.extractMatchedWitness hashes
        ⟨stack, outcomes, 0⟩ = some w ∧
      DERSyntax.valid (hashes.h256 pinKey) = true ∧
      DERSyntax.valid (hashes.h256 w.key) = true ∧
      validKey pinKey = true ∧
      verify FirstOvershoot.pinSignature.dropLast pinKey
        (ScriptCodeSelection.stripEncodedChunks
          [FindAndDelete.pinPattern] EncodedLayout.chunks) 0x01 = true ∧
      validKey w.key = true ∧
      verify PoolRollInvariant.finalNonce.dropLast w.key
        (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
          beforeCheck.stack.reverse) 0x01 = true := by
  obtain ⟨pinKey, _puzzleKey, _raw, _tail, w, beforeCheck,
    _stackShape, fixedEval, pinDER, computedWitness, roundShape, openings,
    finalDER, _reached, _outcome, nonceEval⟩ :=
    necessary_checks_extract_pin_and_final hashes stack outcomes
      sourceFinal validKey verify sourceRun truth checks
  obtain ⟨pinFlag, pinLast, _pinEncoding, pinKeyValid,
    pinVerified⟩ :=
    CoreChecksigEval.successful_base_check 880
      PinPuzzleScriptCode.literalScript
      FirstOvershoot.pinSignature pinKey validKey verify fixedEval
  have pinAll : pinFlag = 0x01 :=
    Option.some.inj
      (pinLast.symm.trans FindAndDelete.pin_signature_sighash_all)
  subst pinFlag
  change verify FirstOvershoot.pinSignature.dropLast pinKey
    (CoreFindAndDelete.run 880 PinPuzzleScriptCode.literalScript
      FindAndDelete.pinPattern) 0x01 = true at pinVerified
  unfold PinPuzzleScriptCode.literalScript at pinVerified
  rw [CoreFindAndDelete.pin_scriptCode_run] at pinVerified
  obtain ⟨finalFlag, finalLast, finalKeyValid,
    finalVerified⟩ :=
    CoreFinalChecksigEval.checker_success validKey verify
      PoolRollInvariant.finalNonce w.key
      (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
        beforeCheck.stack.reverse) nonceEval
  have finalAll : finalFlag = 0x01 :=
    Option.some.inj
      (finalLast.symm.trans ScriptCodeSelection.finalNonce_sighash_all)
  subst finalFlag
  exact ⟨pinKey, w, beforeCheck, roundShape, openings,
    computedWitness, pinDER, finalDER, pinKeyValid, pinVerified,
    finalKeyValid, finalVerified⟩

end QSB.CoreSourceExtraction
