import QSB.CoreStructuralRun
import QSB.SourceWitness
import QSB.CoreFinalChecksigEval

/-!
One-run extraction from the bottom-first source-shaped interpreter. The three
signature-check premises refer to reached source stacks: the pinning pair,
the late puzzle pair, and the final ten-pair scan. The structural run still
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

/-- Executable necessary signature-site conditions for a source-shaped run.
The four checked sites are the fixed pin, early hash puzzle, late hash puzzle,
and enforcing final multisignature. The first-round multisignature can return
false and remains overapproximated here; its fatal encoding errors still need
Core refinement. This predicate alone is not Script acceptance. -/
def necessarySignatureChecks (hashes : Hashes)
    (initial : CoreOpcodeStep.State) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) : Bool :=
  match CoreStructuralRun.run hashes (ByteLayout.program.take 2) initial,
      CoreStructuralRun.run hashes (ByteLayout.program.take 5) initial,
      CoreStructuralRun.run hashes (ByteLayout.program.take 856) initial,
      CoreStructuralRun.run hashes (ByteLayout.program.take 879) initial with
  | some pin, some early, some late, some final =>
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
          (late.stack.reverse[1]?.getD [])
          (late.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreMultisigEval.finalTenEval EncodedLayout.chunks.flatten
          (CoreFinalChecksigEval.checker validKey verify)
          final.stack.reverse = some true)
  | _, _, _, _ => false

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
    roundShape, openings, nonceChecked, finalDER⟩ :=
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
    roundShape, openings, finalDER, sourceLastTrue,
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
  let initial : CoreOpcodeStep.State :=
    CoreOpcodeStep.ofByte ⟨stack, outcomes, 0⟩
  cases hPin : CoreStructuralRun.run hashes
      (ByteLayout.program.take 2) initial with
  | none => simp [necessarySignatureChecks, initial, hPin] at checks
  | some pin =>
      cases hEarly : CoreStructuralRun.run hashes
          (ByteLayout.program.take 5) initial with
      | none =>
          simp [necessarySignatureChecks, initial, hPin, hEarly] at checks
      | some early =>
          cases hLate : CoreStructuralRun.run hashes
              (ByteLayout.program.take 856) initial with
          | none =>
              simp [necessarySignatureChecks, initial, hPin,
                hEarly, hLate] at checks
          | some late =>
              cases hFinal : CoreStructuralRun.run hashes
                  (ByteLayout.program.take 879) initial with
              | none =>
                  simp [necessarySignatureChecks, initial, hPin,
                    hEarly, hLate, hFinal] at checks
              | some beforeCheck =>
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
                    simpa [necessarySignatureChecks, initial,
                      hPin, hEarly, hLate, hFinal] using checks
                  obtain ⟨pinKey, puzzleKey, raw, tail, w,
                    stackShape, fixed, pinDER, roundShape,
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
                    stackShape, fixed, pinDER, roundShape, openings,
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
    _stackShape, fixedEval, pinDER, roundShape, openings,
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
    pinDER, finalDER, pinKeyValid, pinVerified,
    finalKeyValid, finalVerified⟩

end QSB.CoreSourceExtraction
