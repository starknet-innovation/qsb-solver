import QSB.CoreSourceExtraction

/-!
An executable certificate search for the six signature sites in the literal
QSB lock. Four `CHECKSIGVERIFY` sites and the enforcing final multisignature
must succeed. The first multisignature is not a VERIFY opcode, so its scan may
return either Boolean. The search tries those two cases and checks the actual
reached source-shaped signature evaluators before returning a certificate.

The stack, hash functions, key parser, and ECDSA checker are inputs. This is
not a Bitcoin Core refinement or a quantum probability theorem. In particular,
the checker must later be tied to the transaction and compiled Core behavior.
-/
namespace QSB.CoreCheckedCertificate
open ByteMachine

/-- The six signature outcomes in literal opcode order. The fourth site is
the non-enforcing first-round CHECKMULTISIG. -/
def outcomes (firstRound : Bool) : List Bool :=
  [true, true, true, firstRound, true, true]

def initial (stack : List Bytes) (firstRound : Bool) :
    CoreOpcodeStep.State :=
  CoreOpcodeStep.ofByte ⟨stack, outcomes firstRound, 0⟩

/-- A successful candidate has both the full structural run and the
source-shaped checks on the reached signature stacks. -/
def candidate (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) : Option CoreOpcodeStep.State := do
  let final ← CoreStructuralRun.run hashes ByteLayout.program
    (initial stack firstRound)
  if ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ &&
      CoreSourceExtraction.necessarySignatureChecks hashes
        (initial stack firstRound) validKey verify then
    some final
  else none

/-- No signature-scan Boolean is supplied by the caller. A false first-round
result is tried first because it is a legitimate non-enforcing transition. -/
def search (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA) :
    Option (Bool × CoreOpcodeStep.State) :=
  match candidate hashes stack validKey verify false with
  | some final => some (false, final)
  | none =>
      match candidate hashes stack validKey verify true with
      | some final => some (true, final)
      | none => none

theorem candidate_sound (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : candidate hashes stack validKey verify firstRound =
      some final) :
    CoreStructuralRun.run hashes ByteLayout.program
      (initial stack firstRound) = some final ∧
    ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true ∧
    CoreSourceExtraction.necessarySignatureChecks hashes
      (initial stack firstRound) validKey verify = true := by
  unfold candidate at found
  cases runEq : CoreStructuralRun.run hashes ByteLayout.program
      (initial stack firstRound) with
  | none => simp [runEq] at found
  | some reached =>
      simp [runEq] at found
      have conditions := found.1
      have same := found.2
      subst reached
      exact ⟨rfl, conditions.1, conditions.2⟩

theorem candidate_complete (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (runEq : CoreStructuralRun.run hashes ByteLayout.program
      (initial stack firstRound) = some final)
    (truth : ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true)
    (checks : CoreSourceExtraction.necessarySignatureChecks hashes
      (initial stack firstRound) validKey verify = true) :
    candidate hashes stack validKey verify firstRound = some final := by
  simp [candidate, runEq, truth, checks]

/-- Soundness of the two-candidate algorithm: every returned certificate
has a checked source-shaped run and true final stack. -/
theorem search_sound (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes stack validKey verify =
      some (firstRound, final)) :
    CoreStructuralRun.run hashes ByteLayout.program
      (initial stack firstRound) = some final ∧
    ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true ∧
    CoreSourceExtraction.necessarySignatureChecks hashes
      (initial stack firstRound) validKey verify = true := by
  unfold search at found
  cases falseResult : candidate hashes stack validKey verify false with
  | some reached =>
      simp [falseResult] at found
      rcases found with ⟨rfl, rfl⟩
      exact candidate_sound hashes stack validKey verify false reached falseResult
  | none =>
      cases trueResult : candidate hashes stack validKey verify true with
      | none => simp [falseResult, trueResult] at found
      | some reached =>
          simp [falseResult, trueResult] at found
          rcases found with ⟨rfl, rfl⟩
          exact candidate_sound hashes stack validKey verify true reached trueResult

/-- The search examines the entire two-element result space of the first
non-enforcing multisignature; a checked candidate cannot be missed. -/
theorem search_complete (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (available : ∃ firstRound final,
      CoreStructuralRun.run hashes ByteLayout.program
        (initial stack firstRound) = some final ∧
      ByteMachine.finalTruth
        ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true ∧
      CoreSourceExtraction.necessarySignatureChecks hashes
        (initial stack firstRound) validKey verify = true) :
    ∃ firstRound final,
      search hashes stack validKey verify = some (firstRound, final) := by
  obtain ⟨firstRound, final, runEq, truth, checks⟩ := available
  have hit := candidate_complete hashes stack validKey verify
    firstRound final runEq truth checks
  cases firstRound with
  | false => exact ⟨false, final, by simp [search, hit]⟩
  | true =>
      cases other : candidate hashes stack validKey verify false with
      | none => exact ⟨true, final, by simp [search, other, hit]⟩
      | some otherFinal =>
          exact ⟨false, otherFinal, by simp [search, other]⟩

/-- The returned certificate includes the previously omitted first-round
puzzle check at the reached instruction-423 stack. -/
theorem search_first_puzzle (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes stack validKey verify =
      some (firstRound, final)) :
    ∃ beforePuzzle,
      CoreStructuralRun.run hashes (ByteLayout.program.take 423)
        (initial stack firstRound) = some beforePuzzle ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        (beforePuzzle.stack.reverse[1]?.getD [])
        (beforePuzzle.stack.reverse[0]?.getD [])
        validKey verify = some true := by
  exact CoreSourceExtraction.necessary_checks_first_puzzle
    hashes (initial stack firstRound) validKey verify
    (search_sound hashes stack validKey verify firstRound final found).2.2

/-- A returned certificate yields the same nine-position final-round shape,
actual hash-opening equations, and two fixed ALL signature obligations as the
reached-source theorem, without an externally chosen outcome list. -/
theorem search_fixed_all_calls (hashes : Hashes) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes stack validKey verify =
      some (firstRound, final)) :
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
  obtain ⟨runEq, truth, checks⟩ :=
    search_sound hashes stack validKey verify firstRound final found
  exact CoreSourceExtraction.necessary_checks_fixed_all_calls
    hashes stack (outcomes firstRound) final validKey verify
    runEq truth checks

end QSB.CoreCheckedCertificate
