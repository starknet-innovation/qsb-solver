import QSB.DynamicFullSerialized
import QSB.CoreCheckedCertificate

/-!
Executable source-shaped certificate for the complete parameterized Config A
lock. It tries both possible first-round multisignature results, checks the
reached source-shaped signature sites, and accepts only a truthy structural
run. The hash functions, key parser, and ECDSA/sighash verifier are inputs;
compiled Bitcoin Core acceptance is not established here.
-/
namespace QSB.DynamicCheckedCertificate
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

structure Lock where
  pin : Bytes
  nonce0 : Bytes
  nonce1 : Bytes
  firstCommitment : Fin 150 → Bytes
  secondCommitment : Fin 150 → Bytes

def wire (lock : Lock) : Bytes :=
  DynamicFullSerialized.fullWire lock.pin lock.nonce0 lock.nonce1
    lock.firstCommitment lock.secondCommitment

def program (lock : Lock) : List Op :=
  DynamicWholeSource.fullProgram
    (DynamicFullSerialized.priorOps lock.pin lock.nonce0
      lock.firstCommitment) lock.nonce1 lock.secondCommitment

def beforeFinalProgram (lock : Lock) : List Op :=
  DynamicWholeSource.beforeFinalCheckProgram
    (DynamicFullSerialized.priorOps lock.pin lock.nonce0
      lock.firstCommitment) lock.nonce1 lock.secondCommitment

def initial (stack : List Bytes) (firstRound : Bool) :
    CoreOpcodeStep.State :=
  CoreOpcodeStep.ofByte
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩

theorem first_two_opcodes (lock : Lock) :
    (program lock).take 2 = [.push lock.pin, .over] := by
  have fixed : DynamicFullSerialized.staticOps 1 5 =
      [.over, .checksigverify, .sha256, .swap, .checksigverify] := by
    decide
  simp [program, DynamicWholeSource.fullProgram,
    DynamicFullSerialized.priorOps, DynamicFullSerialized.pinOps, fixed]

/-- The first reached CHECKSIGVERIFY always reads the pin signature pushed
by the parameterized lock, regardless of the scriptSig stack beneath it. -/
theorem reached_pin_fixed_signature (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (firstRound : Bool)
    (beforePin : CoreOpcodeStep.State)
    (reached : CoreStructuralRun.run hashes ((program lock).take 2)
      (initial stack firstRound) = some beforePin) :
    beforePin.stack.reverse[1]? = some lock.pin := by
  obtain ⟨byteAfter, byteRun, shape⟩ :=
    CoreStructuralRun.run_refines_byte hashes ((program lock).take 2)
      ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ beforePin
      (by simpa [initial] using reached)
  subst beforePin
  rw [first_two_opcodes] at byteRun
  cases stack with
  | nil =>
      have pushStep : ByteMachine.step hashes (.push lock.pin)
          ⟨[], CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          if lock.pin.length > 520 then none else
            some ⟨[lock.pin], CoreCheckedCertificate.outcomes firstRound,
              0⟩ := by rfl
      have overStep : ByteMachine.step hashes .over
          ⟨[lock.pin], CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          none := by rfl
      by_cases long : lock.pin.length > 520
      · simp [ByteMachine.run, pushStep, long] at byteRun
      · simp [ByteMachine.run, pushStep, overStep, long] at byteRun
  | cons key tail =>
      have pushStep : ByteMachine.step hashes (.push lock.pin)
          ⟨key :: tail, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          if lock.pin.length > 520 then none else
            some ⟨lock.pin :: key :: tail,
              CoreCheckedCertificate.outcomes firstRound, 0⟩ := by rfl
      have overStep : ByteMachine.step hashes .over
          ⟨lock.pin :: key :: tail,
            CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          some ⟨key :: lock.pin :: key :: tail,
            CoreCheckedCertificate.outcomes firstRound, 1⟩ := by rfl
      by_cases long : lock.pin.length > 520
      · simp [ByteMachine.run, pushStep, long] at byteRun
      · by_cases cap1 : tail.length + 2 > 1000
        · simp [ByteMachine.run, pushStep, long, cap1] at byteRun
        · by_cases cap2 : tail.length + 3 > 1000
          · simp [ByteMachine.run, pushStep, overStep,
              long, cap1, cap2] at byteRun
          · have same : byteAfter =
                ⟨key :: lock.pin :: key :: tail,
                  CoreCheckedCertificate.outcomes firstRound, 1⟩ := by
              simpa [ByteMachine.run, pushStep, overStep,
                long, cap1, cap2] using byteRun.symm
            subst byteAfter
            simp [CoreOpcodeStep.ofByte]

/-- Check that the six signature sites retain their Config A opcode roles
despite parameterized data bytes. The individual source evaluators below are
then run on the stacks reached just before those opcode positions. -/
def siteOpcodes (lock : Lock) : Bool :=
  decide ((program lock)[2]? = some .checksigverify ∧
    (program lock)[5]? = some .checksigverify ∧
    (program lock)[423]? = some .checksigverify ∧
    (program lock)[446]? = some .checkmultisig ∧
    (program lock)[856]? = some .checksigverify ∧
    (program lock)[879]? = some .checkmultisig)

def sourceSites (hashes : Hashes) (lock : Lock) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) : Bool :=
  match CoreStructuralRun.run hashes ((program lock).take 2)
      (initial stack firstRound),
      CoreStructuralRun.run hashes ((program lock).take 5)
        (initial stack firstRound),
      CoreStructuralRun.run hashes ((program lock).take 423)
        (initial stack firstRound),
      CoreStructuralRun.run hashes ((program lock).take 446)
        (initial stack firstRound),
      CoreStructuralRun.run hashes ((program lock).take 856)
        (initial stack firstRound) with
  | some pin, some early, some firstPuzzle, some firstCheck, some late =>
      siteOpcodes lock &&
      decide (
        CoreChecksigEval.evalBaseVerifyAll 880 (wire lock)
          (pin.stack.reverse[1]?.getD [])
          (pin.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreChecksigEval.evalBaseVerifyAll 880 (wire lock)
          (early.stack.reverse[1]?.getD [])
          (early.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreChecksigEval.evalBaseVerifyAll 880 (wire lock)
          (firstPuzzle.stack.reverse[1]?.getD [])
          (firstPuzzle.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreChecksigEval.evalBaseVerifyAll 880 (wire lock)
          (late.stack.reverse[1]?.getD [])
          (late.stack.reverse[0]?.getD [])
          validKey verify = some true ∧
        CoreMultisigSourceScan.scanAtStack (wire lock)
          (CoreFinalChecksigEval.checker validKey verify)
          firstCheck.stack = some firstRound)
  | _, _, _, _, _ => false

/-- A successful parameterized source-site check includes the actual reached
pinning CHECKSIGVERIFY pair, even when the first multisignature later returns
false. This is still a source-model check, not compiled-Core acceptance. -/
theorem source_sites_pin (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) (firstRound : Bool)
    (checked : sourceSites hashes lock stack validKey verify
      firstRound = true) :
    ∃ beforePin,
      CoreStructuralRun.run hashes ((program lock).take 2)
        (initial stack firstRound) = some beforePin ∧
      CoreChecksigEval.evalBaseVerifyAll 880 (wire lock)
        (beforePin.stack.reverse[1]?.getD [])
        (beforePin.stack.reverse[0]?.getD [])
        validKey verify = some true := by
  unfold sourceSites at checked
  cases pinEq : CoreStructuralRun.run hashes ((program lock).take 2)
      (initial stack firstRound) with
  | none => simp [pinEq] at checked
  | some beforePin =>
      cases earlyEq : CoreStructuralRun.run hashes ((program lock).take 5)
          (initial stack firstRound) with
      | none => simp [pinEq, earlyEq] at checked
      | some early =>
          cases firstPuzzleEq : CoreStructuralRun.run hashes
              ((program lock).take 423) (initial stack firstRound) with
          | none => simp [pinEq, earlyEq, firstPuzzleEq] at checked
          | some firstPuzzle =>
              cases firstCheckEq : CoreStructuralRun.run hashes
                  ((program lock).take 446)
                  (initial stack firstRound) with
              | none =>
                  simp [pinEq, earlyEq, firstPuzzleEq, firstCheckEq] at checked
              | some firstCheck =>
                  cases lateEq : CoreStructuralRun.run hashes
                      ((program lock).take 856)
                      (initial stack firstRound) with
                  | none =>
                      simp [pinEq, earlyEq, firstPuzzleEq,
                        firstCheckEq, lateEq] at checked
                  | some late =>
                      have all := checked
                      simp only [pinEq, earlyEq, firstPuzzleEq,
                        firstCheckEq, lateEq,
                        Bool.and_eq_true_eq_eq_true_and_eq_true,
                        decide_eq_true_eq] at all
                      exact ⟨beforePin, rfl, all.2.1⟩

/-- The final source evaluator is checked on the very stack reached by the
same structural prefix that precedes the final CHECKMULTISIG. -/
def finalChecked (hashes : Hashes) (lock : Lock) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) : Bool :=
  match CoreStructuralRun.run hashes (beforeFinalProgram lock)
      (initial stack firstRound) with
  | none => false
  | some beforeCheck =>
      decide (CoreMultisigEval.finalTenEval (wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        beforeCheck.stack.reverse = some true)

theorem final_checked_sound (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) (firstRound : Bool)
    (checked : finalChecked hashes lock stack validKey verify
      firstRound = true) :
    ∃ beforeCheck,
      CoreStructuralRun.run hashes (beforeFinalProgram lock)
        (initial stack firstRound) = some beforeCheck ∧
      CoreMultisigEval.finalTenEval (wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        beforeCheck.stack.reverse = some true := by
  unfold finalChecked at checked
  cases reached : CoreStructuralRun.run hashes (beforeFinalProgram lock)
      (initial stack firstRound) with
  | none => simp [reached] at checked
  | some beforeCheck =>
      have finalEval : CoreMultisigEval.finalTenEval (wire lock)
          (CoreFinalChecksigEval.checker validKey verify)
          beforeCheck.stack.reverse = some true := by
        simpa [reached] using checked
      exact ⟨beforeCheck, rfl, finalEval⟩

def candidate (hashes : Hashes) (lock : Lock) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) : Option CoreOpcodeStep.State := do
  let final ← CoreStructuralRun.run hashes (program lock)
    (initial stack firstRound)
  if ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ &&
      sourceSites hashes lock stack validKey verify firstRound &&
      finalChecked hashes lock stack validKey verify firstRound then
    some final
  else none

def search (hashes : Hashes) (lock : Lock) (stack : List Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA) :
    Option (Bool × CoreOpcodeStep.State) :=
  match candidate hashes lock stack validKey verify false with
  | some final => some (false, final)
  | none =>
      match candidate hashes lock stack validKey verify true with
      | some final => some (true, final)
      | none => none

theorem candidate_sound (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : candidate hashes lock stack validKey verify firstRound =
      some final) :
    CoreStructuralRun.run hashes (program lock)
      (initial stack firstRound) = some final ∧
    ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true ∧
    sourceSites hashes lock stack validKey verify firstRound = true ∧
    finalChecked hashes lock stack validKey verify firstRound = true := by
  unfold candidate at found
  cases runEq : CoreStructuralRun.run hashes (program lock)
      (initial stack firstRound) with
  | none => simp [runEq] at found
  | some reached =>
      simp [runEq] at found
      have conditions := found.1
      have same := found.2
      subst reached
      exact ⟨rfl, conditions.1.1, conditions.1.2,
        conditions.2⟩

theorem search_sound (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes lock stack validKey verify =
      some (firstRound, final)) :
    CoreStructuralRun.run hashes (program lock)
      (initial stack firstRound) = some final ∧
    ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true ∧
    sourceSites hashes lock stack validKey verify firstRound = true ∧
    finalChecked hashes lock stack validKey verify firstRound = true := by
  unfold search at found
  cases falseResult : candidate hashes lock stack validKey verify false with
  | some reached =>
      simp [falseResult] at found
      rcases found with ⟨rfl, rfl⟩
      exact candidate_sound hashes lock stack validKey verify false reached
        falseResult
  | none =>
      cases trueResult : candidate hashes lock stack validKey verify true with
      | none => simp [falseResult, trueResult] at found
      | some reached =>
          simp [falseResult, trueResult] at found
          rcases found with ⟨rfl, rfl⟩
          exact candidate_sound hashes lock stack validKey verify true reached
            trueResult

/-- A returned certificate yields the checked nine-position shape for the
complete parameterized Lean serialization. Its source-level ECDSA verifier
still needs exact transaction/Core refinement, and no QROM bound follows. -/
theorem search_good_setup_nine_positions (hashes : Hashes) (lock : Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes lock stack validKey verify =
      some (firstRound, final))
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      DynamicWholeSource.extractTrace hashes
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment)
        ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  obtain ⟨runEq, _truth, _sites, checked⟩ :=
    search_sound hashes lock stack validKey verify firstRound final found
  obtain ⟨beforeCheck, reached, finalEval⟩ :=
    final_checked_sound hashes lock stack validKey verify firstRound checked
  let initialByte : State :=
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩
  have sourceEval : ∀ before : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes
        (DynamicWholeSource.beforeFinalCheckProgram
          (DynamicFullSerialized.priorOps lock.pin lock.nonce0
            lock.firstCommitment) lock.nonce1 lock.secondCommitment)
        (CoreOpcodeStep.ofByte initialByte) = some before →
      CoreMultisigEval.finalTenEval (wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        before.stack.reverse = some true := by
    intro before h
    have same : before = beforeCheck :=
      Option.some.inj (h.symm.trans reached)
    subst before
    exact finalEval
  have parsed := DynamicFullSerialized.full_wire_decodes
    lock.pin lock.nonce0 lock.nonce1
    lock.firstCommitment lock.secondCommitment firstWidth secondWidth
    pinShort nonce0Short nonce1Short
  exact DynamicFullSerialized.accepted_full_structural_good_setup_nine_positions
    hashes lock.pin lock.nonce0 lock.nonce1
    lock.firstCommitment lock.secondCommitment firstWidth secondWidth
    pinShort nonce0Short nonce1Short initialByte final (program lock)
    parsed runEq (CoreFinalChecksigEval.checker validKey verify)
    sourceEval noCommitmentDER

end QSB.DynamicCheckedCertificate
