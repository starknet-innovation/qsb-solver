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

theorem first_five_opcodes (lock : Lock) :
    (program lock).take 5 =
      [.push lock.pin, .over, .checksigverify, .sha256, .swap] := by
  have fixed : DynamicFullSerialized.staticOps 1 5 =
      [.over, .checksigverify, .sha256, .swap, .checksigverify] := by
    decide
  simp [program, DynamicWholeSource.fullProgram,
    DynamicFullSerialized.priorOps, DynamicFullSerialized.pinOps, fixed]

theorem first_five_split (lock : Lock) :
    (program lock).take 5 =
      (program lock).take 2 ++ [.checksigverify, .sha256, .swap] := by
  rw [first_five_opcodes, first_two_opcodes]
  rfl

/-- The exact three instructions after the pin site hash the duplicated pin
key and put that hash in the next CHECKSIGVERIFY signature slot. -/
theorem accepted_early_puzzle_from_pin_state (hashes : Hashes)
    (pin key : Bytes) (tail : List Bytes) (firstRound : Bool)
    (after : State)
    (accepted : run hashes [.checksigverify, .sha256, .swap]
      ⟨key :: pin :: key :: tail,
        CoreCheckedCertificate.outcomes firstRound, 1⟩ = some after) :
    after.stack[1]? = some (hashes.h256 key) := by
  cases tail with
  | nil =>
      have first : step hashes .checksigverify
          ⟨[key, pin, key], CoreCheckedCertificate.outcomes firstRound, 1⟩ =
          some ⟨[key], [true, true, firstRound, true, true], 2⟩ := by rfl
      have second : step hashes .sha256
          ⟨[key], [true, true, firstRound, true, true], 2⟩ =
          some ⟨[hashes.h256 key],
            [true, true, firstRound, true, true], 3⟩ := by rfl
      have third : step hashes .swap
          ⟨[hashes.h256 key],
            [true, true, firstRound, true, true], 3⟩ = none := by rfl
      simp [run, first, second, third] at accepted
  | cons puzzle rest =>
      have first : step hashes .checksigverify
          ⟨key :: pin :: key :: puzzle :: rest,
            CoreCheckedCertificate.outcomes firstRound, 1⟩ =
          some ⟨key :: puzzle :: rest,
            [true, true, firstRound, true, true], 2⟩ := by rfl
      have second : step hashes .sha256
          ⟨key :: puzzle :: rest,
            [true, true, firstRound, true, true], 2⟩ =
          some ⟨hashes.h256 key :: puzzle :: rest,
            [true, true, firstRound, true, true], 3⟩ := by rfl
      have third : step hashes .swap
          ⟨hashes.h256 key :: puzzle :: rest,
            [true, true, firstRound, true, true], 3⟩ =
          some ⟨puzzle :: hashes.h256 key :: rest,
            [true, true, firstRound, true, true], 4⟩ := by rfl
      by_cases large : rest.length + 2 > 1000
      · simp [run, first, large] at accepted
      · have shape : after =
            ⟨puzzle :: hashes.h256 key :: rest,
              [true, true, firstRound, true, true], 4⟩ := by
          simpa [run, first, second, third, large,
            show (key :: puzzle :: rest).length = rest.length + 2 by simp,
            show (hashes.h256 key :: puzzle :: rest).length =
              rest.length + 2 by simp,
            show (puzzle :: hashes.h256 key :: rest).length =
              rest.length + 2 by simp] using accepted.symm
        subst after
        rfl

theorem prior_ops_length (lock : Lock) :
    (DynamicFullSerialized.priorOps lock.pin lock.nonce0
      lock.firstCommitment).length = 446 := by
  have pushes :
      (DynamicFinalInit.commitmentPushes lock.firstCommitment).length =
        150 := by
    simpa [DynamicFinalInit.commitmentPushes] using
      DynamicFinalInit.commitmentPool_length lock.firstCommitment
  have static5 : (DynamicFullSerialized.staticOps 1 5).length = 5 := by
    decide
  have static151 : (DynamicFullSerialized.staticOps 156 151).length =
      151 := by decide
  have static138 : (DynamicFullSerialized.staticOps 308 138).length =
      138 := by decide
  simp [DynamicFullSerialized.priorOps, DynamicFullSerialized.pinOps,
    DynamicFullSerialized.firstDataOps, pushes, static5, static151,
    static138]

theorem late_verify_prefix_opcodes (lock : Lock) :
    (program lock).take 856 =
      DynamicWholeSource.beforeLateVerifyProgram
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment) lock.nonce1 lock.secondCommitment := by
  have signedLength :
      (DynamicSignedChain.dataAndSignedProgram lock.nonce1
        lock.secondCommitment).length = 393 := by
    have blocks : FinalSignedChain.allSignedBlocks.length = 91 := by
      decide
    simp [DynamicSignedChain.dataAndSignedProgram,
      DynamicFinalInit.dataOps_length, blocks]
  have bonusLength : FinalBonusSecond.bothBonusOps.length = 10 := by
    decide
  have lateLength : (ByteLatePuzzle.lateOps.take 6).length = 6 := by
    decide
  have prefixLength :
      (DynamicWholeSource.beforeLateVerifyProgram
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment) lock.nonce1
          lock.secondCommitment).length = 856 := by
    simp [DynamicWholeSource.beforeLateVerifyProgram,
      prior_ops_length lock, signedLength, bonusLength, lateLength]
  have split := DynamicWholeSource.full_program_late_verify_split
    (DynamicFullSerialized.priorOps lock.pin lock.nonce0
      lock.firstCommitment) lock.nonce1 lock.secondCommitment
  have taken := congrArg (List.take 856) split
  simpa [program, prefixLength] using taken

/-- Successful execution of the first two parameterized opcodes duplicates
the first arbitrary witness key around the lock-pushed pin signature. -/
theorem reached_pin_stack_shape (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (firstRound : Bool)
    (beforePin : CoreOpcodeStep.State)
    (reached : CoreStructuralRun.run hashes ((program lock).take 2)
      (initial stack firstRound) = some beforePin) :
    ∃ key tail, stack = key :: tail ∧
      beforePin = CoreOpcodeStep.ofByte
        ⟨key :: lock.pin :: key :: tail,
          CoreCheckedCertificate.outcomes firstRound, 1⟩ := by
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
            exact ⟨key, tail, rfl, rfl⟩

/-- The first reached CHECKSIGVERIFY always reads the pin signature pushed
by the parameterized lock, regardless of the scriptSig stack beneath it. -/
theorem reached_pin_fixed_signature (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (firstRound : Bool)
    (beforePin : CoreOpcodeStep.State)
    (reached : CoreStructuralRun.run hashes ((program lock).take 2)
      (initial stack firstRound) = some beforePin) :
    beforePin.stack.reverse[1]? = some lock.pin := by
  obtain ⟨key, tail, _stackShape, pinShape⟩ :=
    reached_pin_stack_shape hashes lock stack firstRound beforePin reached
  simp [pinShape, CoreOpcodeStep.ofByte]

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

theorem source_sites_early (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) (firstRound : Bool)
    (checked : sourceSites hashes lock stack validKey verify
      firstRound = true) :
    ∃ beforeEarly,
      CoreStructuralRun.run hashes ((program lock).take 5)
        (initial stack firstRound) = some beforeEarly ∧
      CoreChecksigEval.evalBaseVerifyAll 880 (wire lock)
        (beforeEarly.stack.reverse[1]?.getD [])
        (beforeEarly.stack.reverse[0]?.getD [])
        validKey verify = some true := by
  unfold sourceSites at checked
  cases pinEq : CoreStructuralRun.run hashes ((program lock).take 2)
      (initial stack firstRound) with
  | none => simp [pinEq] at checked
  | some beforePin =>
      cases earlyEq : CoreStructuralRun.run hashes ((program lock).take 5)
          (initial stack firstRound) with
      | none => simp [pinEq, earlyEq] at checked
      | some beforeEarly =>
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
                      exact ⟨beforeEarly, rfl, all.2.2.1⟩

theorem source_sites_late (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) (firstRound : Bool)
    (checked : sourceSites hashes lock stack validKey verify
      firstRound = true) :
    ∃ beforeLate,
      CoreStructuralRun.run hashes ((program lock).take 856)
        (initial stack firstRound) = some beforeLate ∧
      CoreChecksigEval.evalBaseVerifyAll 880 (wire lock)
        (beforeLate.stack.reverse[1]?.getD [])
        (beforeLate.stack.reverse[0]?.getD [])
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
                  | some beforeLate =>
                      have all := checked
                      simp only [pinEq, earlyEq, firstPuzzleEq,
                        firstCheckEq, lateEq,
                        Bool.and_eq_true_eq_eq_true_and_eq_true,
                        decide_eq_true_eq] at all
                      exact ⟨beforeLate, rfl, all.2.2.2.2.1⟩

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

/-- Every complete checked source run is returned by its corresponding
first-round candidate. The first CHECKMULTISIG may be either true or false. -/
theorem candidate_complete (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (runEq : CoreStructuralRun.run hashes (program lock)
      (initial stack firstRound) = some final)
    (truth : ByteMachine.finalTruth
      ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true)
    (sites : sourceSites hashes lock stack validKey verify
      firstRound = true)
    (last : finalChecked hashes lock stack validKey verify
      firstRound = true) :
    candidate hashes lock stack validKey verify firstRound =
      some final := by
  simp [candidate, runEq, truth, sites, last]

/-- Search exhausts the two possible first-round scan outcomes. An available
checked source run therefore yields some returned certificate, although the
search may select the false candidate when both candidates work. -/
theorem search_complete (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (available : ∃ firstRound final,
      CoreStructuralRun.run hashes (program lock)
        (initial stack firstRound) = some final ∧
      ByteMachine.finalTruth
        ⟨final.stack.reverse, final.outcomes, final.ops⟩ = true ∧
      sourceSites hashes lock stack validKey verify firstRound = true ∧
      finalChecked hashes lock stack validKey verify firstRound = true) :
    ∃ firstRound final,
      search hashes lock stack validKey verify =
        some (firstRound, final) := by
  obtain ⟨firstRound, final, runEq, truth, sites, last⟩ := available
  have hit := candidate_complete hashes lock stack validKey verify
    firstRound final runEq truth sites last
  cases firstRound with
  | false => exact ⟨false, final, by simp [search, hit]⟩
  | true =>
      cases other : candidate hashes lock stack validKey verify false with
      | none => exact ⟨true, final, by simp [search, other, hit]⟩
      | some otherFinal =>
          exact ⟨false, otherFinal, by simp [search, other]⟩

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

/-- The source-addressed tenth final signature is the exact nonce bytes
pushed by the parameterized lock. The arbitrary scriptSig may change earlier
stack contents, but not this reached slot on a successful certificate. -/
theorem search_final_fixed_nonce_slot (hashes : Hashes) (lock : Lock)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes lock stack validKey verify =
      some (firstRound, final)) :
    ∃ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes (beforeFinalProgram lock)
        (initial stack firstRound) = some beforeCheck ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 := by
  obtain ⟨fullRun, _truth, _sites, checked⟩ :=
    search_sound hashes lock stack validKey verify firstRound final found
  obtain ⟨beforeCheck, reached, _finalEval⟩ :=
    final_checked_sound hashes lock stack validKey verify firstRound checked
  let initialByte : State :=
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩
  obtain ⟨byteFinal, byteAccepted, _finalShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes (program lock)
      initialByte final (by simpa [initial, initialByte] using fullRun)
  obtain ⟨byteBefore, byteReached, sourceBeforeShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes (beforeFinalProgram lock)
      initialByte beforeCheck (by simpa [initial, initialByte] using reached)
  obtain ⟨modelBefore, modelReached, nonceSlot⟩ :=
    DynamicWholeSource.accepted_whole_final_nonce_slot hashes
      (DynamicFullSerialized.priorOps lock.pin lock.nonce0
        lock.firstCommitment) lock.nonce1 lock.secondCommitment
      secondWidth initialByte byteFinal
      (by simpa [program] using byteAccepted)
  have same : modelBefore = byteBefore :=
    Option.some.inj (modelReached.symm.trans
      (by simpa [beforeFinalProgram] using byteReached))
  subst modelBefore
  have topSlot : beforeCheck.stack.reverse[21]? = some lock.nonce1 := by
    rw [sourceBeforeShape]
    simpa [CoreOpcodeStep.ofByte] using nonceSlot
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp topSlot
  have enough : 13 + 9 ≤ beforeCheck.stack.reverse.length := by omega
  refine ⟨beforeCheck, reached, ?_⟩
  calc
    CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        CoreMultisigStack.signatureAt
          (beforeCheck.stack.reverse).reverse 10 9 := by simp
    _ = beforeCheck.stack.reverse[12 + 9]? :=
      CoreMultisigStack.final_signature_slot
        beforeCheck.stack.reverse 9 enough
    _ = some lock.nonce1 := by simpa using topSlot

/-- The reached late CHECKSIGVERIFY gates `H` of the same key used by the
tenth final CHECKMULTISIG pair. A successful source-site certificate forces
that hash to be strict DER. The hash and verifier remain supplied functions;
compiled-Core acceptance is not inferred. -/
theorem search_late_puzzle_final_key_der (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes lock stack validKey verify =
      some (firstRound, final)) :
    ∃ (key : Bytes) (beforeLate beforeCheck : CoreOpcodeStep.State),
      CoreStructuralRun.run hashes ((program lock).take 856)
        (initial stack firstRound) = some beforeLate ∧
      CoreStructuralRun.run hashes (beforeFinalProgram lock)
        (initial stack firstRound) = some beforeCheck ∧
      beforeLate.stack.reverse[1]? = some (hashes.h256 key) ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some key ∧
      DERSyntax.valid (hashes.h256 key) = true := by
  obtain ⟨fullRun, _truth, sites, checked⟩ :=
    search_sound hashes lock stack validKey verify firstRound final found
  obtain ⟨beforeLate, lateReached, lateChecked⟩ :=
    source_sites_late hashes lock stack validKey verify firstRound sites
  obtain ⟨beforeCheck, checkReached, _finalEval⟩ :=
    final_checked_sound hashes lock stack validKey verify firstRound checked
  let initialByte : State :=
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩
  obtain ⟨byteFinal, byteAccepted, _finalShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes (program lock)
      initialByte final (by simpa [initial, initialByte] using fullRun)
  obtain ⟨byteLate, byteLateReached, lateShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes ((program lock).take 856)
      initialByte beforeLate (by simpa [initial, initialByte] using lateReached)
  obtain ⟨byteCheck, byteCheckReached, checkShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes (beforeFinalProgram lock)
      initialByte beforeCheck (by simpa [initial, initialByte] using checkReached)
  obtain ⟨key, modelLate, modelCheck, modelLateReached,
    modelCheckReached, sigAt, keyAt⟩ :=
    DynamicWholeSource.accepted_whole_late_puzzle_final_key hashes
      (DynamicFullSerialized.priorOps lock.pin lock.nonce0
        lock.firstCommitment) lock.nonce1 lock.secondCommitment
      initialByte byteFinal (by simpa [program] using byteAccepted)
  have lateSame : modelLate = byteLate :=
    Option.some.inj (modelLateReached.symm.trans
      (by simpa [late_verify_prefix_opcodes lock] using byteLateReached))
  have checkSame : modelCheck = byteCheck :=
    Option.some.inj (modelCheckReached.symm.trans
      (by simpa [beforeFinalProgram] using byteCheckReached))
  subst modelLate
  subst modelCheck
  have sourceSig : beforeLate.stack.reverse[1]? =
      some (hashes.h256 key) := by
    rw [lateShape]
    simpa [CoreOpcodeStep.ofByte] using sigAt
  have sourceKey : beforeCheck.stack.reverse[10]? = some key := by
    rw [checkShape]
    simpa [CoreOpcodeStep.ofByte] using keyAt
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp sourceKey
  have keyBound : 2 + 9 ≤ beforeCheck.stack.reverse.length := by omega
  have finalKey : CoreMultisigStack.keyAt beforeCheck.stack 9 =
      some key := by
    calc
      CoreMultisigStack.keyAt beforeCheck.stack 9 =
          CoreMultisigStack.keyAt
            (beforeCheck.stack.reverse).reverse 9 := by simp
      _ = beforeCheck.stack.reverse[1 + 9]? :=
        CoreMultisigStack.keyAt_reverse
          beforeCheck.stack.reverse 9 keyBound
      _ = some key := by simpa using sourceKey
  have actualSig : beforeLate.stack.reverse[1]?.getD [] =
      hashes.h256 key := by simp [sourceSig]
  rw [actualSig] at lateChecked
  obtain ⟨_hashType, _last, der, _keyValid, _verified⟩ :=
    CoreChecksigEval.successful_base_check 880 (wire lock)
      (hashes.h256 key) (beforeLate.stack.reverse[0]?.getD [])
      validKey verify lateChecked
  exact ⟨key, beforeLate, beforeCheck, lateReached, checkReached,
    sourceSig, finalKey, der⟩

/-- The early puzzle gates `H` of the exact reached pinning key. Its
CHECKSIGVERIFY source-site success forces those hash bytes to be strict DER.
The pin key originates in the arbitrary initial witness stack. -/
theorem search_early_puzzle_pin_key_der (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes lock stack validKey verify =
      some (firstRound, final)) :
    ∃ (key : Bytes) (beforePin beforeEarly : CoreOpcodeStep.State),
      CoreStructuralRun.run hashes ((program lock).take 2)
        (initial stack firstRound) = some beforePin ∧
      CoreStructuralRun.run hashes ((program lock).take 5)
        (initial stack firstRound) = some beforeEarly ∧
      beforePin.stack.reverse[0]? = some key ∧
      beforeEarly.stack.reverse[1]? = some (hashes.h256 key) ∧
      DERSyntax.valid (hashes.h256 key) = true := by
  obtain ⟨_fullRun, _truth, sites, _checked⟩ :=
    search_sound hashes lock stack validKey verify firstRound final found
  obtain ⟨beforePin, pinReached, _pinChecked⟩ :=
    source_sites_pin hashes lock stack validKey verify firstRound sites
  obtain ⟨beforeEarly, earlyReached, earlyChecked⟩ :=
    source_sites_early hashes lock stack validKey verify firstRound sites
  obtain ⟨key, tail, _stackShape, pinShape⟩ :=
    reached_pin_stack_shape hashes lock stack firstRound beforePin pinReached
  have suffixRun : CoreStructuralRun.run hashes
      [.checksigverify, .sha256, .swap] beforePin =
        some beforeEarly := by
    rw [first_five_split, CoreStructuralRun.run_append,
      pinReached] at earlyReached
    simpa using earlyReached
  obtain ⟨byteEarly, byteEarlyRun, earlyShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes
      [.checksigverify, .sha256, .swap]
      ⟨key :: lock.pin :: key :: tail,
        CoreCheckedCertificate.outcomes firstRound, 1⟩
      beforeEarly (by simpa [pinShape] using suffixRun)
  have byteSig := accepted_early_puzzle_from_pin_state
    hashes lock.pin key tail firstRound byteEarly byteEarlyRun
  have sourceSig : beforeEarly.stack.reverse[1]? =
      some (hashes.h256 key) := by
    rw [earlyShape]
    simpa [CoreOpcodeStep.ofByte] using byteSig
  have pinKey : beforePin.stack.reverse[0]? = some key := by
    simp [pinShape, CoreOpcodeStep.ofByte]
  have actualSig : beforeEarly.stack.reverse[1]?.getD [] =
      hashes.h256 key := by simp [sourceSig]
  rw [actualSig] at earlyChecked
  obtain ⟨_hashType, _last, der, _keyValid, _verified⟩ :=
    CoreChecksigEval.successful_base_check 880 (wire lock)
      (hashes.h256 key) (beforeEarly.stack.reverse[0]?.getD [])
      validKey verify earlyChecked
  exact ⟨key, beforePin, beforeEarly, pinReached, earlyReached,
    pinKey, sourceSig, der⟩

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

/-- A good-setup certificate fixes the actual first nine signature cells at
the reached source-shaped final CHECKMULTISIG. The seven trace-derived cells
are kept in their scan order; the tenth cell is handled separately by
`search_final_fixed_nonce_slot`. -/
theorem search_good_setup_reached_final_slots (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes lock stack validKey verify =
      some (firstRound, final))
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : CoreOpcodeStep.State),
      CoreStructuralRun.run hashes (beforeFinalProgram lock)
        (initial stack firstRound) = some beforeCheck ∧
      beforeCheck.stack.reverse[12]? =
        some (FinalSignedLoop.generatedDummyAt b) ∧
      beforeCheck.stack.reverse[13]? =
        some (FinalSignedLoop.generatedDummyAt a) ∧
      (∀ j : Nat, j < 7 → beforeCheck.stack.reverse[j + 14]? =
        (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?) ∧
      beforeCheck.stack.reverse[21]? = some lock.nonce1 ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      DynamicWholeSource.extractTrace hashes
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment)
        ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          some trace := by
  obtain ⟨fullRun, _truth, _sites, checked⟩ :=
    search_sound hashes lock stack validKey verify firstRound final found
  obtain ⟨beforeCheck, reached, finalEval⟩ :=
    final_checked_sound hashes lock stack validKey verify firstRound checked
  let initialByte : State :=
    ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩
  obtain ⟨byteFinal, byteAccepted, _finalShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes (program lock)
      initialByte final (by simpa [initial, initialByte] using fullRun)
  obtain ⟨byteBefore, byteReached, sourceBeforeShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes (beforeFinalProgram lock)
      initialByte beforeCheck (by simpa [initial, initialByte] using reached)
  have byteEval : ∀ before : State,
      run hashes (beforeFinalProgram lock) initialByte = some before →
      CoreMultisigEval.finalTenEval (wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        before.stack = some true := by
    intro before h
    have same : before = byteBefore :=
      Option.some.inj (h.symm.trans byteReached)
    subst before
    simpa [sourceBeforeShape, CoreOpcodeStep.ofByte] using finalEval
  obtain ⟨trace, a, b, modelBefore, modelReached, slotB, slotA,
    signed, nonceSlot, seven, hits, distinct, extracted⟩ :=
    DynamicWholeSource.accepted_whole_good_setup_nine_reached_slots
      hashes
      (DynamicFullSerialized.priorOps lock.pin lock.nonce0
        lock.firstCommitment) lock.nonce1 lock.secondCommitment
      secondWidth initialByte byteFinal
      (by simpa [program] using byteAccepted)
      (wire lock) (CoreFinalChecksigEval.checker validKey verify)
      (by simpa [beforeFinalProgram] using byteEval) noCommitmentDER
  have same : modelBefore = byteBefore :=
    Option.some.inj (modelReached.symm.trans
      (by simpa [beforeFinalProgram] using byteReached))
  subst modelBefore
  have sourceB : beforeCheck.stack.reverse[12]? =
      some (FinalSignedLoop.generatedDummyAt b) := by
    rw [sourceBeforeShape]
    simpa [CoreOpcodeStep.ofByte] using slotB
  have sourceA : beforeCheck.stack.reverse[13]? =
      some (FinalSignedLoop.generatedDummyAt a) := by
    rw [sourceBeforeShape]
    simpa [CoreOpcodeStep.ofByte] using slotA
  have sourceSigned : ∀ j : Nat, j < 7 →
      beforeCheck.stack.reverse[j + 14]? =
        (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]? := by
    intro j within
    rw [sourceBeforeShape]
    simpa [CoreOpcodeStep.ofByte] using signed j within
  have sourceNonce : beforeCheck.stack.reverse[21]? = some lock.nonce1 := by
    rw [sourceBeforeShape]
    simpa [CoreOpcodeStep.ofByte] using nonceSlot
  exact ⟨trace, a, b, beforeCheck, reached, sourceB, sourceA,
    sourceSigned, sourceNonce, seven, hits, distinct, extracted⟩

/-- On a good setup, all nine source-addressed signature bytes before the
fixed final nonce are generated `SIGHASH_SINGLE` dummies. This identifies
the actual cells read by the final ten-pair scan, not merely nine selected
commitment indices. -/
theorem search_good_setup_nine_dummy_signatures (hashes : Hashes) (lock : Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : search hashes lock stack validKey verify =
      some (firstRound, final))
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false) :
    ∃ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes (beforeFinalProgram lock)
        (initial stack firstRound) = some beforeCheck ∧
      ∀ j : Fin 9, ∃ id : Fin 150,
        CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val =
          some (FinalSignedLoop.generatedDummyAt id) := by
  obtain ⟨trace, a, b, beforeCheck, reached, slotB, slotA,
    signed, nonceSlot, seven, _hits, _distinct, _extracted⟩ :=
    search_good_setup_reached_final_slots hashes lock stack validKey verify
      firstRound final found secondWidth noCommitmentDER
  have enough : 22 ≤ beforeCheck.stack.reverse.length := by
    obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp nonceSlot
    omega
  refine ⟨beforeCheck, reached, ?_⟩
  intro j
  have address : CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val =
      beforeCheck.stack.reverse[12 + j.val]? := by
    simpa using CoreMultisigStack.final_signature_slot
      beforeCheck.stack.reverse j.val (by omega)
  by_cases zero : j.val = 0
  · exact ⟨b, address.trans (by simpa [zero] using slotB)⟩
  by_cases one : j.val = 1
  · exact ⟨a, address.trans (by simpa [one] using slotA)⟩
  let k := j.val - 2
  have kBound : k < 7 := by dsimp [k]; omega
  let ids := (trace.map Prod.fst).reverse
  have idsLength : ids.length = 7 := by simp [ids, seven]
  have kWithin : k < ids.length := by omega
  have mapEq :
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse =
        ids.map FinalSignedLoop.generatedDummyAt := by
    simp [ids, List.map_reverse, List.map_map]
  have dummyAt :
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[k]? =
        some (FinalSignedLoop.generatedDummyAt ids[k]) := by
    rw [mapEq]
    simp [kWithin]
  refine ⟨ids[k], ?_⟩
  calc
    CoreMultisigStack.signatureAt beforeCheck.stack 10 j.val =
        beforeCheck.stack.reverse[12 + j.val]? := address
    _ = beforeCheck.stack.reverse[k + 14]? := by congr 1; dsimp [k]; omega
    _ = (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[k]? :=
          signed k kBound
    _ = some (FinalSignedLoop.generatedDummyAt ids[k]) := dummyAt

end QSB.DynamicCheckedCertificate
