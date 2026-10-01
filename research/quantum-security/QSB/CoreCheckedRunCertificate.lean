import QSB.CoreCheckedStep
import QSB.CoreCheckedCertificate

/-!
Bridge from a successful checker-derived literal run to the existing
six-site source certificate. This remains a relation between Lean models:
the key parser, transaction digest, ECDSA checker, and compiled Bitcoin Core
interpreter are not implemented or refined here.
-/
namespace QSB.CoreCheckedRunCertificate
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

private theorem successful_prefix (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (before after : List Op) (initial final : CoreCheckedStep.State)
    (records : List Bool)
    (success : CoreCheckedStep.run hashes script validKey verify
      (before ++ after) initial = some (final, records)) :
    ∃ middle first later,
      CoreCheckedStep.run hashes script validKey verify before initial =
        some (middle, first) ∧
      CoreCheckedStep.run hashes script validKey verify after middle =
        some (final, later) ∧
      records = first ++ later := by
  rw [CoreCheckedStep.run_append] at success
  cases hbefore : CoreCheckedStep.run hashes script validKey verify
      before initial with
  | none => simp [hbefore] at success
  | some pair =>
      obtain ⟨middle, first⟩ := pair
      cases hafter : CoreCheckedStep.run hashes script validKey verify
          after middle with
      | none => simp [hbefore, hafter] at success
      | some pair =>
          obtain ⟨reached, later⟩ := pair
          have output : (final, records) =
              (reached, first ++ later) := by
            simpa [hbefore, hafter] using success.symm
          have finalEq := (Prod.mk.inj output).1
          have recordsEq := (Prod.mk.inj output).2
          subst reached
          exact ⟨middle, first, later, rfl, hafter, recordsEq⟩

private theorem successful_cons (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (op : Op) (rest : List Op)
    (s final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes script validKey verify
      (op :: rest) s = some (final, records)) :
    ∃ next record later,
      CoreCheckedStep.step hashes script validKey verify op s =
        some (next, record) ∧
      next.stack.length ≤ 1000 ∧
      CoreCheckedStep.run hashes script validKey verify rest next =
        some (final, later) ∧
      records = record.toList ++ later := by
  simp only [CoreCheckedStep.run] at success
  cases hstep : CoreCheckedStep.step hashes script validKey verify op s with
  | none => simp [hstep] at success
  | some pair =>
      obtain ⟨next, record⟩ := pair
      by_cases large : next.stack.length > 1000
      · simp [hstep, large] at success
      · cases hrest : CoreCheckedStep.run hashes script validKey verify
            rest next with
        | none => simp [hstep, large, hrest] at success
        | some pair =>
            obtain ⟨reached, later⟩ := pair
            have output : (final, records) =
                (reached, record.toList ++ later) := by
              simpa [hstep, large, hrest] using success.symm
            have finalEq := (Prod.mk.inj output).1
            have recordsEq := (Prod.mk.inj output).2
            subst reached
            exact ⟨next, record, later, rfl, by omega,
              hrest, recordsEq⟩

/-- A successful checked run exposes the actual source-shaped checker result
at any reached CHECKSIGVERIFY site, and the structural prefix has the same
reached stack with the computed future outcomes. -/
theorem reached_checksig_site (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (before after : List Op)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes script validKey verify
      (before ++ .checksigverify :: after) initial =
        some (final, records)) :
    ∃ sourceBefore : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes before
        (CoreCheckedStep.lift initial records) = some sourceBefore ∧
      CoreChecksigEval.evalBaseVerifyAll 880 script
        (sourceBefore.stack.reverse[1]?.getD [])
        (sourceBefore.stack.reverse[0]?.getD [])
        validKey verify = some true ∧
      records[CoreCheckedStep.signatureSites before]? = some true := by
  obtain ⟨middle, first, later, hbefore, hafter, recordEq⟩ :=
    successful_prefix hashes script validKey verify before
      (.checksigverify :: after) initial final records success
  obtain ⟨next, record, restRecords, hstep, _, _, laterEq⟩ :=
    successful_cons hashes script validKey verify
      .checksigverify after middle final later hafter
  cases hcheck : CoreCheckedStep.checkedChecksig script validKey verify
      middle with
  | none => simp [CoreCheckedStep.step, hcheck] at hstep
  | some checkedNext =>
      have result : (next, record) = (checkedNext, some true) := by
        simpa [CoreCheckedStep.step, hcheck] using hstep.symm
      have nextEq := (Prod.mk.inj result).1
      have recordEq' := (Prod.mk.inj result).2
      subst next
      subst record
      have remaining : later = true :: restRecords := by
        simpa using laterEq
      have structural := CoreCheckedStep.checked_run_frames
        hashes script validKey verify before initial middle first
        (true :: restRecords) hbefore
      have sourcePrefix : CoreStructuralRun.run hashes before
          (CoreCheckedStep.lift initial records) =
            some (CoreCheckedStep.lift middle (true :: restRecords)) := by
        rw [recordEq, remaining]
        exact structural
      obtain ⟨sig, key, keyAt, sigAt, coreChecked, _⟩ :=
        CoreCheckedStep.checkedChecksig_sound script validKey verify
          middle checkedNext hcheck
      have direct : CoreChecksigEval.evalBaseVerifyAll 880 script
          sig key validKey verify = some true := by
        rw [CoreChecksigEval.evalBaseVerifyAll_eq_core]
        exact coreChecked
      have firstLength := CoreCheckedStep.run_record_length hashes script
        validKey verify before initial middle first hbefore
      have recordAt : records[first.length]? = some true := by
        rw [recordEq, remaining]
        simp
      refine ⟨CoreCheckedStep.lift middle (true :: restRecords),
        sourcePrefix, ?_, ?_⟩
      · simpa [CoreCheckedStep.lift, keyAt, sigAt] using direct
      · simpa [firstLength] using recordAt

/-- A reached CHECKMULTISIG site's recorded Boolean equals the actual
source-shaped count, deletion, encoding, and ordered key-scan result. The
Boolean may be false when this opcode is not enforcing. -/
theorem reached_multisig_site (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (before after : List Op)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes script validKey verify
      (before ++ .checkmultisig :: after) initial =
        some (final, records)) :
    ∃ (sourceBefore : CoreOpcodeStep.State) (actual : Bool),
      CoreStructuralRun.run hashes before
        (CoreCheckedStep.lift initial records) = some sourceBefore ∧
      CoreMultisigSourceScan.scanAtStack script
        (CoreFinalChecksigEval.checker validKey verify)
        sourceBefore.stack = some actual ∧
      sourceBefore.outcomes.head? = some actual ∧
      records[CoreCheckedStep.signatureSites before]? = some actual := by
  obtain ⟨middle, first, later, hbefore, hafter, recordEq⟩ :=
    successful_prefix hashes script validKey verify before
      (.checkmultisig :: after) initial final records success
  obtain ⟨next, record, restRecords, hstep, _, _, laterEq⟩ :=
    successful_cons hashes script validKey verify
      .checkmultisig after middle final later hafter
  cases hcheck : CoreCheckedStep.checkedMultisig script validKey verify
      middle with
  | none => simp [CoreCheckedStep.step, hcheck] at hstep
  | some pair =>
      obtain ⟨checkedNext, result⟩ := pair
      have output : (next, record) =
          (checkedNext, some result) := by
        simpa [CoreCheckedStep.step, hcheck] using hstep.symm
      have nextEq := (Prod.mk.inj output).1
      have recordEq' := (Prod.mk.inj output).2
      subst next
      subst record
      have remaining : later = result :: restRecords := by
        simpa using laterEq
      have structural := CoreCheckedStep.checked_run_frames
        hashes script validKey verify before initial middle first
        (result :: restRecords) hbefore
      have sourcePrefix : CoreStructuralRun.run hashes before
          (CoreCheckedStep.lift initial records) =
            some (CoreCheckedStep.lift middle
              (result :: restRecords)) := by
        rw [recordEq, remaining]
        exact structural
      have scanned := (CoreCheckedStep.checkedMultisig_sound
        script validKey verify middle checkedNext result hcheck).1
      have firstLength := CoreCheckedStep.run_record_length hashes script
        validKey verify before initial middle first hbefore
      have recordAt : records[first.length]? = some result := by
        rw [recordEq, remaining]
        simp
      exact ⟨CoreCheckedStep.lift middle (result :: restRecords),
        result, sourcePrefix, scanned, by simp [CoreCheckedStep.lift],
        by simpa [firstLength] using recordAt⟩

private theorem literal_checksig_at (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (k : Nat)
    (site : ByteLayout.program = ByteLayout.program.take k ++
      .checksigverify :: ByteLayout.program.drop (k + 1))
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program initial =
        some (final, records)) :
    ∃ sourceBefore : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes (ByteLayout.program.take k)
        (CoreCheckedStep.lift initial records) = some sourceBefore ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        (sourceBefore.stack.reverse[1]?.getD [])
        (sourceBefore.stack.reverse[0]?.getD [])
        validKey verify = some true ∧
      records[CoreCheckedStep.signatureSites
        (ByteLayout.program.take k)]? = some true := by
  rw [site] at success
  simpa [PinPuzzleScriptCode.literalScript] using
    reached_checksig_site hashes EncodedLayout.chunks.flatten
      validKey verify (ByteLayout.program.take k)
      (ByteLayout.program.drop (k + 1)) initial final records success

private theorem literal_first_scan (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program initial =
        some (final, records)) :
    ∃ (sourceBefore : CoreOpcodeStep.State) (actual : Bool),
      CoreStructuralRun.run hashes (ByteLayout.program.take 446)
        (CoreCheckedStep.lift initial records) = some sourceBefore ∧
      CoreMultisigSourceScan.scanAtStack EncodedLayout.chunks.flatten
        (CoreFinalChecksigEval.checker validKey verify)
        sourceBefore.stack = some actual ∧
      sourceBefore.outcomes.head? = some actual ∧
      records[3]? = some actual := by
  have site : ByteLayout.program = ByteLayout.program.take 446 ++
      .checkmultisig :: ByteLayout.program.drop 447 := by decide
  rw [site] at success
  have reached := reached_multisig_site hashes EncodedLayout.chunks.flatten
    validKey verify (ByteLayout.program.take 446)
    (ByteLayout.program.drop 447) initial final records success
  simpa [show CoreCheckedStep.signatureSites
      (ByteLayout.program.take 446) = 3 by decide] using reached

private theorem literal_final_scan (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ sourceBefore : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes (ByteLayout.program.take 879)
        (CoreCheckedStep.lift initial records) = some sourceBefore ∧
      CoreMultisigEval.finalTenEval EncodedLayout.chunks.flatten
        (CoreFinalChecksigEval.checker validKey verify)
        sourceBefore.stack.reverse = some true := by
  obtain ⟨before, previous, checkedPrefix, checkedFinal, recorded,
    enough, keys, sigs, dummy⟩ :=
    CoreCheckedStep.literal_checked_run_final_source_layout hashes
      validKey verify initial final records success accepted
  have structural := CoreCheckedStep.checked_run_frames
    hashes EncodedLayout.chunks.flatten validKey verify
    (ByteLayout.program.take 879) initial before previous [true]
    checkedPrefix
  have sourcePrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 879)
      (CoreCheckedStep.lift initial records) =
        some (CoreCheckedStep.lift before [true]) := by
    rw [recorded]
    exact structural
  have finalEval := CoreCheckedStep.checkedMultisig_final_ten_eval
    EncodedLayout.chunks.flatten validKey verify before final
    keys sigs dummy enough checkedFinal
  exact ⟨CoreCheckedStep.lift before [true], sourcePrefix,
    by simpa [CoreCheckedStep.lift] using finalEval⟩

/-- A truthy checker-derived execution of the literal lock satisfies all six
reached source-signature conditions in the existing executable certificate.
The first multisignature may be false; its computed result must still match
the structural outcome cursor. No compiled-Core implication is asserted. -/
theorem literal_run_necessary_signature_checks (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    CoreSourceExtraction.necessarySignatureChecks hashes
      (CoreCheckedStep.lift initial records) validKey verify = true := by
  have site2 : ByteLayout.program = ByteLayout.program.take 2 ++
      .checksigverify :: ByteLayout.program.drop 3 := by decide
  have site5 : ByteLayout.program = ByteLayout.program.take 5 ++
      .checksigverify :: ByteLayout.program.drop 6 := by decide
  have site423 : ByteLayout.program = ByteLayout.program.take 423 ++
      .checksigverify :: ByteLayout.program.drop 424 := by decide
  have site856 : ByteLayout.program = ByteLayout.program.take 856 ++
      .checksigverify :: ByteLayout.program.drop 857 := by decide
  obtain ⟨pin, pinRun, pinChecked, _⟩ :=
    literal_checksig_at hashes validKey verify 2 site2
      initial final records success
  obtain ⟨early, earlyRun, earlyChecked, _⟩ :=
    literal_checksig_at hashes validKey verify 5 site5
      initial final records success
  obtain ⟨firstPuzzle, firstRun, firstChecked, _⟩ :=
    literal_checksig_at hashes validKey verify 423 site423
      initial final records success
  obtain ⟨late, lateRun, lateChecked, _⟩ :=
    literal_checksig_at hashes validKey verify 856 site856
      initial final records success
  obtain ⟨finalCheck, finalRun, finalChecked⟩ :=
    literal_final_scan hashes validKey verify
      initial final records success accepted
  obtain ⟨firstRound, actual, firstRoundRun, firstRoundScan,
    firstRoundOutcome, _⟩ :=
    literal_first_scan hashes validKey verify
      initial final records success
  have other : CoreSourceExtraction.otherSignatureChecks hashes
      (CoreCheckedStep.lift initial records) validKey verify = true := by
    simp [CoreSourceExtraction.otherSignatureChecks,
      pinRun, earlyRun, firstRun, lateRun, finalRun,
      pinChecked, earlyChecked, firstChecked, lateChecked,
      finalChecked]
  have first : CoreSourceExtraction.firstRoundSignatureCheck hashes
      (CoreCheckedStep.lift initial records) validKey verify = true := by
    simp [CoreSourceExtraction.firstRoundSignatureCheck,
      firstRoundRun, firstRoundScan, firstRoundOutcome]
  simp [CoreSourceExtraction.necessarySignatureChecks,
    other, first]

/-- The complete checker-derived result list has four true VERIFY sites,
one arbitrary first-round multisignature result, and a true enforcing final
multisignature result. The first-round Boolean is the actual reached scan. -/
theorem literal_run_record_pattern (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ firstRound,
      records = CoreCheckedCertificate.outcomes firstRound := by
  have site2 : ByteLayout.program = ByteLayout.program.take 2 ++
      .checksigverify :: ByteLayout.program.drop 3 := by decide
  have site5 : ByteLayout.program = ByteLayout.program.take 5 ++
      .checksigverify :: ByteLayout.program.drop 6 := by decide
  have site423 : ByteLayout.program = ByteLayout.program.take 423 ++
      .checksigverify :: ByteLayout.program.drop 424 := by decide
  have site856 : ByteLayout.program = ByteLayout.program.take 856 ++
      .checksigverify :: ByteLayout.program.drop 857 := by decide
  obtain ⟨_, _, _, pinAt⟩ :=
    literal_checksig_at hashes validKey verify 2 site2
      initial final records success
  obtain ⟨_, _, _, earlyAt⟩ :=
    literal_checksig_at hashes validKey verify 5 site5
      initial final records success
  obtain ⟨_, _, _, firstAt⟩ :=
    literal_checksig_at hashes validKey verify 423 site423
      initial final records success
  obtain ⟨_, _, _, lateAt⟩ :=
    literal_checksig_at hashes validKey verify 856 site856
      initial final records success
  obtain ⟨_, firstRound, _, _, _, firstRoundAt⟩ :=
    literal_first_scan hashes validKey verify
      initial final records success
  obtain ⟨beforeFinal, previous, beforeRun, _, recorded⟩ :=
    CoreCheckedStep.literal_checked_run_final_scan_true hashes
      validKey verify initial final records success accepted
  have previousLen := CoreCheckedStep.run_record_length hashes
    EncodedLayout.chunks.flatten validKey verify
    (ByteLayout.program.take 879) initial beforeFinal previous beforeRun
  have lastAt : records[previous.length]? = some true := by
    rw [recorded]
    simp
  have e0 : records[0]? = some true := by
    simpa [show CoreCheckedStep.signatureSites
      (ByteLayout.program.take 2) = 0 by decide] using pinAt
  have e1 : records[1]? = some true := by
    simpa [show CoreCheckedStep.signatureSites
      (ByteLayout.program.take 5) = 1 by decide] using earlyAt
  have e2 : records[2]? = some true := by
    simpa [show CoreCheckedStep.signatureSites
      (ByteLayout.program.take 423) = 2 by decide] using firstAt
  have e3 : records[3]? = some firstRound := firstRoundAt
  have e4 : records[4]? = some true := by
    simpa [show CoreCheckedStep.signatureSites
      (ByteLayout.program.take 856) = 4 by decide] using lateAt
  have e5 : records[5]? = some true := by
    simpa [previousLen, show CoreCheckedStep.signatureSites
      (ByteLayout.program.take 879) = 5 by decide] using lastAt
  have lengthSix := CoreCheckedStep.literal_run_six_records hashes
    validKey verify initial final records success
  refine ⟨firstRound, ?_⟩
  apply List.ext_getElem?
  intro i
  by_cases within : i < 6
  · interval_cases i
    all_goals simp [CoreCheckedCertificate.outcomes,
      e0, e1, e2, e3, e4, e5]
  · have leftNone : records[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    have rightNone : (CoreCheckedCertificate.outcomes firstRound)[i]? =
        none := by simp [CoreCheckedCertificate.outcomes, within]
    exact leftNone.trans rightNone.symm

/-- Starting from an arbitrary post-scriptSig byte stack and zero opcode
cost, a truthy checker-derived run is accepted by the existing certificate
candidate for its actually computed first-round scan Boolean. -/
theorem literal_run_candidate (hashes : Hashes)
    (stack : List Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ firstRound,
      records = CoreCheckedCertificate.outcomes firstRound ∧
      CoreCheckedCertificate.candidate hashes stack validKey verify
        firstRound = some (CoreCheckedStep.lift final []) := by
  obtain ⟨firstRound, pattern⟩ :=
    literal_run_record_pattern hashes validKey verify
      ⟨stack.reverse, 0⟩ final records success accepted
  have startEq : CoreCheckedStep.lift
      (⟨stack.reverse, 0⟩ : CoreCheckedStep.State) records =
        CoreCheckedCertificate.initial stack firstRound := by
    simp [CoreCheckedStep.lift, CoreCheckedCertificate.initial,
      CoreOpcodeStep.ofByte, pattern]
  have structural := CoreCheckedStep.checked_run_frames hashes
    EncodedLayout.chunks.flatten validKey verify ByteLayout.program
    ⟨stack.reverse, 0⟩ final records [] success
  have sourceRun : CoreStructuralRun.run hashes ByteLayout.program
      (CoreCheckedCertificate.initial stack firstRound) =
        some (CoreCheckedStep.lift final []) := by
    simpa [startEq] using structural
  have modeledTruth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true := by
    rw [← CoreCheckedStep.literal_checked_run_final_truth hashes
      validKey verify ⟨stack.reverse, 0⟩ final records success]
    exact accepted
  have sourceTruth : ByteMachine.finalTruth
      ⟨(CoreCheckedStep.lift final []).stack.reverse,
        (CoreCheckedStep.lift final []).outcomes,
        (CoreCheckedStep.lift final []).ops⟩ = true := by
    simpa [CoreCheckedStep.lift] using modeledTruth
  have checked := literal_run_necessary_signature_checks hashes
    validKey verify ⟨stack.reverse, 0⟩ final records success accepted
  have sourceChecks : CoreSourceExtraction.necessarySignatureChecks
      hashes (CoreCheckedCertificate.initial stack firstRound)
        validKey verify = true := by
    simpa [startEq] using checked
  obtain ⟨sourceBefore, actual, firstRun, sourceScan,
    _outcome, recordAt⟩ :=
    literal_first_scan hashes validKey verify
      ⟨stack.reverse, 0⟩ final records success
  have actualEq : actual = firstRound := by
    rw [pattern] at recordAt
    simpa [CoreCheckedCertificate.outcomes] using recordAt.symm
  have candidatePrefix : CoreStructuralRun.run hashes
      (ByteLayout.program.take 446)
      (CoreCheckedCertificate.initial stack firstRound) =
        some sourceBefore := by
    simpa [startEq] using firstRun
  have firstMatches : CoreCheckedCertificate.firstOutcomeMatches
      hashes stack validKey verify firstRound = true := by
    unfold CoreCheckedCertificate.firstOutcomeMatches
    simpa [candidatePrefix, actualEq] using sourceScan
  refine ⟨firstRound, pattern, ?_⟩
  exact CoreCheckedCertificate.candidate_complete hashes stack
    validKey verify firstRound (CoreCheckedStep.lift final [])
    sourceRun sourceTruth sourceChecks firstMatches

/-- The executable two-candidate certificate search finds some result for
every truthy checked literal source-model run from an arbitrary initial byte
stack. The search result need not be identified here with the recorded first
Boolean; both candidates are independently checked. -/
theorem literal_run_search_succeeds (hashes : Hashes)
    (stack : List Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ firstRound sourceFinal,
      CoreCheckedCertificate.search hashes stack validKey verify =
        some (firstRound, sourceFinal) := by
  obtain ⟨firstRound, _pattern, found⟩ :=
    literal_run_candidate hashes stack validKey verify
      final records success accepted
  cases firstRound with
  | false =>
      exact ⟨false, CoreCheckedStep.lift final [],
        by simp [CoreCheckedCertificate.search, found]⟩
  | true =>
      cases other : CoreCheckedCertificate.candidate hashes stack
          validKey verify false with
      | none =>
          exact ⟨true, CoreCheckedStep.lift final [],
            by simp [CoreCheckedCertificate.search, other, found]⟩
      | some otherFinal =>
          exact ⟨false, otherFinal,
            by simp [CoreCheckedCertificate.search, other]⟩

/-- The checker-derived source run now supplies the earlier certificate's
pin and enforcing final-round conclusions without assuming its six site
checks separately. These obligations still concern the external checker
function, not compiled Core or a quantum security game. -/
theorem literal_run_extract_pin_and_final (hashes : Hashes)
    (stack : List Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ (pinKey puzzleKey raw : Bytes) (tail : List Bytes)
      (w : RoundWitness (Fin 150) Bytes Bytes)
      (sourceBeforeCheck : CoreOpcodeStep.State),
      stack = pinKey :: puzzleKey :: raw :: tail ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        PinPuzzleScriptCode.literalScript
        FirstOvershoot.pinSignature pinKey validKey verify = some true ∧
      DERSyntax.valid (hashes.h256 pinKey) = true ∧
      FinalRoundWitness.extractMatchedWitness hashes
        ⟨stack, records, 0⟩ = some w ∧
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      DERSyntax.valid (hashes.h256 w.key) = true ∧
      CoreStructuralRun.run hashes (ByteLayout.program.take 879)
        (CoreOpcodeStep.ofByte ⟨stack, records, 0⟩) =
          some sourceBeforeCheck ∧
      sourceBeforeCheck.outcomes.head? = some true ∧
      CoreFinalChecksigEval.checker validKey verify
        PoolRollInvariant.finalNonce w.key
        (CoreMultisigEval.deletedScript EncodedLayout.chunks.flatten
          sourceBeforeCheck.stack.reverse) = true := by
  have sourceRun : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte ⟨stack, records, 0⟩) =
        some (CoreCheckedStep.lift final []) := by
    simpa [CoreCheckedStep.lift, CoreOpcodeStep.ofByte] using
      CoreCheckedStep.checked_run_frames hashes
        EncodedLayout.chunks.flatten validKey verify ByteLayout.program
        ⟨stack.reverse, 0⟩ final records [] success
  have modeledTruth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true := by
    rw [← CoreCheckedStep.literal_checked_run_final_truth hashes
      validKey verify ⟨stack.reverse, 0⟩ final records success]
    exact accepted
  have sourceTruth : ByteMachine.finalTruth
      ⟨(CoreCheckedStep.lift final []).stack.reverse,
        (CoreCheckedStep.lift final []).outcomes,
        (CoreCheckedStep.lift final []).ops⟩ = true := by
    simpa [CoreCheckedStep.lift] using modeledTruth
  have checks : CoreSourceExtraction.necessarySignatureChecks hashes
      (CoreOpcodeStep.ofByte ⟨stack, records, 0⟩)
        validKey verify = true := by
    simpa [CoreCheckedStep.lift, CoreOpcodeStep.ofByte] using
      literal_run_necessary_signature_checks hashes validKey verify
        ⟨stack.reverse, 0⟩ final records success accepted
  exact CoreSourceExtraction.necessary_checks_extract_pin_and_final
    hashes stack records (CoreCheckedStep.lift final [])
    validKey verify sourceRun sourceTruth checks

/-- Both fixed signatures in a truthy checked literal run call the external
verifier with `SIGHASH_ALL` and their actual source-shaped scriptCodes. This
is a deterministic statement about the checker interface, not an ECDSA,
transaction-hash, or compiled-Core verification theorem. -/
theorem literal_run_fixed_all_calls (hashes : Hashes)
    (stack : List Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes EncodedLayout.chunks.flatten
      validKey verify ByteLayout.program ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ (pinKey : Bytes) (w : RoundWitness (Fin 150) Bytes Bytes)
      (beforeCheck : CoreOpcodeStep.State),
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      FinalRoundWitness.extractMatchedWitness hashes
        ⟨stack, records, 0⟩ = some w ∧
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
  have sourceRun : CoreStructuralRun.run hashes ByteLayout.program
      (CoreOpcodeStep.ofByte ⟨stack, records, 0⟩) =
        some (CoreCheckedStep.lift final []) := by
    simpa [CoreCheckedStep.lift, CoreOpcodeStep.ofByte] using
      CoreCheckedStep.checked_run_frames hashes
        EncodedLayout.chunks.flatten validKey verify ByteLayout.program
        ⟨stack.reverse, 0⟩ final records [] success
  have modeledTruth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true := by
    rw [← CoreCheckedStep.literal_checked_run_final_truth hashes
      validKey verify ⟨stack.reverse, 0⟩ final records success]
    exact accepted
  have sourceTruth : ByteMachine.finalTruth
      ⟨(CoreCheckedStep.lift final []).stack.reverse,
        (CoreCheckedStep.lift final []).outcomes,
        (CoreCheckedStep.lift final []).ops⟩ = true := by
    simpa [CoreCheckedStep.lift] using modeledTruth
  have checks : CoreSourceExtraction.necessarySignatureChecks hashes
      (CoreOpcodeStep.ofByte ⟨stack, records, 0⟩)
        validKey verify = true := by
    simpa [CoreCheckedStep.lift, CoreOpcodeStep.ofByte] using
      literal_run_necessary_signature_checks hashes validKey verify
        ⟨stack.reverse, 0⟩ final records success accepted
  exact CoreSourceExtraction.necessary_checks_fixed_all_calls
    hashes stack records (CoreCheckedStep.lift final [])
    validKey verify sourceRun sourceTruth checks

end QSB.CoreCheckedRunCertificate
