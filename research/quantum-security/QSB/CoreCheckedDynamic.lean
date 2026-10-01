import QSB.CoreCheckedRunCertificate
import QSB.DynamicCheckedCertificate
import QSB.DynamicCoreFinalTruth

/-!
The parameterized Config A program is run with signature-site results computed
at the reached stacks.  These results concern the Lean source-shaped checker;
the compiled Bitcoin Core interpreter, transaction sighash, and ECDSA remain
external to this model.
-/
namespace QSB.CoreCheckedDynamic
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Parameterized data pushes do not move Config A's six signature opcodes. -/
theorem site_opcodes (lock : DynamicCheckedCertificate.Lock) :
    DynamicCheckedCertificate.siteOpcodes lock = true := by
  have static5 : (DynamicFullSerialized.staticOps 1 5).length = 5 := by
    decide
  have static151 : (DynamicFullSerialized.staticOps 156 151).length =
      151 := by decide
  have static138 : (DynamicFullSerialized.staticOps 308 138).length =
      138 := by decide
  have dummyLength : PoolRollInvariant.finalDummyPushes.length = 150 := by
    decide
  simp [DynamicCheckedCertificate.siteOpcodes,
    DynamicCheckedCertificate.program,
    DynamicWholeSource.fullProgram,
    DynamicFullSerialized.priorOps,
    DynamicFullSerialized.pinOps,
    DynamicFullSerialized.firstDataOps,
    DynamicFinalInit.commitmentPushes,
    DynamicFinalInit.commitmentPool,
    DynamicFinalInit.finalRoundProgram,
    DynamicFinalInit.dataOps,
    List.getElem?_append, static5, static151, static138,
    dummyLength]; decide +revert

private theorem split_at_opcode (ops : List Op) (k : Nat) (op : Op)
    (hAt : ops[k]? = some op) :
    ops = ops.take k ++ op :: ops.drop (k + 1) := by
  induction k generalizing ops with
  | zero =>
      cases ops with
      | nil => simp at hAt
      | cons head tail =>
          simp at hAt
          subst head
          rfl
  | succ k ih =>
      cases ops with
      | nil => simp at hAt
      | cons head tail =>
          have inner : tail[k]? = some op := by simpa using hAt
          change head :: tail =
            head :: (tail.take k ++ op :: tail.drop (k + 1))
          exact congrArg (List.cons head) (ih tail inner)

private theorem dynamic_checksig_at (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (k : Nat)
    (site : (DynamicCheckedCertificate.program lock)[k]? =
      some .checksigverify)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records)) :
    ∃ sourceBefore : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes
        ((DynamicCheckedCertificate.program lock).take k)
        (CoreCheckedStep.lift initial records) = some sourceBefore ∧
      CoreChecksigEval.evalBaseVerifyAll 880
        (DynamicCheckedCertificate.wire lock)
        (sourceBefore.stack.reverse[1]?.getD [])
        (sourceBefore.stack.reverse[0]?.getD [])
        validKey verify = some true ∧
      records[CoreCheckedStep.signatureSites
        ((DynamicCheckedCertificate.program lock).take k)]? =
          some true := by
  have split := split_at_opcode
    (DynamicCheckedCertificate.program lock) k .checksigverify site
  rw [split] at success
  exact CoreCheckedRunCertificate.reached_checksig_site hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    ((DynamicCheckedCertificate.program lock).take k)
    ((DynamicCheckedCertificate.program lock).drop (k + 1))
    initial final records success

private theorem dynamic_multisig_at (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (k : Nat)
    (site : (DynamicCheckedCertificate.program lock)[k]? =
      some .checkmultisig)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records)) :
    ∃ (sourceBefore : CoreOpcodeStep.State) (actual : Bool),
      CoreStructuralRun.run hashes
        ((DynamicCheckedCertificate.program lock).take k)
        (CoreCheckedStep.lift initial records) = some sourceBefore ∧
      CoreMultisigSourceScan.scanAtStack
        (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        sourceBefore.stack = some actual ∧
      sourceBefore.outcomes.head? = some actual ∧
      records[CoreCheckedStep.signatureSites
        ((DynamicCheckedCertificate.program lock).take k)]? =
          some actual := by
  have split := split_at_opcode
    (DynamicCheckedCertificate.program lock) k .checkmultisig site
  rw [split] at success
  exact CoreCheckedRunCertificate.reached_multisig_site hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    ((DynamicCheckedCertificate.program lock).take k)
    ((DynamicCheckedCertificate.program lock).drop (k + 1))
    initial final records success

private theorem signature_sites_append (before after : List Op) :
    CoreCheckedStep.signatureSites (before ++ after) =
      CoreCheckedStep.signatureSites before +
        CoreCheckedStep.signatureSites after := by
  induction before with
  | nil => simp [CoreCheckedStep.signatureSites]
  | cons op rest ih =>
      cases op <;> simp [CoreCheckedStep.signatureSites, ih,
        Nat.add_assoc]

private theorem signature_sites_pushes (values : List Bytes) :
    CoreCheckedStep.signatureSites (values.map Op.push) = 0 := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [CoreCheckedStep.signatureSites, ih]

private theorem signature_sites_take_pushes (values : List Bytes)
    (k : Nat) :
    CoreCheckedStep.signatureSites
      ((values.map Op.push).take k) = 0 := by
  simpa only [List.map_take] using
    signature_sites_pushes (values.take k)

private theorem signature_sites_take_mapped_pushes {α : Type}
    (values : List α) (f : α → Bytes) (k : Nat) :
    CoreCheckedStep.signatureSites
      ((values.map (Op.push ∘ f)).take k) = 0 := by
  simpa only [List.map_map, Function.comp_def] using
    signature_sites_take_pushes (values.map f) k

private theorem signature_sites_take_reverse_mapped_pushes {α : Type}
    (values : List α) (f : α → Bytes) (k : Nat) :
    CoreCheckedStep.signatureSites
      ((values.map (Op.push ∘ f)).reverse.take k) = 0 := by
  simpa only [List.map_reverse] using
    signature_sites_take_mapped_pushes values.reverse f k

theorem program_six_sites (lock : DynamicCheckedCertificate.Lock) :
    CoreCheckedStep.signatureSites
      (DynamicCheckedCertificate.program lock) = 6 := by
  simp [DynamicCheckedCertificate.program,
    DynamicWholeSource.fullProgram,
    DynamicFullSerialized.priorOps,
    DynamicFullSerialized.pinOps,
    DynamicFullSerialized.firstDataOps,
    DynamicFinalInit.finalRoundProgram,
    DynamicFinalInit.dataOps,
    signature_sites_append, signature_sites_pushes,
    CoreCheckedStep.signatureSites]; decide +revert

theorem prefix_site_counts (lock : DynamicCheckedCertificate.Lock) :
    CoreCheckedStep.signatureSites
      ((DynamicCheckedCertificate.program lock).take 2) = 0 ∧
    CoreCheckedStep.signatureSites
      ((DynamicCheckedCertificate.program lock).take 5) = 1 ∧
    CoreCheckedStep.signatureSites
      ((DynamicCheckedCertificate.program lock).take 423) = 2 ∧
    CoreCheckedStep.signatureSites
      ((DynamicCheckedCertificate.program lock).take 446) = 3 ∧
    CoreCheckedStep.signatureSites
      ((DynamicCheckedCertificate.program lock).take 856) = 4 ∧
    CoreCheckedStep.signatureSites
      ((DynamicCheckedCertificate.program lock).take 879) = 5 := by
  have static5 : (DynamicFullSerialized.staticOps 1 5).length = 5 := by
    decide
  have static151 : (DynamicFullSerialized.staticOps 156 151).length =
      151 := by decide
  have static138 : (DynamicFullSerialized.staticOps 308 138).length =
      138 := by decide
  have dummyLength : PoolRollInvariant.finalDummyPushes.length = 150 := by
    decide
  simp [DynamicCheckedCertificate.program,
    DynamicWholeSource.fullProgram,
    DynamicFullSerialized.priorOps,
    DynamicFullSerialized.pinOps,
    DynamicFullSerialized.firstDataOps,
    DynamicFinalInit.finalRoundProgram,
    DynamicFinalInit.dataOps,
    DynamicFinalInit.commitmentPushes,
    DynamicFinalInit.commitmentPool,
    List.take_append, static5, static151, static138,
    dummyLength, signature_sites_append,
    signature_sites_take_pushes,
    signature_sites_take_reverse_mapped_pushes,
    CoreCheckedStep.signatureSites] ; decide +revert

theorem program_final_split (lock : DynamicCheckedCertificate.Lock) :
    DynamicCheckedCertificate.program lock =
      DynamicCheckedCertificate.beforeFinalProgram lock ++
        [.checkmultisig] := by
  have suffix840 : ByteLayout.program.drop 840 =
      FinalBonusSecond.bothBonusOps ++ ByteLayout.program.drop 850 := by
    decide
  simp [DynamicCheckedCertificate.program,
    DynamicCheckedCertificate.beforeFinalProgram,
    DynamicWholeSource.fullProgram,
    DynamicWholeSource.beforeFinalCheckProgram,
    DynamicBonusChain.finalCheckPrefix,
    DynamicBonusChain.final_round_program_eq,
    suffix840, ByteLatePuzzle.generated_late_final_check_split,
    List.append_assoc]

/-- An accepted, truthy checked execution of any parameterized Config A
program has a true final source-shaped multisignature scan.  The first scan
result is not constrained by this theorem. -/
theorem checked_run_final_scan_true (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ before previous,
      CoreCheckedStep.run hashes (DynamicCheckedCertificate.wire lock)
        validKey verify
        (DynamicCheckedCertificate.beforeFinalProgram lock) initial =
          some (before, previous) ∧
      CoreCheckedStep.checkedMultisig (DynamicCheckedCertificate.wire lock)
        validKey verify before = some (final, true) ∧
      records = previous ++ [true] := by
  have structural := CoreCheckedStep.checked_run_frames hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.program lock) initial final records [] success
  have truth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true := by
    have sourceTruth := DynamicCoreFinalTruth.source_run_final_truth hashes
      lock ⟨initial.stack.reverse, records, initial.ops⟩
      (CoreCheckedStep.lift final []) (by
        simpa [DynamicCheckedCertificate.initial,
          CoreCheckedStep.lift, CoreOpcodeStep.ofByte] using structural)
    have finalEq : CoreFinalTruth.coreFinalTruth
        (CoreCheckedStep.lift final []) =
          CoreFinalTruth.castToBool
            (final.stack.getLast?.getD []) := by
      simp [CoreFinalTruth.coreFinalTruth, CoreCheckedStep.lift]
    rw [finalEq] at sourceTruth
    exact sourceTruth.symm.trans accepted
  rw [program_final_split lock] at success
  exact CoreCheckedStep.checked_run_ending_multisig_true hashes
    (DynamicCheckedCertificate.wire lock) validKey verify _ initial final
    records success truth

/-- Successful dynamic byte execution reaches the fixed ten/ten count cells
and the empty NULLDUMMY cell.  This part is independent of the commitment
bytes and of the signature verdicts. -/
theorem byte_final_layout (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (initial beforeCheck final : ByteMachine.State)
    (prefixRun : ByteMachine.run hashes
      (DynamicCheckedCertificate.beforeFinalProgram lock) initial =
        some beforeCheck)
    (full : ByteMachine.run hashes
      (DynamicCheckedCertificate.program lock) initial = some final) :
    23 ≤ beforeCheck.stack.length ∧
    beforeCheck.stack[0]? = some [0x0a] ∧
    beforeCheck.stack[11]? = some [0x0a] ∧
    beforeCheck.stack[22]? = some [] := by
  let pre : List Op :=
    DynamicFullSerialized.priorOps lock.pin lock.nonce0
      lock.firstCommitment ++ [.checkmultisig] ++
    DynamicSignedChain.dataAndSignedProgram lock.nonce1
      lock.secondCommitment ++ FinalBonusSecond.bothBonusOps ++
    ByteLatePuzzle.lateOps
  have beforeSplit : DynamicCheckedCertificate.beforeFinalProgram lock =
      pre ++ ByteFinalCounts.finalSetup := by
    simp [pre, DynamicCheckedCertificate.beforeFinalProgram,
      DynamicWholeSource.beforeFinalCheckProgram,
      DynamicBonusChain.finalCheckPrefix, List.append_assoc]
  rw [beforeSplit, ByteMachine.run_append] at prefixRun
  cases hpre : ByteMachine.run hashes pre initial with
  | none => simp [hpre] at prefixRun
  | some under =>
      have setup : ByteMachine.run hashes ByteFinalCounts.finalSetup
          under = some beforeCheck := by simpa [hpre] using prefixRun
      obtain ⟨keyCount, sigCount⟩ :=
        ByteFinalCounts.accepted_final_setup_count_operands hashes
          under.stack under.outcomes under.ops beforeCheck setup
      rw [program_final_split lock, ByteMachine.run_append] at full
      have exactPrefix : ByteMachine.run hashes
          (pre ++ ByteFinalCounts.finalSetup) initial =
            some beforeCheck := by
        rw [ByteMachine.run_append, hpre]
        exact setup
      have last : ByteMachine.run hashes [.checkmultisig]
          beforeCheck = some final := by
        simpa [beforeSplit, exactPrefix] using full
      have dummy := ByteFinalCounts.successful_final_check_dummy_empty
        hashes beforeCheck final keyCount sigCount last
      have enough : 23 ≤ beforeCheck.stack.length := by
        obtain ⟨index, _⟩ := List.getElem?_eq_some_iff.mp dummy
        omega
      exact ⟨enough, keyCount, sigCount, dummy⟩

/-- The checked final scan on a parameterized lock supplies the specialized
ten-pair source evaluator at the *same reached stack* as the byte execution.
The checker remains an external key-parser/ECDSA function. -/
theorem checked_run_final_ten_eval (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ before : ByteMachine.State,
      ByteMachine.run hashes
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        ⟨initial.stack.reverse, records, initial.ops⟩ = some before ∧
      CoreMultisigEval.finalTenEval
        (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        before.stack = some true := by
  obtain ⟨before, previous, checkedPrefix, checkedFinal, recorded⟩ :=
    checked_run_final_scan_true hashes lock validKey verify
      initial final records success accepted
  have bytePrefix := CoreCheckedStep.checked_run_refines_byte_tail hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    initial before previous [true] checkedPrefix
  have reached : ByteMachine.run hashes
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      ⟨initial.stack.reverse, records, initial.ops⟩ =
        some ⟨before.stack.reverse, [true], before.ops⟩ := by
    rw [recorded]
    exact bytePrefix
  have whole := CoreCheckedStep.checked_run_refines_byte hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.program lock) initial final records success
  obtain ⟨enough, keys, sigs, dummy⟩ :=
    byte_final_layout hashes lock
      ⟨initial.stack.reverse, records, initial.ops⟩
      ⟨before.stack.reverse, [true], before.ops⟩
      ⟨final.stack.reverse, [], final.ops⟩ reached whole
  have finalEval := CoreCheckedStep.checkedMultisig_final_ten_eval
    (DynamicCheckedCertificate.wire lock) validKey verify
    before final keys sigs dummy (by simpa using enough) checkedFinal
  exact ⟨⟨before.stack.reverse, [true], before.ops⟩, reached, finalEval⟩

/-- The six computed result records of a truthy parameterized checked run
have the same fixed pattern as the literal lock.  Its one unconstrained entry
is the actual reached first-round multisignature result. -/
theorem checked_run_record_pattern (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ firstRound,
      records = CoreCheckedCertificate.outcomes firstRound := by
  have roles :
      (DynamicCheckedCertificate.program lock)[2]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[5]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[423]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[446]? = some .checkmultisig ∧
      (DynamicCheckedCertificate.program lock)[856]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[879]? = some .checkmultisig := by
    simpa [DynamicCheckedCertificate.siteOpcodes] using site_opcodes lock
  obtain ⟨at2, at5, at423, at446, at856, _at879⟩ := roles
  obtain ⟨_, _, _, pinAt⟩ :=
    dynamic_checksig_at hashes lock validKey verify 2 at2
      initial final records success
  obtain ⟨_, _, _, earlyAt⟩ :=
    dynamic_checksig_at hashes lock validKey verify 5 at5
      initial final records success
  obtain ⟨_, _, _, puzzleAt⟩ :=
    dynamic_checksig_at hashes lock validKey verify 423 at423
      initial final records success
  obtain ⟨_, firstRound, _, _, _, firstRoundAt⟩ :=
    dynamic_multisig_at hashes lock validKey verify 446 at446
      initial final records success
  obtain ⟨_, _, _, lateAt⟩ :=
    dynamic_checksig_at hashes lock validKey verify 856 at856
      initial final records success
  obtain ⟨before, previous, beforeRun, _, recorded⟩ :=
    checked_run_final_scan_true hashes lock validKey verify
      initial final records success accepted
  have prefixCounts := prefix_site_counts lock
  have beforeSites : CoreCheckedStep.signatureSites
      (DynamicCheckedCertificate.beforeFinalProgram lock) = 5 := by
    have six := program_six_sites lock
    rw [program_final_split, signature_sites_append] at six
    simp [CoreCheckedStep.signatureSites] at six
    omega
  have previousLen := CoreCheckedStep.run_record_length hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    initial before previous beforeRun
  have lengthSix := CoreCheckedStep.run_record_length hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.program lock)
    initial final records success
  have e0 : records[0]? = some true := by
    simpa [prefixCounts.1] using pinAt
  have e1 : records[1]? = some true := by
    simpa [prefixCounts.2.1] using earlyAt
  have e2 : records[2]? = some true := by
    simpa [prefixCounts.2.2.1] using puzzleAt
  have e3 : records[3]? = some firstRound := by
    simpa [prefixCounts.2.2.2.1] using firstRoundAt
  have e4 : records[4]? = some true := by
    simpa [prefixCounts.2.2.2.2.1] using lateAt
  have e5 : records[5]? = some true := by
    have last : records[previous.length]? = some true := by
      rw [recorded]
      simp
    simpa [previousLen, beforeSites] using last
  have exactLength : records.length = 6 := by
    simpa [program_six_sites lock] using lengthSix
  refine ⟨firstRound, ?_⟩
  apply List.ext_getElem?
  intro i
  by_cases within : i < 6
  · interval_cases i
    all_goals simp [CoreCheckedCertificate.outcomes,
      e0, e1, e2, e3, e4, e5]
  · have leftNone : records[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    have rightNone :
        (CoreCheckedCertificate.outcomes firstRound)[i]? = none := by
      simp [CoreCheckedCertificate.outcomes, within]
    exact leftNone.trans rightNone.symm

/-- Once the computed records have the six-site pattern, the existing
parameterized certificate's four reached CHECKSIGVERIFY checks and first
multisignature scan follow from this one checker-derived run. -/
theorem checked_run_source_sites (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (pattern : records = CoreCheckedCertificate.outcomes firstRound) :
    DynamicCheckedCertificate.sourceSites hashes lock stack validKey verify
      firstRound = true := by
  have roles :
      (DynamicCheckedCertificate.program lock)[2]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[5]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[423]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[446]? = some .checkmultisig ∧
      (DynamicCheckedCertificate.program lock)[856]? = some .checksigverify ∧
      (DynamicCheckedCertificate.program lock)[879]? = some .checkmultisig := by
    simpa [DynamicCheckedCertificate.siteOpcodes] using site_opcodes lock
  obtain ⟨at2, at5, at423, at446, at856, _at879⟩ := roles
  obtain ⟨pin, pinRun, pinChecked, _⟩ :=
    dynamic_checksig_at hashes lock validKey verify 2 at2
      ⟨stack.reverse, 0⟩ final records success
  obtain ⟨early, earlyRun, earlyChecked, _⟩ :=
    dynamic_checksig_at hashes lock validKey verify 5 at5
      ⟨stack.reverse, 0⟩ final records success
  obtain ⟨firstPuzzle, puzzleRun, puzzleChecked, _⟩ :=
    dynamic_checksig_at hashes lock validKey verify 423 at423
      ⟨stack.reverse, 0⟩ final records success
  obtain ⟨firstCheck, actual, firstRun, firstScan,
    _firstOutcome, firstAt⟩ :=
    dynamic_multisig_at hashes lock validKey verify 446 at446
      ⟨stack.reverse, 0⟩ final records success
  obtain ⟨late, lateRun, lateChecked, _⟩ :=
    dynamic_checksig_at hashes lock validKey verify 856 at856
      ⟨stack.reverse, 0⟩ final records success
  have actualEq : actual = firstRound := by
    have at3 : records[3]? = some actual := by
      simpa [prefix_site_counts lock |>.2.2.2.1] using firstAt
    rw [pattern] at at3
    simpa [CoreCheckedCertificate.outcomes] using at3.symm
  have startEq : CoreCheckedStep.lift
      (⟨stack.reverse, 0⟩ : CoreCheckedStep.State) records =
        DynamicCheckedCertificate.initial stack firstRound := by
    simp [CoreCheckedStep.lift, DynamicCheckedCertificate.initial,
      CoreOpcodeStep.ofByte, pattern]
  rw [startEq] at pinRun earlyRun puzzleRun firstRun lateRun
  simp [DynamicCheckedCertificate.sourceSites,
    pinRun, earlyRun, puzzleRun, firstRun, lateRun,
    site_opcodes lock, pinChecked, earlyChecked, puzzleChecked,
    lateChecked, actualEq, firstScan]

/-- The final source evaluator in the parameterized certificate is computed
at the structural state reached by the same checker-derived run. -/
theorem checked_run_final_checked (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (firstRound : Bool)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true)
    (pattern : records = CoreCheckedCertificate.outcomes firstRound) :
    DynamicCheckedCertificate.finalChecked hashes lock stack validKey verify
      firstRound = true := by
  obtain ⟨before, previous, checkedPrefix, _, recorded⟩ :=
    checked_run_final_scan_true hashes lock validKey verify
      ⟨stack.reverse, 0⟩ final records success accepted
  have structural := CoreCheckedStep.checked_run_frames hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    ⟨stack.reverse, 0⟩ before previous [true] checkedPrefix
  have sourcePrefix : CoreStructuralRun.run hashes
      (DynamicCheckedCertificate.beforeFinalProgram lock)
      (DynamicCheckedCertificate.initial stack firstRound) =
        some (CoreCheckedStep.lift before [true]) := by
    have startEq : CoreCheckedStep.lift
        (⟨stack.reverse, 0⟩ : CoreCheckedStep.State) records =
          DynamicCheckedCertificate.initial stack firstRound := by
      simp [CoreCheckedStep.lift, DynamicCheckedCertificate.initial,
        CoreOpcodeStep.ofByte, pattern]
    rw [recorded] at startEq
    simpa [startEq] using structural
  obtain ⟨byteBefore, bytePrefix, finalEval⟩ :=
    checked_run_final_ten_eval hashes lock validKey verify
      ⟨stack.reverse, 0⟩ final records success accepted
  have checkedByte := CoreCheckedStep.checked_run_refines_byte_tail hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    ⟨stack.reverse, 0⟩ before previous [true] checkedPrefix
  have same : byteBefore =
      (⟨before.stack.reverse, [true], before.ops⟩ : ByteMachine.State) := by
    apply Option.some.inj
    calc
      some byteBefore = ByteMachine.run hashes
          (DynamicCheckedCertificate.beforeFinalProgram lock)
          ⟨stack, records, 0⟩ := by
            simpa only [List.reverse_reverse] using bytePrefix.symm
      _ = some ⟨before.stack.reverse, [true], before.ops⟩ := by
        rw [recorded]
        simpa only [List.reverse_reverse] using checkedByte
  subst byteBefore
  simp [DynamicCheckedCertificate.finalChecked,
    sourcePrefix, CoreCheckedStep.lift] at finalEval ⊢
  exact finalEval

/-- A truthy checker-derived parameterized run is accepted by the existing
certificate candidate for its actual first-round scan result. -/
theorem checked_run_candidate (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ firstRound,
      records = CoreCheckedCertificate.outcomes firstRound ∧
      DynamicCheckedCertificate.candidate hashes lock stack validKey verify
        firstRound = some (CoreCheckedStep.lift final []) := by
  obtain ⟨firstRound, pattern⟩ :=
    checked_run_record_pattern hashes lock validKey verify
      ⟨stack.reverse, 0⟩ final records success accepted
  have sourceRun := CoreCheckedStep.checked_run_frames hashes
    (DynamicCheckedCertificate.wire lock) validKey verify
    (DynamicCheckedCertificate.program lock)
    ⟨stack.reverse, 0⟩ final records [] success
  have startEq : CoreCheckedStep.lift
      (⟨stack.reverse, 0⟩ : CoreCheckedStep.State) records =
        DynamicCheckedCertificate.initial stack firstRound := by
    simp [CoreCheckedStep.lift, DynamicCheckedCertificate.initial,
      CoreOpcodeStep.ofByte, pattern]
  simp only [List.append_nil] at sourceRun
  rw [startEq] at sourceRun
  have truthEq := DynamicCoreFinalTruth.source_run_final_truth hashes
    lock ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩
    (CoreCheckedStep.lift final []) sourceRun
  have sourceTruth : ByteMachine.finalTruth
      ⟨(CoreCheckedStep.lift final []).stack.reverse,
        (CoreCheckedStep.lift final []).outcomes,
        (CoreCheckedStep.lift final []).ops⟩ = true := by
    rw [← truthEq]
    simpa [CoreFinalTruth.coreFinalTruth,
      CoreCheckedStep.lift] using accepted
  have sites := checked_run_source_sites hashes lock stack validKey
    verify firstRound final records success pattern
  have last := checked_run_final_checked hashes lock stack validKey
    verify firstRound final records success accepted pattern
  refine ⟨firstRound, pattern, ?_⟩
  exact DynamicCheckedCertificate.candidate_complete hashes lock stack
    validKey verify firstRound (CoreCheckedStep.lift final [])
    sourceRun sourceTruth sites last

/-- The executable two-candidate parameterized certificate search finds a
result for every truthy checker-derived run from an arbitrary initial stack.
The result may be the false candidate if both independently checked candidate
runs work. -/
theorem checked_run_search_succeeds (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ firstRound sourceFinal,
      DynamicCheckedCertificate.search hashes lock stack validKey verify =
        some (firstRound, sourceFinal) := by
  obtain ⟨firstRound, _pattern, found⟩ :=
    checked_run_candidate hashes lock stack validKey verify
      final records success accepted
  cases firstRound with
  | false =>
      exact ⟨false, CoreCheckedStep.lift final [],
        by simp [DynamicCheckedCertificate.search, found]⟩
  | true =>
      cases other : DynamicCheckedCertificate.candidate hashes lock stack
          validKey verify false with
      | none =>
          exact ⟨true, CoreCheckedStep.lift final [],
            by simp [DynamicCheckedCertificate.search, other, found]⟩
      | some otherFinal =>
          exact ⟨false, otherFinal,
            by simp [DynamicCheckedCertificate.search, other]⟩

/-- A truthy checker-derived run of any parameterized Config A lock fixes
nine distinct second-round positions outside the DER-shaped-commitment setup
exception.  No final signature result, ten-pair scan, or source-site verdict
is supplied separately by the caller.  The result still assumes the Lean
checker and byte execution model, not compiled Bitcoin Core acceptance. -/
theorem checked_run_good_setup_nine_positions (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (width : ∀ i : Fin 150, (lock.secondCommitment i).length = 20)
    (noCommitmentDER : ∀ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = false)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      DynamicWholeSource.extractTrace hashes
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment) ⟨stack, records, 0⟩ = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  let prior := DynamicFullSerialized.priorOps lock.pin lock.nonce0
    lock.firstCommitment
  let sourceInitial : CoreCheckedStep.State := ⟨stack.reverse, 0⟩
  let byteInitial : ByteMachine.State := ⟨stack, records, 0⟩
  let byteFinal : ByteMachine.State :=
    ⟨final.stack.reverse, [], final.ops⟩
  have byteRun : ByteMachine.run hashes
      (DynamicWholeSource.fullProgram prior lock.nonce1
        lock.secondCommitment) byteInitial = some byteFinal := by
    simpa [prior, byteInitial, byteFinal, sourceInitial,
      DynamicCheckedCertificate.program] using
      CoreCheckedStep.checked_run_refines_byte hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) sourceInitial final records
      success
  obtain ⟨sourceBefore, beforeRun, finalEval⟩ :=
    checked_run_final_ten_eval hashes lock validKey verify
      sourceInitial final records success accepted
  have finalGate : ∀ beforeCheck : ByteMachine.State,
      ByteMachine.run hashes
        (DynamicWholeSource.beforeFinalCheckProgram prior lock.nonce1
          lock.secondCommitment) byteInitial = some beforeCheck →
      CoreMultisigEval.finalTenEval
        (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        beforeCheck.stack = some true := by
    intro beforeCheck reached
    have same : beforeCheck = sourceBefore :=
      Option.some.inj (reached.symm.trans (by
        simpa [prior, byteInitial, sourceInitial,
          DynamicCheckedCertificate.beforeFinalProgram] using beforeRun))
    subst beforeCheck
    exact finalEval
  exact DynamicWholeSource.accepted_whole_good_setup_nine_positions
    hashes prior lock.nonce1 lock.secondCommitment width
      byteInitial byteFinal byteRun
      (DynamicCheckedCertificate.wire lock)
      (CoreFinalChecksigEval.checker validKey verify)
      finalGate noCommitmentDER

/-- For an arbitrary parameterized lock, a truthy checker-derived execution
either encounters the explicit DER-shaped second-round setup exception or
extracts nine distinct second-round positions. -/
theorem checked_run_der_exception_or_nine_positions (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (width : ∀ i : Fin 150, (lock.secondCommitment i).length = 20)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) ⟨stack.reverse, 0⟩ =
        some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    (∃ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = true) ∨
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      DynamicWholeSource.extractTrace hashes
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment) ⟨stack, records, 0⟩ = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  by_cases bad : ∃ i : Fin 150,
      DERSyntax.valid (lock.secondCommitment i) = true
  · exact Or.inl bad
  · apply Or.inr
    have good : ∀ i : Fin 150,
        DERSyntax.valid (lock.secondCommitment i) = false := by
      intro i
      cases h : DERSyntax.valid (lock.secondCommitment i) with
      | false => rfl
      | true => exact False.elim (bad ⟨i, h⟩)
    exact checked_run_good_setup_nine_positions hashes lock width good
      stack validKey verify final records success accepted

end QSB.CoreCheckedDynamic
