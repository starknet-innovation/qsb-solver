import QSB.ByteMachineQueries
import QSB.CoreCheckedDynamic
import QSB.LockOpcodeBudget

/-!
Source-model accounting for signature verification in the parameterized Config A
lock. The tracked pair scan follows the same early-exit and DER-gate branches
as `CoreMultisigEval.scan`. Each attempted pair consumes one key, including
failed comparisons. One legacy signature digest costs at most two H calls.
The key parser, sighash implementation, ECDSA verifier, and compiled Core
refinement remain external. `validKey` and `verify` are arbitrary functions;
their own oracle use is not counted. The 48 H-call figure applies when each
reached `verify` call is instantiated with one modeled legacy SHA256d digest,
which uses at most two H evaluations. The 81 figure adds that reservation to
the separately traced byte-model hash opcodes; it is not a traced bound for
the whole checked run.
-/
namespace QSB.LockSignatureQueryBudget
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Instrument the source-shaped scan with the number of pairs for which the
encoding gate passed and the verifier was evaluated. -/
def scanTracked (encoding : Bytes → Bool) (verify : Bytes → Bytes → Bool) :
    List Bytes → List Bytes → Option Bool × Nat
  | [], _ => (some true, 0)
  | _ :: _, [] => (some false, 0)
  | sig :: sigs, key :: keys =>
      if (sig :: sigs).length > (key :: keys).length then (some false, 0)
      else if encoding sig then
        if verify sig key then
          let later := scanTracked encoding verify sigs keys
          (later.1, later.2 + 1)
        else
          let later := scanTracked encoding verify (sig :: sigs) keys
          (later.1, later.2 + 1)
      else (none, 0)

/-- Instrumentation leaves the source scanner's result unchanged, including
nonfatal false results and fatal DER failures. -/
theorem scanTracked_result (encoding : Bytes → Bool)
    (verify : Bytes → Bytes → Bool) :
    ∀ (sigs keys : List Bytes),
      (scanTracked encoding verify sigs keys).1 =
        CoreMultisigEval.scan encoding verify sigs keys
  | sigs, [] => by cases sigs <;> rfl
  | [], _ :: _ => rfl
  | sig :: sigs, key :: keys => by
      simp only [scanTracked, CoreMultisigEval.scan]
      split_ifs <;> simp [scanTracked_result encoding verify]

/-- Each attempted pair advances the key cursor; no path evaluates the
verifier more often than there are reached keys. -/
theorem scanTracked_calls_le (encoding : Bytes → Bool)
    (verify : Bytes → Bytes → Bool) :
    ∀ (sigs keys : List Bytes),
      (scanTracked encoding verify sigs keys).2 ≤ keys.length
  | sigs, [] => by cases sigs <;> simp [scanTracked]
  | [], _ :: _ => by simp [scanTracked]
  | sig :: sigs, key :: keys => by
      simp only [scanTracked]
      split_ifs <;>
        simp only [List.length_cons] <;>
        have a := scanTracked_calls_le encoding verify sigs keys <;>
        have b := scanTracked_calls_le encoding verify (sig :: sigs) keys <;>
        omega

/-- Instrument the actual source-shaped multisignature entry point. Rejected
count/capacity checks perform no pair evaluations. -/
def scanAtStackTracked (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool)
    (bottom : List Bytes) : Option Bool × Nat :=
  match CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none => (none, 0)
  | some n =>
      if n < 0 ∨ n > 20 then (none, 0) else
      match CoreMultisigCleanup.parseSourceCount bottom (n.toNat + 2) with
      | none => (none, 0)
      | some m =>
          if m < 0 ∨ m > n then (none, 0) else
          let top := bottom.reverse
          if n.toNat + m.toNat + 3 > top.length then (none, 0) else
          scanTracked DERSyntax.verifyAllEncoding
            (CoreMultisigEval.nonemptyVerify checker
              (CoreMultisigSourceScan.deletedScript script top
                n.toNat m.toNat))
            (CoreMultisigSourceScan.reachedSignatures top
              n.toNat m.toNat)
            (CoreMultisigSourceScan.reachedKeys top n.toNat)

theorem scanAtStackTracked_result (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool)
    (bottom : List Bytes) :
    (scanAtStackTracked script checker bottom).1 =
      CoreMultisigSourceScan.scanAtStack script checker bottom := by
  unfold scanAtStackTracked CoreMultisigSourceScan.scanAtStack
  cases keys : CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none => simp
  | some n =>
      by_cases badN : n < 0 ∨ n > 20
      · simp [badN]
      · cases sigs : CoreMultisigCleanup.parseSourceCount bottom
            (n.toNat + 2) with
        | none => simp [badN, sigs]
        | some m =>
            by_cases badM : m < 0 ∨ m > n
            · simp [badN, sigs, badM]
            · by_cases short : bottom.length < n.toNat + m.toNat + 3
              · simp [badN, sigs, badM, short]
              · simp [badN, sigs, badM, short,
                  scanTracked_result]

/-- At a reached ten-key site, the source-shaped pair loop evaluates at most
ten pairs, even when the scan returns false or aborts on malformed DER. -/
theorem scanAtStackTracked_ten_calls_le (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool)
    (bottom : List Bytes)
    (ten : CoreMultisigCleanup.parseSourceCount bottom 1 = some 10) :
    (scanAtStackTracked script checker bottom).2 ≤ 10 := by
  cases sigs : CoreMultisigCleanup.parseSourceCount bottom 12 with
  | none => simp [scanAtStackTracked, ten, sigs]
  | some m =>
      by_cases badM : m < 0 ∨ m > (10 : Int)
      · simp [scanAtStackTracked, ten, sigs, badM]
      · by_cases short : bottom.length < 10 + m.toNat + 3
        · simp [scanAtStackTracked, ten, sigs, badM, short]
        ·
          have h := scanTracked_calls_le DERSyntax.verifyAllEncoding
            (CoreMultisigEval.nonemptyVerify checker
              (CoreMultisigSourceScan.deletedScript script bottom.reverse
                10 m.toNat))
            (CoreMultisigSourceScan.reachedSignatures bottom.reverse
              10 m.toNat)
            (CoreMultisigSourceScan.reachedKeys bottom.reverse 10)
          have keysLength :
              (CoreMultisigSourceScan.reachedKeys bottom.reverse 10).length
                ≤ 10 := by
            simp [CoreMultisigSourceScan.reachedKeys]
          simpa [scanAtStackTracked, ten, sigs, badM, short] using
            le_trans h keysLength

/-- The fixed `OP_10` data push at each generated multisignature site is
read as ten keys by the source-shaped one-based count parser. -/
theorem parse_ten_after_push (xs : List Bytes) :
    CoreMultisigCleanup.parseSourceCount (xs ++ [[0x0a]]) 1 = some 10 := by
  simp [CoreMultisigCleanup.parseSourceCount,
    CoreMultisigStack.stacktopNeg, CoreScriptNum.coreSetVch,
    ByteIndex.coreOrWord]

/-- A successful checked ten-key multisignature step uses the instrumented
source scan, and evaluates at most ten verifier pairs. -/
theorem checkedMultisig_ten_pair_calls_le (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : CoreCheckedStep.State) (result : Bool)
    (ten : CoreMultisigCleanup.parseSourceCount s.stack 1 = some 10)
    (success : CoreCheckedStep.checkedMultisig script validKey verify s =
      some (next, result)) :
    (scanAtStackTracked script
      (CoreFinalChecksigEval.checker validKey verify) s.stack).1 =
        some result ∧
    (scanAtStackTracked script
      (CoreFinalChecksigEval.checker validKey verify) s.stack).2 ≤ 10 := by
  constructor
  · rw [scanAtStackTracked_result]
    exact (CoreCheckedStep.checkedMultisig_sound script validKey verify
      s next result success).1
  · exact scanAtStackTracked_ten_calls_le script
      (CoreFinalChecksigEval.checker validKey verify) s.stack ten

theorem checked_push_ten_shape (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : CoreCheckedStep.State) (record : Option Bool)
    (success : CoreCheckedStep.step hashes script validKey verify
      (.push [0x0a]) s = some (next, record)) :
    next = ⟨s.stack ++ [[0x0a]], s.ops⟩ ∧ record = none := by
  simp [CoreCheckedStep.step, CoreOpcodeStep.step] at success
  exact ⟨success.2.1.symm, success.2.2.symm⟩

private theorem checked_run_cons_success (hashes : Hashes)
    (script : Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (op : Op) (rest : List Op)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes script validKey verify
      (op :: rest) initial = some (final, records)) :
    ∃ next record later,
      CoreCheckedStep.step hashes script validKey verify op initial =
        some (next, record) ∧
      next.stack.length ≤ 1000 ∧
      CoreCheckedStep.run hashes script validKey verify rest next =
        some (final, later) ∧
      records = record.toList ++ later := by
  simp only [CoreCheckedStep.run] at success
  cases hstep : CoreCheckedStep.step hashes script validKey verify op initial with
  | none => simp [hstep] at success
  | some pair =>
      obtain ⟨next, record⟩ := pair
      by_cases large : next.stack.length > 1000
      · simp [hstep, large] at success
      · cases hrest : CoreCheckedStep.run hashes script validKey verify rest next with
        | none => simp [hstep, large, hrest] at success
        | some pair =>
            obtain ⟨after, later⟩ := pair
            have output : final = after ∧
                records = record.toList ++ later := by
              simpa [hstep, large, hrest] using success.symm
            rcases output with ⟨rfl, rfl⟩
            exact ⟨next, record, later, rfl, by omega, hrest, rfl⟩

/-- A successful generated key-check fragment has a reached ten-key
source scan. Its recorded pair-call count is at most ten, for either scan
Boolean; a false first-round multisignature is included. -/
theorem checked_keyCheck_pair_calls_le (hashes : Hashes)
    (script : Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes script validKey verify
      LockOpcodeBudget.keyCheck initial = some (final, records)) :
    ∃ before result,
      CoreCheckedStep.checkedMultisig script validKey verify before =
        some (final, result) ∧
      records = [result] ∧
      (scanAtStackTracked script
        (CoreFinalChecksigEval.checker validKey verify) before.stack).1 =
          some result ∧
      (scanAtStackTracked script
        (CoreFinalChecksigEval.checker validKey verify) before.stack).2 ≤ 10 := by
  change CoreCheckedStep.run hashes script validKey verify
      [.push [0x0a], .checkmultisig] initial =
        some (final, records) at success
  obtain ⟨before, pushRecord, later, pushStep, _, restRun,
      recordsEq⟩ := checked_run_cons_success hashes script validKey verify
        (.push [0x0a]) [.checkmultisig] initial final records success
  obtain ⟨beforeShape, pushRecordEq⟩ :=
    checked_push_ten_shape hashes script validKey verify
      initial before pushRecord pushStep
  subst before
  subst pushRecord
  obtain ⟨next, checkRecord, tail, checkStep, _, emptyRun,
      laterEq⟩ := checked_run_cons_success hashes script validKey verify
        .checkmultisig []
        ⟨initial.stack ++ [[0x0a]], initial.ops⟩ final later restRun
  simp [CoreCheckedStep.run] at emptyRun
  rcases emptyRun with ⟨rfl, rfl⟩
  cases multiStep : CoreCheckedStep.checkedMultisig script validKey verify
      ⟨initial.stack ++ [[0x0a]], initial.ops⟩ with
  | none => simp [CoreCheckedStep.step, multiStep] at checkStep
  | some pair =>
      obtain ⟨after, result⟩ := pair
      have pair : (next, checkRecord) = (after, some result) := by
        simpa [CoreCheckedStep.step, multiStep] using checkStep.symm
      rcases Prod.mk.inj pair with ⟨rfl, rfl⟩
      have ten : CoreMultisigCleanup.parseSourceCount
          (initial.stack ++ [[0x0a]]) 1 = some 10 :=
        parse_ten_after_push initial.stack
      have scan := checkedMultisig_ten_pair_calls_le script validKey verify
        ⟨initial.stack ++ [[0x0a]], initial.ops⟩ next result ten multiStep
      refine ⟨_, result, multiStep, ?_, scan.1, scan.2⟩
      simp [recordsEq, laterEq]

private theorem checked_run_append_success (hashes : Hashes)
    (script : Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (before after : List Op)
    (initial final : CoreCheckedStep.State) (records : List Bool)
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
          obtain ⟨afterState, later⟩ := pair
          have output : final = afterState ∧ records = first ++ later := by
            simpa [hbefore, hafter] using success.symm
          rcases output with ⟨rfl, rfl⟩
          exact ⟨middle, first, later, rfl, hafter, rfl⟩

/-- Both generated ten-key source scans are reached in every successful
checked execution of the parameterized lock. Their combined number of
attempted pair-verifier calls is at most twenty, including a false first
round. This counts the scan control flow only: arbitrary `validKey` and
`verify` implementations may make additional oracle calls. -/
theorem checked_lock_multisig_pair_calls_le_20 (hashes : Hashes)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : CoreCheckedStep.State) (records : List Bool)
    (success : CoreCheckedStep.run hashes
      (DynamicCheckedCertificate.wire lock) validKey verify
      (DynamicCheckedCertificate.program lock) initial =
        some (final, records)) :
    ∃ afterFirst beforeFirst beforeFinal resultFirst resultFinal,
      CoreCheckedStep.checkedMultisig
        (DynamicCheckedCertificate.wire lock) validKey verify
        beforeFirst = some (afterFirst, resultFirst) ∧
      CoreCheckedStep.checkedMultisig
        (DynamicCheckedCertificate.wire lock) validKey verify
        beforeFinal = some (final, resultFinal) ∧
      (scanAtStackTracked (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        beforeFirst.stack).1 = some resultFirst ∧
      (scanAtStackTracked (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        beforeFinal.stack).1 = some resultFinal ∧
      (scanAtStackTracked (DynamicCheckedCertificate.wire lock)
        (CoreFinalChecksigEval.checker validKey verify)
        beforeFirst.stack).2 +
        (scanAtStackTracked (DynamicCheckedCertificate.wire lock)
          (CoreFinalChecksigEval.checker validKey verify)
          beforeFinal.stack).2 ≤ 20 := by
  have split : DynamicCheckedCertificate.program lock =
      LockOpcodeBudget.priorPrefix lock ++
        (LockOpcodeBudget.keyCheck ++
          (LockOpcodeBudget.finalMiddle lock ++
            LockOpcodeBudget.keyCheck)) := by
    simpa only [List.append_assoc] using
      LockOpcodeBudget.program_split lock
  rw [split] at success
  let script := DynamicCheckedCertificate.wire lock
  obtain ⟨afterPrefix, prefixRecords, remainingRecords,
      _prefixRun, remainingRun, _⟩ :=
    checked_run_append_success hashes script validKey verify
      (LockOpcodeBudget.priorPrefix lock)
      (LockOpcodeBudget.keyCheck ++
        (LockOpcodeBudget.finalMiddle lock ++ LockOpcodeBudget.keyCheck))
      initial final records success
  obtain ⟨afterFirst, firstRecords, finalPartRecords,
      firstRun, finalPartRun, _⟩ :=
    checked_run_append_success hashes script validKey verify
      LockOpcodeBudget.keyCheck
      (LockOpcodeBudget.finalMiddle lock ++ LockOpcodeBudget.keyCheck)
      afterPrefix final remainingRecords remainingRun
  obtain ⟨beforeSecond, middleRecords, secondRecords,
      _middleRun, secondRun, _⟩ :=
    checked_run_append_success hashes script validKey verify
      (LockOpcodeBudget.finalMiddle lock) LockOpcodeBudget.keyCheck
      afterFirst final finalPartRecords finalPartRun
  obtain ⟨beforeFirst, resultFirst, firstCheck, _, firstScan,
      firstCalls⟩ := checked_keyCheck_pair_calls_le hashes script
        validKey verify afterPrefix afterFirst firstRecords firstRun
  obtain ⟨beforeFinal, resultFinal, finalCheck, _, finalScan,
      finalCalls⟩ := checked_keyCheck_pair_calls_le hashes script
        validKey verify beforeSecond final secondRecords secondRun
  dsimp [script] at firstCalls finalCalls
  exact ⟨afterFirst, beforeFirst, beforeFinal, resultFirst, resultFinal,
    firstCheck, finalCheck, firstScan, finalScan, by omega⟩

/-- The static signature-digest allowance of one opcode. `CHECKMULTISIG`
reserves ten attempted pairs at each of the lock's two fixed ten-key sites. -/
def sigHAllowance : Op → Nat
  | .checksigverify => 2
  | .checkmultisig => 20
  | _ => 0

theorem sigHAllowance_skeleton (op : Op) :
    sigHAllowance (LockOpcodeInventory.skeleton op) = sigHAllowance op := by
  cases op <;> rfl

theorem literal_sigHAllowance :
    (ByteLayout.program.map sigHAllowance).sum = 48 := by decide

/-- Every parameterized lock has four CHECKSIGVERIFY sites and two ten-key
CHECKMULTISIG sites, reserving 48 legacy SHA256 calls in total. -/
theorem lock_sigHAllowance (lock : DynamicCheckedCertificate.Lock) :
    ((DynamicCheckedCertificate.program lock).map sigHAllowance).sum = 48 := by
  have same := congrArg
    (fun ops : List Op => (ops.map sigHAllowance).sum)
    (LockOpcodeInventory.program_skeleton lock)
  simpa [List.map_map, sigHAllowance_skeleton,
    literal_sigHAllowance] using same

/-- The static per-opcode reservation totals 81: 33 for byte-model hash
opcodes plus 48 for signature-site SHA256d calls. This is not a traced
checked-run or Core query bound. -/
theorem lock_total_allowance (lock : DynamicCheckedCertificate.Lock) :
    ((DynamicCheckedCertificate.program lock).map
      (fun op => ByteMachineQueries.opBudget op + sigHAllowance op)).sum =
        81 := by
  have sum_add (ops : List Op) :
      (ops.map (fun op => ByteMachineQueries.opBudget op +
        sigHAllowance op)).sum =
      (ops.map ByteMachineQueries.opBudget).sum +
        (ops.map sigHAllowance).sum := by
    induction ops with
    | nil => rfl
    | cons op rest ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        omega
  rw [sum_add]
  have hash := ByteMachineQueries.lock_budget lock
  have signatures := lock_sigHAllowance lock
  omega

end QSB.LockSignatureQueryBudget
