import QSB.DynamicSourceGate
import QSB.FinalSignedAccepted

/-!
Compose an arbitrary first-round source-shaped priorOps with the parameterized
final round. A successful first CHECKMULTISIG always leaves `[]` or `[1]` on
the stack; the final-round extraction therefore needs no postulated prior
result width. The priorOps may be any opcode program. Equality with a production
builder output and refinement from compiled Core remain external.
-/
namespace QSB.DynamicWholeSource
open ByteMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def fullProgram (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  priorOps ++ [.checkmultisig] ++
    DynamicFinalInit.finalRoundProgram nonce commitmentAt

def beforeFinalCheckProgram (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  priorOps ++ [.checkmultisig] ++
    DynamicBonusChain.finalCheckPrefix nonce commitmentAt

theorem literal_full_program :
    fullProgram (ByteLayout.program.take 446)
      PoolRollInvariant.finalNonce
      FinalSignedLoop.generatedCommitmentAt = ByteLayout.program := by
  have suffix : FinalSignedAccepted.firstFinalRoundPrefix ++
      ByteLayout.program.drop 761 = ByteLayout.program.drop 447 := by
    simpa [FinalSignedAccepted.firstFinalRoundPrefix, List.drop_drop]
      using (List.take_append_drop 314 (ByteLayout.program.drop 447))
  calc
    _ = ByteLayout.program.take 446 ++ [.checkmultisig] ++
        ByteLayout.program.drop 447 := by
          rw [fullProgram, DynamicFinalInit.literal_final_round_program]
    _ = ByteLayout.program.take 446 ++ [.checkmultisig] ++
        (FinalSignedAccepted.firstFinalRoundPrefix ++
          ByteLayout.program.drop 761) := by rw [suffix]
    _ = ByteLayout.program := by
      simpa only [List.append_assoc, List.singleton_append] using
        FinalSignedAccepted.generated_first_round_check_boundary.symm

/-- Every successful full modeled run has a first-round Boolean cell at the
exact boundary where the parameterized second round begins. Nothing about the
contents of the priorOps or the initial witness stack is assumed. -/
theorem accepted_first_boundary (hashes : Hashes)
    (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (initial final : State)
    (accepted : run hashes (fullProgram priorOps nonce commitmentAt)
      initial = some final) :
    ∃ (result : Bool) (tail : List Bytes)
      (outcomes : List Bool) (cost : Nat),
      run hashes (priorOps ++ [.checkmultisig]) initial =
        some (State.mk (boolBytes result :: tail) outcomes cost) ∧
      run hashes (DynamicFinalInit.finalRoundProgram nonce commitmentAt)
        (State.mk (boolBytes result :: tail) outcomes cost) = some final := by
  rw [fullProgram, run_append] at accepted
  cases reached : run hashes (priorOps ++ [.checkmultisig]) initial with
  | none => simp [reached] at accepted
  | some afterFirst =>
      have suffix : run hashes
          (DynamicFinalInit.finalRoundProgram nonce commitmentAt)
          afterFirst = some final := by
        simpa [reached] using accepted
      rw [run_append] at reached
      cases before : run hashes priorOps initial with
      | none => simp [before] at reached
      | some beforeCheck =>
          have one : run hashes [.checkmultisig] beforeCheck =
              some afterFirst := by
            simpa [before] using reached
          have stepped : step hashes .checkmultisig beforeCheck =
              some afterFirst := by
            cases hStep : step hashes .checkmultisig beforeCheck with
            | none => simp [run, hStep] at one
            | some next =>
                by_cases large : next.stack.length > 1000
                · simp [run, hStep, large] at one
                · have same : next = afterFirst := by
                    simpa [run, hStep, large] using one
                  simp [same]
          obtain ⟨result, tail, shape⟩ :=
            FinalSignedAccepted.successful_checkmultisig_result_shape
              hashes beforeCheck afterFirst stepped
          cases afterFirst with
          | mk stack outcomes cost =>
              change stack = boolBytes result :: tail at shape
              subst stack
              exact ⟨result, tail, outcomes, cost, rfl, suffix⟩

theorem first_result_wrong_width (result : Bool) :
    (boolBytes result).length ≠ 20 := by
  cases result <;> decide

/-- The tenth signature cell of the reached final multisignature is the
lock-pushed nonce for every successful parameterized byte run. This uses no
DER or signature-checker premise: it is a stack-origin fact. -/
theorem accepted_whole_final_nonce_slot (hashes : Hashes)
    (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (initial final : State)
    (accepted : run hashes (fullProgram priorOps nonce commitmentAt)
      initial = some final) :
    ∃ beforeCheck : State,
      run hashes (beforeFinalCheckProgram priorOps nonce commitmentAt)
        initial = some beforeCheck ∧
      beforeCheck.stack[21]? = some nonce := by
  obtain ⟨result, tail, outcomes, cost, firstRun, finalRun⟩ :=
    accepted_first_boundary hashes priorOps nonce commitmentAt initial final
      accepted
  obtain ⟨_, _, _, _, _, _, _, _, beforeCheck, prefixRun,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, nonceSlot,
      _, _, _⟩ :=
    DynamicBonusChain.accepted_data_signed_final_signature_origins
      hashes nonce (boolBytes result) commitmentAt width
      (first_result_wrong_width result) tail outcomes cost final finalRun
  refine ⟨beforeCheck, ?_, nonceSlot⟩
  change run hashes ((priorOps ++ [.checkmultisig]) ++
    DynamicBonusChain.finalCheckPrefix nonce commitmentAt) initial =
      some beforeCheck
  rw [run_append, firstRun]
  exact prefixRun

/-- Read the seven signed opening pairs from the actual post-first-round
modeled stack. The first-round prefix is executed, then the extractor uses
the same fixed witness-tail offsets as the dynamic signed-chain proof. -/
def extractTrace (hashes : Hashes) (priorOps : List Op)
    (initial : State) : Option (List (Fin 150 × Bytes)) := do
  let afterFirst ← run hashes (priorOps ++ [.checkmultisig]) initial
  match afterFirst.stack with
  | [] => none
  | _ :: tail =>
      FinalSignedChain.extractOrdered (List.finRange 7)
        (List.finRange 150) 0 tail

/-- With a successful source-shaped final ten-pair evaluation on the reached
stack, every accepted byte-model full run from an arbitrary witness stack
yields seven actual opening/hash equations and two further distinct bonus
positions on a good setup. The priorOps may contain any pinning/first-round
opcodes, but its last CHECKMULTISIG is explicit. -/
theorem accepted_whole_good_setup_nine_positions (hashes : Hashes)
    (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (initial final : State)
    (accepted : run hashes (fullProgram priorOps nonce commitmentAt)
      initial = some final)
    (script : Bytes) (checker : Bytes → Bytes → Bytes → Bool)
    (sourceEval : ∀ beforeCheck : State,
      run hashes (beforeFinalCheckProgram priorOps nonce commitmentAt)
        initial = some beforeCheck →
      CoreMultisigEval.finalTenEval script checker
        beforeCheck.stack = some true)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (commitmentAt id) = false) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      extractTrace hashes priorOps initial = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  obtain ⟨result, tail, outcomes, cost, firstRun, finalRun⟩ :=
    accepted_first_boundary hashes priorOps nonce commitmentAt initial final
      accepted
  have gate : ∀ beforeCheck : State,
      run hashes (DynamicBonusChain.finalCheckPrefix nonce commitmentAt)
        (State.mk (boolBytes result :: tail) outcomes cost) =
          some beforeCheck →
      CoreMultisigEval.finalTenEval script checker
        beforeCheck.stack = some true := by
    intro beforeCheck reached
    apply sourceEval beforeCheck
    change run hashes ((priorOps ++ [.checkmultisig]) ++
      DynamicBonusChain.finalCheckPrefix nonce commitmentAt) initial =
        some beforeCheck
    rw [run_append, firstRun]
    exact reached
  obtain ⟨trace, a, b, beforeCheck, _reached, _slotA, _slotB,
      _signed, _nonceSlot, _dummySlot, seven, hits,
      _different, _freshA, _freshB, distinct, count, traceExtract⟩ :=
    DynamicSourceGate.nine_positions_of_source_eval hashes nonce
      (boolBytes result) commitmentAt width
      (first_result_wrong_width result) tail outcomes cost final finalRun
      script checker gate noCommitmentDER
  have extracted : extractTrace hashes priorOps initial = some trace := by
    simp only [extractTrace, firstRun]
    exact traceExtract
  exact ⟨trace, a, b, extracted, seven, hits, distinct, count⟩

end QSB.DynamicWholeSource
