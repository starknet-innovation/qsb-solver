import QSB.DynamicWireSource
import QSB.CoreStructuralRun

/-!
Connect the parameterized full-wire lock to the bottom-first, Core-shaped
structural interpreter. A single successful source run supplies the byte run;
the final source evaluator is checked at the state reached by that same run.
Cryptographic outcomes are still supplied, and this is not compiled Core.
-/
namespace QSB.DynamicCoreStructural
open ByteMachine
open EncodedScript
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

theorem full_program_final_check_split (priorOps : List Op)
    (nonce : Bytes) (commitmentAt : Fin 150 → Bytes) :
    DynamicWholeSource.fullProgram priorOps nonce commitmentAt =
      DynamicWholeSource.beforeFinalCheckProgram priorOps nonce commitmentAt ++
        [.checkmultisig] := by
  have suffix : ByteLayout.program.drop 840 =
      FinalBonusSecond.bothBonusOps ++
        (ByteLatePuzzle.lateOps ++ ByteFinalCounts.finalSetup) ++
        [.checkmultisig] := by decide
  simp [DynamicWholeSource.fullProgram,
    DynamicWholeSource.beforeFinalCheckProgram,
    DynamicBonusChain.final_round_program_eq,
    DynamicBonusChain.finalCheckPrefix, suffix, List.append_assoc]

/-- One successful source-shaped run of the parsed full wire program, and a
true final ten-pair evaluator at its reached pre-CHECKMULTISIG stack, imply
the executable seven-opening trace and nine distinct selected positions on
a good setup. The source run's signature Booleans still require a link to
Core's real checker, and compiled Core acceptance is not a premise here. -/
theorem accepted_structural_wire_good_setup_nine_positions
    (hashes : Hashes)
    (priorChunks : List Bytes) (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (priorSimple : ∀ chunk ∈ priorChunks,
      FindAndDelete.simpleChunk chunk = true)
    (priorDecoded : priorChunks.map decodeChunk = priorOps.map some)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76)
    (initial : State) (sourceFinal : CoreOpcodeStep.State)
    (parsedOps : List Op)
    (parsed : DynamicSerializedRound.parseCoreOps
      (DynamicWireSource.fullChunks priorChunks nonce commitmentAt).length
      (DynamicWireSource.fullWire priorChunks nonce commitmentAt) = some parsedOps)
    (accepted : CoreStructuralRun.run hashes parsedOps
      (CoreOpcodeStep.ofByte initial) = some sourceFinal)
    (checker : Bytes → Bytes → Bytes → Bool)
    (sourceEval : ∀ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes
        (DynamicWholeSource.beforeFinalCheckProgram priorOps nonce commitmentAt)
        (CoreOpcodeStep.ofByte initial) = some beforeCheck →
      CoreMultisigEval.finalTenEval
        (DynamicWireSource.fullWire priorChunks nonce commitmentAt) checker
        beforeCheck.stack.reverse = some true)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (commitmentAt id) = false) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      DynamicWholeSource.extractTrace hashes priorOps initial = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  have identity := DynamicWireSource.full_wire_decodes priorChunks priorOps
    nonce commitmentAt priorSimple priorDecoded width nonceShort
  have opsEq : parsedOps =
      DynamicWholeSource.fullProgram priorOps nonce commitmentAt :=
    Option.some.inj (parsed.symm.trans identity)
  subst parsedOps
  obtain ⟨byteFinal, byteAccepted, _sourceShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes
      (DynamicWholeSource.fullProgram priorOps nonce commitmentAt)
      initial sourceFinal accepted
  have sourcePrefix : ∃ middle,
      CoreStructuralRun.run hashes
        (DynamicWholeSource.beforeFinalCheckProgram priorOps nonce commitmentAt)
        (CoreOpcodeStep.ofByte initial) = some middle := by
    rw [full_program_final_check_split] at accepted
    exact CoreStructuralRun.successful_prefix hashes
      (DynamicWholeSource.beforeFinalCheckProgram priorOps nonce commitmentAt)
      [.checkmultisig] (CoreOpcodeStep.ofByte initial) sourceFinal accepted
  obtain ⟨sourceBefore, reached⟩ := sourcePrefix
  obtain ⟨byteBefore, byteReached, sourceBeforeShape⟩ :=
    CoreStructuralRun.run_refines_byte hashes
      (DynamicWholeSource.beforeFinalCheckProgram priorOps nonce commitmentAt)
      initial sourceBefore reached
  apply DynamicWholeSource.accepted_whole_good_setup_nine_positions
    hashes priorOps nonce commitmentAt width initial byteFinal byteAccepted
    (DynamicWireSource.fullWire priorChunks nonce commitmentAt) checker
  · intro beforeCheck byteRun
    have same : beforeCheck = byteBefore :=
      Option.some.inj (byteRun.symm.trans byteReached)
    subst beforeCheck
    have checked := sourceEval sourceBefore reached
    simpa [sourceBeforeShape, CoreOpcodeStep.ofByte] using checked
  · exact noCommitmentDER

end QSB.DynamicCoreStructural
