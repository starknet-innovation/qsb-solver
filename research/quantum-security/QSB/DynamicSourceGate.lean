import QSB.DynamicBonusIndices
import QSB.CoreMultisigEval

/-!
Connect the parameterized final-round source extractor to the concrete
source-shaped ten-pair CHECKMULTISIG evaluator. Its ECDSA checker is still an
arbitrary function; a successful compiled-Core-to-evaluator refinement is not
claimed here.
-/
namespace QSB.DynamicSourceGate
open ByteMachine

def checkedPair (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (sig key : Bytes) : Bool :=
  DERSyntax.verifyAllEncoding sig &&
    CoreMultisigEval.nonemptyVerify checker
      (CoreMultisigEval.deletedScript script top) sig key

theorem checkedPair_der (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (sig key : Bytes)
    (success : checkedPair script checker top sig key = true) :
    DERSyntax.valid sig = true := by
  have parts : DERSyntax.verifyAllEncoding sig = true ∧
      CoreMultisigEval.nonemptyVerify checker
        (CoreMultisigEval.deletedScript script top) sig key = true := by
    simpa [checkedPair] using success
  have nonempty := (CoreMultisigEval.nonemptyVerify_sound checker
    (CoreMultisigEval.deletedScript script top) sig key parts.2).1
  simpa [DERSyntax.verifyAllEncoding_nonempty sig nonempty] using parts.1

theorem source_eval_success_match (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (success : CoreMultisigEval.finalTenEval script checker top = some true) :
    Multisig.matchSigs (checkedPair script checker top)
      ((top.drop 12).take 10) ((top.drop 1).take 10) = true := by
  simpa [checkedPair, FinalScriptCode.reachedSignatures] using
    CoreMultisigEval.finalTenEval_success_match script checker top success

/-- Source-shaped success discharges both the matched-scan and strict-DER
premises of the parameterized nine-position theorem. This is still
conditional on a successful modeled byte run and on success of the separate
source-shaped evaluator at the reached final stack. -/
theorem nine_positions_of_source_eval (hashes : Hashes)
    (nonce prior : Bytes) (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes
      (DynamicFinalInit.finalRoundProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) = some final)
    (script : Bytes) (checker : Bytes → Bytes → Bytes → Bool)
    (sourceEval : ∀ beforeCheck : State,
      run hashes (DynamicBonusChain.finalCheckPrefix nonce commitmentAt)
        (State.mk (prior :: tail) outcomes cost) = some beforeCheck →
      CoreMultisigEval.finalTenEval script checker
        beforeCheck.stack = some true)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (commitmentAt id) = false) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : State),
      run hashes (DynamicBonusChain.finalCheckPrefix nonce commitmentAt)
        (State.mk (prior :: tail) outcomes cost) = some beforeCheck ∧
      beforeCheck.stack[13]? =
        some (FinalSignedLoop.generatedDummyAt a) ∧
      beforeCheck.stack[12]? =
        some (FinalSignedLoop.generatedDummyAt b) ∧
      (∀ j : Nat, j < 7 → beforeCheck.stack[j + 14]? =
        (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?) ∧
      beforeCheck.stack[21]? = some nonce ∧
      beforeCheck.stack[22]? = some [] ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      a ≠ b ∧ a ∉ trace.map Prod.fst ∧ b ∉ trace.map Prod.fst ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
      FinalSignedChain.extractOrdered (List.finRange 7)
        (List.finRange 150) 0 tail = some trace := by
  apply DynamicBonusIndices.matched_dynamic_nine_positions
    hashes nonce prior commitmentAt width priorWrong tail outcomes cost
      final accepted
      (fun sig key => checkedPair script checker
        ((run hashes (DynamicBonusChain.finalCheckPrefix nonce commitmentAt)
          (State.mk (prior :: tail) outcomes cost)).getD
            (State.mk [] [] 0)).stack sig key)
  · intro sig key success
    exact checkedPair_der script checker _ sig key success
  · exact noCommitmentDER
  · intro beforeCheck reached
    simp [reached]
    simpa using source_eval_success_match script checker _
      (sourceEval beforeCheck reached)

end QSB.DynamicSourceGate
