import QSB.FinalSignedLoop

/-!
The second-round data-push block with arbitrary commitment and nonce bytes.
The dummy bytes are the deterministic Config A second-round signatures from
the inspected builder. This is an executable byte-model block, not a proof
that every generated script or compiled Core uses it. The subsequent signed
and bonus instructions require a separate parameterized execution bridge.
-/
namespace QSB.DynamicFinalInit
open ByteMachine
open FinalSignedLoop
open FinalSignedBoundary
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def commitmentPool (commitmentAt : Fin 150 → Bytes) : List Bytes :=
  (List.finRange 150).map commitmentAt

def commitmentPushes (commitmentAt : Fin 150 → Bytes) : List Bytes :=
  (commitmentPool commitmentAt).reverse

def dataOps (nonce : Bytes) (commitmentAt : Fin 150 → Bytes) : List Op :=
  (commitmentPushes commitmentAt ++ finalDummyPushes ++
    [[], nonce]).map Op.push

/-- Vary the second-round data pushes while retaining the literal Config A
selection and signature-opcode suffix. Matching this suffix to a dynamic
builder output is a separate source-refinement obligation. -/
def finalRoundProgram (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  dataOps nonce commitmentAt ++ ByteLayout.program.drop 749

theorem commitmentPool_length (commitmentAt : Fin 150 → Bytes) :
    (commitmentPool commitmentAt).length = 150 := by
  simp [commitmentPool]

theorem dataOps_length (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) :
    (dataOps nonce commitmentAt).length = 302 := by
  have dummyLength : finalDummyPushes.length = 150 := by
    simpa [finalDummyPool] using generated_dummy_pool_length
  simp [dataOps, commitmentPushes, commitmentPool, dummyLength]

/-- Successful execution of the arbitrary data-push block reconstructs the
same pool order as the generated literal lock, independent of lower witness
stack cells and supplied signature outcomes. -/
theorem accepted_data_shape (hashes : Hashes) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (dataOps nonce commitmentAt)
      (State.mk stack outcomes cost) = some final) :
    final = State.mk (nonce :: [] ::
      finalDummyPool ++ commitmentPool commitmentAt ++ stack)
        outcomes cost := by
  have shape := FinalSignedAccepted.accepted_pushes_shape hashes
    (commitmentPushes commitmentAt ++ finalDummyPushes ++ [[], nonce])
    stack outcomes cost final accepted
  simpa [dataOps, commitmentPushes, finalDummyPool,
    List.reverse_append, List.append_assoc] using shape

/-- The abstract dynamic block specializes to the exact 302 literal push
opcodes in the disposable generated lock. -/
theorem literal_data_ops :
    dataOps finalNonce generatedCommitmentAt =
      FinalSignedAccepted.finalRoundAllOps := by
  have poolEq : commitmentPool generatedCommitmentAt =
      finalCommitmentPool := by decide
  have pushesEq : commitmentPushes generatedCommitmentAt =
      finalCommitmentPushes := by
    simpa [commitmentPushes, finalCommitmentPool] using
      congrArg List.reverse poolEq
  rw [FinalSignedAccepted.generated_final_round_all_pushes]
  simp [dataOps, pushesEq]

theorem literal_final_round_program :
    finalRoundProgram finalNonce generatedCommitmentAt =
      ByteLayout.program.drop 447 := by
  unfold finalRoundProgram
  rw [literal_data_ops]
  exact List.take_append_drop 302 (ByteLayout.program.drop 447) |>.trans
    (by simp)

/-- Surviving positions identify both byte pools after the same erasures.
The commitment map may vary by setup; dummy signatures remain fixed here. -/
structure AlignedPool (commitmentAt : Fin 150 → Bytes)
    (ids : List (Fin 150)) (dummies commitments : List Bytes) : Prop where
  dummyMap : dummies = ids.map generatedDummyAt
  commitmentMap : commitments = ids.map commitmentAt

theorem initial_alignment (commitmentAt : Fin 150 → Bytes) :
    AlignedPool commitmentAt (List.finRange 150)
      finalDummyPool (commitmentPool commitmentAt) := by
  constructor
  · exact FinalSignedLoop.generated_initial_pool_alignment.dummyMap
  · rfl

theorem paired_erasure_preserves_alignment
    (commitmentAt : Fin 150 → Bytes)
    (ids : List (Fin 150)) (dummies commitments : List Bytes)
    (aligned : AlignedPool commitmentAt ids dummies commitments)
    (j : Nat) :
    AlignedPool commitmentAt (ids.eraseIdx j)
      (dummies.eraseIdx j) (commitments.eraseIdx j) := by
  rcases aligned with ⟨dummyMap, commitmentMap⟩
  constructor
  · rw [dummyMap, List.eraseIdx_map]
  · rw [commitmentMap, List.eraseIdx_map]

theorem initial_pool_shape (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20) :
    PoolShape [] finalDummyPool (commitmentPool commitmentAt) := by
  refine ⟨?_, ?_, ?_, generated_dummy_pool_width, ?_⟩
  · simp [generated_dummy_pool_length]
  · simp [commitmentPool, generated_dummy_pool_length]
  · simp
  · intro x hx
    obtain ⟨i, _present, rfl⟩ := List.mem_map.mp hx
    exact width i

/-- Any completed parameterized final-round execution reaches the exact
aligned data block before its signed selections. The later selection and
signature checks are deliberately not inferred from this prefix theorem. -/
theorem accepted_final_round_init (hashes : Hashes) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (stack : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (finalRoundProgram nonce commitmentAt)
      (State.mk stack outcomes cost) = some final) :
    ∃ afterData : State,
      run hashes (dataOps nonce commitmentAt)
        (State.mk stack outcomes cost) = some afterData ∧
      afterData = State.mk (nonce :: [] ::
        finalDummyPool ++ commitmentPool commitmentAt ++ stack)
          outcomes cost ∧
      PoolShape [] finalDummyPool (commitmentPool commitmentAt) ∧
      AlignedPool commitmentAt (List.finRange 150)
        finalDummyPool (commitmentPool commitmentAt) := by
  unfold finalRoundProgram at accepted
  rw [run_append] at accepted
  cases reached : run hashes (dataOps nonce commitmentAt)
      (State.mk stack outcomes cost) with
  | none => simp [reached] at accepted
  | some afterData =>
      exact ⟨afterData, rfl,
        accepted_data_shape hashes nonce commitmentAt
          stack outcomes cost afterData reached,
        initial_pool_shape commitmentAt width,
        initial_alignment commitmentAt⟩

end QSB.DynamicFinalInit
