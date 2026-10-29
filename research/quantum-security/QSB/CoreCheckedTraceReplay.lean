import QSB.CoreTraceSimulation

/-!
An executable certificate checker for one finite checked source-model lock
trace. A supplied frame names the state and optional signature result after
one opcode; `replay` checks each frame against `CoreCheckedStep.step` and the
post-step stack limit. This replaces a global `LocalBridge` premise with
finite, checkable source-model transitions for one run.

The current pinned `libbitcoinconsensus` adapter reports validity and an
error code, not opcode states or signature records. Even if a separate native
instrumentation emitted such frames, authenticating their Core origin and
refining Core's hashes, key parser, sighash, ECDSA, and scriptSig handoff would
remain external. No compiled-Core equivalence follows from this checker.
-/
namespace QSB.CoreCheckedTraceReplay
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- One claimed post-opcode source state and signature-site record. -/
structure Frame where
  after : CoreCheckedStep.State
  record : Option Bool
  deriving Repr

/-- Validate one supplied frame per opcode, including the post-step 1000-cell
limit, and return the final source state and ordered signature records. -/
def replay (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA) :
    List Op → CoreCheckedStep.State → List Frame →
      Option (CoreCheckedStep.State × List Bool)
  | [], s, [] => some (s, [])
  | op :: rest, s, frame :: frames =>
      if CoreCheckedStep.step hashes script validKey verify op s =
          some (frame.after, frame.record) then
        if frame.after.stack.length > 1000 then none
        else do
          let (final, later) ← replay hashes script validKey verify
            rest frame.after frames
          some (final, frame.record.toList ++ later)
      else none
  | _, _, _ => none

/-- A successful finite replay is exactly a checked source-model run with the
same final state and ordered signature-site results. -/
theorem replay_sound (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool) (verify : CoreChecksigEval.VerifyECDSA) :
    ∀ (ops : List Op) (initial : CoreCheckedStep.State)
      (frames : List Frame) (final : CoreCheckedStep.State)
      (records : List Bool),
      replay hashes script validKey verify ops initial frames =
        some (final, records) →
      CoreCheckedStep.run hashes script validKey verify ops initial =
        some (final, records)
  | [], initial, frames, final, records, success => by
      cases frames with
      | nil =>
          simp [replay] at success
          rcases success with ⟨rfl, rfl⟩
          rfl
      | cons _ _ => simp [replay] at success
  | op :: rest, initial, frames, final, records, success => by
      cases frames with
      | nil => simp [replay] at success
      | cons frame laterFrames =>
          by_cases transition : CoreCheckedStep.step hashes script validKey
              verify op initial = some (frame.after, frame.record)
          · by_cases large : frame.after.stack.length > 1000
            · simp [replay, transition, large] at success
            · cases tail : replay hashes script validKey verify rest
                frame.after laterFrames with
              | none => simp [replay, transition, large, tail] at success
              | some pair =>
                  obtain ⟨after, later⟩ := pair
                  have output : final = after ∧
                      records = frame.record.toList ++ later := by
                    simpa [replay, transition, large, tail] using success.symm
                  rcases output with ⟨rfl, rfl⟩
                  have sourceTail := replay_sound hashes script validKey verify
                    rest frame.after laterFrames final later tail
                  simp [CoreCheckedStep.run, transition, large, sourceTail]
          · simp [replay, transition] at success

/-- Exact supplied bytes, a source-model scriptSig handoff, and a verified
finite trace provide the source acceptance predicate used by the reduction.
The trace's claimed Core origin is not established by this theorem. -/
theorem sourceAccepted_of_replay
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (validTx : SighashAllWire.valid attempt.tx)
    (wireMatched : CoreCheckedWire.matchesWire attempt.supplied lock = true)
    (frames : List Frame) (final : CoreCheckedStep.State)
    (records : List Bool)
    (checked : replay (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.wire lock) validKey
      (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa)
      (DynamicCheckedCertificate.program lock)
      ⟨attempt.stack.reverse, 0⟩ frames = some (final, records))
    (truth : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    DynamicSourceGame.sourceAccepted functions lock validKey ecdsa
      attempt := by
  refine ⟨validTx, wireMatched, final, records, ?_, truth⟩
  change CoreCheckedWire.run (JointSourceChecks.hashes functions) lock
    attempt.supplied attempt.stack validKey
    (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa) =
      some (final, records)
  rw [CoreCheckedWire.run_eq_model (JointSourceChecks.hashes functions)
    lock attempt.supplied wireMatched firstWidth secondWidth pinShort
    nonce0Short nonce1Short attempt.stack validKey
    (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa)]
  exact replay_sound (JointSourceChecks.hashes functions)
    (DynamicCheckedCertificate.wire lock) validKey
    (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa)
    (DynamicCheckedCertificate.program lock) ⟨attempt.stack.reverse, 0⟩
    frames final records checked

end QSB.CoreCheckedTraceReplay
