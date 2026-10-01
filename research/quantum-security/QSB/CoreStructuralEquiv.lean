import QSB.CoreStructuralRun
import QSB.ByteStackFrame

/-!
The bottom-first Core-shaped structural transition and the top-first byte
transition agree in both directions on every modeled opcode, including the
first, possibly false, and final CHECKMULTISIG sites. This is a theorem about
two Lean models with supplied signature-scan outcomes. It does not identify
those outcomes with compiled Core's DER, sighash, key parsing, or ECDSA checks.
-/
namespace QSB.CoreStructuralEquiv
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/-- A successful byte CHECKSIGVERIFY step gives the same source-shaped pop
when its supplied outcome is true. -/
theorem checksig_byte_success_to_source (hashes : Hashes)
    (before after : ByteMachine.State)
    (byte : ByteMachine.step hashes .checksigverify before = some after) :
    CoreChecksigStep.step (CoreOpcodeStep.ofByte before) =
      some (CoreOpcodeStep.ofByte after) := by
  unfold ByteMachine.step at byte
  cases before with
  | mk stack outcomes ops =>
      cases stack with
      | nil => simp at byte
      | cons pubKey xs =>
          cases xs with
          | nil => simp at byte
          | cons sig tail =>
              by_cases budget : ops + 1 > 201
              · simp [budget] at byte
              · cases outcomes with
                | nil => simp [budget] at byte
                | cons result rest =>
                    cases result with
                    | false => simp [budget] at byte
                    | true =>
                        have source := CoreChecksigStep.step_of_reached_cells
                          pubKey sig tail rest ops budget
                        have reduced :
                            (some (⟨tail, rest, ops + 1⟩ : ByteMachine.State)) =
                              some after := by
                          simpa [budget] using byte
                        have byteShape : after = ⟨tail, rest, ops + 1⟩ := by
                          exact (Option.some.inj reduced).symm
                        simpa [byteShape] using source

/-- A successful byte CHECKMULTISIG step gives the same source-shaped count,
NULLDUMMY, cleanup, outcome, and opcode-cost transition. -/
theorem multisig_byte_success_to_source (hashes : Hashes)
    (before after : ByteMachine.State)
    (byte : ByteMachine.step hashes .checkmultisig before = some after) :
    CoreMultisigStep.step (CoreOpcodeStep.ofByte before) =
      some (CoreOpcodeStep.ofByte after) := by
  unfold ByteMachine.step at byte
  cases before with
  | mk stack outcomes ops =>
      cases stack with
      | nil => simp [] at byte
      | cons rawN xs =>
          by_cases budget : ops + 1 > 201
          · simp [ budget] at byte
          · cases parsedN : ByteIndex.parseScriptNum rawN with
            | none => simp [ budget, parsedN] at byte
            | some n =>
                by_cases badN : n < 0 ∨ n > 20 ∨ ops + 1 + n.toNat > 201
                · simp [ budget, parsedN, badN] at byte
                · cases sigCell : xs[n.toNat]? with
                  | none =>
                      simp [ budget, parsedN, badN,
                        sigCell] at byte
                  | some rawM =>
                      cases parsedM : ByteIndex.parseScriptNum rawM with
                      | none =>
                          simp [ budget, parsedN, badN,
                            sigCell, parsedM] at byte
                      | some m =>
                          by_cases badM : m < 0 ∨ m > n
                          · simp [ budget, parsedN, badN,
                              sigCell, parsedM, badM] at byte
                          · cases dummyCell : xs[n.toNat + 1 + m.toNat]? with
                            | none =>
                                simp [ budget, parsedN, badN,
                                  sigCell, parsedM, badM, dummyCell] at byte
                            | some dummyValue =>
                                cases dummyValue with
                                | cons b bs =>
                                    simp [ budget, parsedN,
                                      badN, sigCell, parsedM, badM,
                                      dummyCell] at byte
                                | nil =>
                                    cases outcomes with
                                    | nil =>
                                        simp [ budget,
                                          parsedN, badN, sigCell, parsedM,
                                          badM, dummyCell] at byte
                                    | cons result rest =>
                                        have both := CoreMultisigStep.step_of_reached_cells
                                          hashes rawN rawM xs n m result rest ops
                                          budget parsedN badN sigCell parsedM
                                          badM dummyCell
                                        have same : after =
                                            ⟨boolBytes result :: xs.drop
                                              (n.toNat + m.toNat + 2), rest,
                                              ops + 1 + n.toNat⟩ :=
                                          Option.some.inj (byte.symm.trans both.2)
                                        simpa [same] using both.1

theorem step_byte_success_to_source (hashes : Hashes) (op : Op)
    (before after : ByteMachine.State)
    (byte : ByteMachine.step hashes op before = some after) :
    CoreStructuralRun.step hashes op (CoreOpcodeStep.ofByte before) =
      some (CoreOpcodeStep.ofByte after) := by
  cases op <;> simp only [CoreStructuralRun.step]
  case checksigverify =>
    exact checksig_byte_success_to_source hashes before after byte
  case checkmultisig =>
    exact multisig_byte_success_to_source hashes before after byte
  all_goals
    rw [CoreOpcodeStep.step_eq_byte hashes _ before (by rfl), byte]
    rfl

/-- Both Lean structural interpreters agree on success and failure for every
modeled opcode, for arbitrary starting cells and supplied outcomes. -/
theorem step_eq_byte (hashes : Hashes) (op : Op)
    (before : ByteMachine.State) :
    CoreStructuralRun.step hashes op (CoreOpcodeStep.ofByte before) =
      (ByteMachine.step hashes op before).map CoreOpcodeStep.ofByte := by
  cases hbyte : ByteMachine.step hashes op before with
  | some after =>
      simpa [hbyte] using
        step_byte_success_to_source hashes op before after hbyte
  | none =>
      cases hsource : CoreStructuralRun.step hashes op
          (CoreOpcodeStep.ofByte before) with
      | none => simp [hbyte]
      | some after =>
          obtain ⟨byteAfter, success, _same⟩ :=
            CoreStructuralRun.step_refines_byte hashes op before after hsource
          simp [hbyte] at success

/-- The two structural runs agree exactly, including the post-op stack guard.
This is still a Lean-to-Lean equivalence, not compiled-Core refinement. -/
theorem run_eq_byte (hashes : Hashes) (ops : List Op)
    (before : ByteMachine.State) :
    CoreStructuralRun.run hashes ops (CoreOpcodeStep.ofByte before) =
      (ByteMachine.run hashes ops before).map CoreOpcodeStep.ofByte := by
  induction ops generalizing before with
  | nil => rfl
  | cons op rest ih =>
      simp only [CoreStructuralRun.run, ByteMachine.run]
      rw [step_eq_byte hashes op before]
      cases hstep : ByteMachine.step hashes op before with
      | none => simp
      | some next =>
          simp only [hstep, Option.map_some, Option.bind_some]
          have sameLength :
              (CoreOpcodeStep.ofByte next).stack.length =
                next.stack.length := by simp [CoreOpcodeStep.ofByte]
          by_cases large : next.stack.length > 1000
          · simp [sameLength, large]
          · simp [sameLength, large, ih next]

/-- Appending lower stack cells to a successful byte run preserves the
corresponding source-shaped structural run whenever the enlarged peak remains
inside the 1000-cell post-op guard. Signature Booleans remain supplied. -/
theorem run_bottom_frame (hashes : Hashes) (ops : List Op)
    (s final : ByteMachine.State) (peak : Nat) (tail : List Bytes)
    (base : BytePrefixCapacity.runPeak hashes ops s = some (final, peak))
    (capacity : peak + tail.length ≤ 1000) :
    CoreStructuralRun.run hashes ops
      (CoreOpcodeStep.ofByte {s with stack := s.stack ++ tail}) =
      some (CoreOpcodeStep.ofByte
        {final with stack := final.stack ++ tail}) := by
  have framed := ByteStackFrame.runPeak_frame hashes ops s final peak tail
    base capacity
  have erased := BytePrefixCapacity.forget_peak hashes ops
    {s with stack := s.stack ++ tail}
  rw [framed] at erased
  rw [run_eq_byte]
  simpa using congrArg (Option.map CoreOpcodeStep.ofByte) erased.symm

/-- Exceeding the peak guard in a successful nonempty byte run also rejects
the corresponding source-shaped structural run for any lower cell values. -/
theorem run_bottom_overflow (hashes : Hashes) (ops : List Op)
    (s final : ByteMachine.State) (peak : Nat) (tail : List Bytes)
    (nonempty : ops ≠ [])
    (base : BytePrefixCapacity.runPeak hashes ops s = some (final, peak))
    (overflow : peak + tail.length > 1000) :
    CoreStructuralRun.run hashes ops
      (CoreOpcodeStep.ofByte {s with stack := s.stack ++ tail}) = none := by
  have failed := ByteStackFrame.runPeak_frame_overflow hashes ops s final
    peak tail nonempty base overflow
  have erased := BytePrefixCapacity.forget_peak hashes ops
    {s with stack := s.stack ++ tail}
  rw [failed] at erased
  rw [run_eq_byte]
  simp [← erased]

end QSB.CoreStructuralEquiv
