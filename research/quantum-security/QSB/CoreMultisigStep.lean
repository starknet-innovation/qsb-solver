import QSB.CoreMultisigCleanup
import QSB.CoreOpcodeStep

/-!
A bottom-first source-shaped structural CHECKMULTISIG transition. `outcomes`
supplies the signature-scan Boolean: this module handles the source count
addresses, ScriptNum parsing, opcode budget, NULLDUMMY, and stack mutation.
Connecting that Boolean and the whole transition to compiled Core remains
separate.
-/
namespace QSB.CoreMultisigStep
open ByteMachine
set_option linter.unusedSimpArgs false

def step (s : CoreOpcodeStep.State) : Option CoreOpcodeStep.State := do
  if s.ops + 1 > 201 then none else
  let n ← CoreMultisigCleanup.parseSourceCount s.stack 1
  if n < 0 ∨ n > 20 ∨ s.ops + 1 + n.toNat > 201 then none else
  if n.toNat + 2 > s.stack.length then none else
  let m ← CoreMultisigCleanup.parseSourceCount s.stack (n.toNat + 2)
  if m < 0 ∨ m > n then none else
  let result :: rest := s.outcomes | none
  let stack ← CoreMultisigCleanup.cleanup s.stack n.toNat m.toNat result
  some ⟨stack, rest, s.ops + 1 + n.toNat⟩

/-- On any reached well-formed count/dummy cells, the source-shaped
bottom-first transition and byte-model top-first transition agree exactly,
for either supplied scan result. In particular this applies to the first
non-enforcing CHECKMULTISIG when its result is false. -/
theorem step_of_reached_cells (hashes : Hashes)
    (rawN rawM : Bytes) (xs : List Bytes)
    (n m : Int) (result : Bool) (rest : List Bool) (ops : Nat)
    (budget : ¬ ops + 1 > 201)
    (keyParsed : ByteIndex.parseScriptNum rawN = some n)
    (goodN : ¬(n < 0 ∨ n > 20 ∨ ops + 1 + n.toNat > 201))
    (sigCell : xs[n.toNat]? = some rawM)
    (sigParsed : ByteIndex.parseScriptNum rawM = some m)
    (goodM : ¬(m < 0 ∨ m > n))
    (dummy : xs[n.toNat + 1 + m.toNat]? = some []) :
    let initial : ByteMachine.State := ⟨rawN :: xs, result :: rest, ops⟩
    let final : ByteMachine.State :=
      ⟨boolBytes result :: xs.drop (n.toNat + m.toNat + 2),
        rest, ops + 1 + n.toNat⟩
    step (CoreOpcodeStep.ofByte initial) =
        some (CoreOpcodeStep.ofByte final) ∧
      ByteMachine.step hashes .checkmultisig initial = some final := by
  have cells := CoreMultisigCleanup.source_cells_from_byte_cells
    rawN rawM xs n m result keyParsed sigCell sigParsed dummy
  have sigIndex : n.toNat < xs.length :=
    (List.getElem?_eq_some_iff.mp sigCell).choose
  constructor
  · have c1 : CoreMultisigCleanup.parseSourceCount
        (xs.reverse ++ [rawN]) 1 = some n := by
      simpa only [List.reverse_cons] using cells.1
    have c2 : CoreMultisigCleanup.parseSourceCount
        (xs.reverse ++ [rawN]) (n.toNat + 2) = some m := by
      simpa only [List.reverse_cons] using cells.2.1
    have c3 : CoreMultisigCleanup.cleanup
        (xs.reverse ++ [rawN]) n.toNat m.toNat result =
        some ((boolBytes result :: xs.drop (n.toNat + m.toNat + 2)).reverse) := by
      simpa only [List.reverse_cons] using cells.2.2.2
    unfold step CoreOpcodeStep.ofByte
    simp [budget, c1, c2, goodN, goodM, c3, sigIndex]
  · unfold ByteMachine.step
    simp [budget, keyParsed, goodN, sigCell, sigParsed, goodM,
      dummy]

/-- A successful source-shaped structural step projects to a successful
byte-model step with the same stack, supplied scan Boolean, outcomes tail,
and opcode count. This is the direction needed for lock extraction once
compiled Core is refined to this source step. -/
theorem successful_source_step_refines_byte (hashes : Hashes)
    (before : ByteMachine.State) (after : CoreOpcodeStep.State)
    (source : step (CoreOpcodeStep.ofByte before) = some after) :
    ∃ byteAfter : ByteMachine.State,
      ByteMachine.step hashes .checkmultisig before = some byteAfter ∧
      after = CoreOpcodeStep.ofByte byteAfter := by
  cases before with
  | mk stack outcomes ops =>
    cases stack with
    | nil =>
      simp [step, CoreOpcodeStep.ofByte,
        CoreMultisigCleanup.parseSourceCount,
        CoreMultisigStack.stacktopNeg] at source
    | cons rawN xs =>
      have firstRead : CoreMultisigCleanup.parseSourceCount
          (rawN :: xs).reverse 1 = ByteIndex.parseScriptNum rawN := by
        rw [CoreMultisigCleanup.parseSourceCount_reverse
          (rawN :: xs) 1 (by omega) (by simp)]
        rfl
      simp only [List.reverse_cons] at firstRead
      by_cases budget : ops + 1 > 201
      · simp [step, CoreOpcodeStep.ofByte, budget] at source
      · cases keyParsed : ByteIndex.parseScriptNum rawN with
        | none =>
          simp [step, CoreOpcodeStep.ofByte, budget,
            firstRead, keyParsed] at source
        | some n =>
          by_cases badN : n < 0 ∨ n > 20 ∨ ops + 1 + n.toNat > 201
          · simp [step, CoreOpcodeStep.ofByte, budget,
              firstRead, keyParsed, badN] at source
          · by_cases enoughSig : n.toNat + 2 ≤ (rawN :: xs).length
            · have secondRead : CoreMultisigCleanup.parseSourceCount
                  (rawN :: xs).reverse (n.toNat + 2) =
                  (xs[n.toNat]?).bind ByteIndex.parseScriptNum := by
                rw [CoreMultisigCleanup.parseSourceCount_reverse
                  (rawN :: xs) (n.toNat + 2) (by omega) enoughSig]
                simp
              simp only [List.reverse_cons] at secondRead
              cases sigCell : xs[n.toNat]? with
              | none =>
                  simp [step, CoreOpcodeStep.ofByte, budget,
                    firstRead, keyParsed, badN, enoughSig,
                    secondRead, sigCell] at source
              | some rawM =>
                cases sigParsed : ByteIndex.parseScriptNum rawM with
                | none =>
                    simp [step, CoreOpcodeStep.ofByte, budget,
                      firstRead, keyParsed, badN, enoughSig,
                      secondRead, sigCell, sigParsed] at source
                | some m =>
                  by_cases badM : m < 0 ∨ m > n
                  · simp [step, CoreOpcodeStep.ofByte, budget,
                      firstRead, keyParsed, badN, enoughSig,
                      secondRead, sigCell, sigParsed, badM]
                      at source
                  · cases outcomes with
                    | nil =>
                        simp [step, CoreOpcodeStep.ofByte, budget,
                          firstRead, keyParsed, badN, enoughSig,
                          secondRead, sigCell, sigParsed, badM]
                          at source
                    | cons result rest =>
                      cases cleaned : CoreMultisigCleanup.cleanup
                          (rawN :: xs).reverse n.toNat m.toNat result with
                      | none =>
                          simp only [List.reverse_cons] at cleaned
                          simp [step, CoreOpcodeStep.ofByte, budget,
                            firstRead, keyParsed, badN, enoughSig,
                            secondRead, sigCell, sigParsed, badM,
                            cleaned] at source
                      | some cleanedStack =>
                        simp only [List.reverse_cons] at cleaned
                        obtain ⟨dummyAt, cleanedShape⟩ :=
                          CoreMultisigCleanup.cleanup_success
                            (rawN :: xs) n.toNat m.toNat result
                            cleanedStack (by simpa only [List.reverse_cons] using cleaned)
                        have dummy : xs[n.toNat + 1 + m.toNat]? =
                            some [] := by
                          simpa [CoreMultisigStack.sourceArgumentDepth,
                            Nat.add_assoc, Nat.add_comm,
                            Nat.add_left_comm] using dummyAt
                        have both := step_of_reached_cells hashes rawN rawM
                          xs n m result rest ops budget keyParsed badN
                          sigCell sigParsed badM dummy
                        let byteAfter : ByteMachine.State :=
                          ⟨boolBytes result :: xs.drop (n.toNat + m.toNat + 2),
                            rest, ops + 1 + n.toNat⟩
                        have sourceAfter : after =
                            CoreOpcodeStep.ofByte byteAfter := by
                          have h := source
                          simp [step, CoreOpcodeStep.ofByte, budget,
                            firstRead, keyParsed, badN, enoughSig,
                            secondRead, sigCell, sigParsed, badM,
                            cleaned] at h
                          simpa [byteAfter, CoreOpcodeStep.ofByte,
                            cleanedShape,
                            CoreMultisigStack.sourceArgumentDepth,
                            Nat.add_assoc, Nat.add_comm,
                            Nat.add_left_comm] using h.2.symm
                        exact ⟨byteAfter, both.2, sourceAfter⟩
            · have tooShort : ¬n.toNat < xs.length := by
                simp only [List.length_cons] at enoughSig
                omega
              simp [step, CoreOpcodeStep.ofByte, budget,
                firstRead, keyParsed, badN] at source
              exact (tooShort source.1).elim

end QSB.CoreMultisigStep
