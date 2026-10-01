import QSB.ByteWitness

/-!
One disposable witness checks the modeled stack-capacity boundary when
arbitrary scriptSig-produced cells are placed below its normal 57-cell stack.
The hash lookup and signature outcomes are fixture values; this is a byte
interpreter differential target, not a real-lock spend or Core refinement.
-/
namespace QSB.BytePrefixCapacity
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def runPeak (hashes : Hashes) : List Op → State → Option (State × Nat)
  | [], s => some (s, s.stack.length)
  | op :: rest, s => do
      let next ← step hashes op s
      if next.stack.length > 1000 then none else do
        let (result, later) ← runPeak hashes rest next
        some (result, max next.stack.length later)

/-- Recording the maximum reached stack height does not affect execution. -/
theorem forget_peak (hashes : Hashes) (ops : List Op) (s : State) :
    (runPeak hashes ops s).map Prod.fst = run hashes ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      simp only [runPeak, run]
      cases hstep : step hashes op s with
      | none => simp
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large]
          · cases htail : runPeak hashes rest next with
            | none => simp [large, htail, ← ih]
            | some value =>
                rcases value with ⟨final, peak⟩
                simp [large, htail, ← ih]

def input (extraBottomCells : Nat) : State :=
  ⟨ByteWitness.witness ++ List.replicate extraBottomCells ([] : Bytes),
    [true, true, true, false, true, true], 0⟩

inductive Failure where
  | step (opcodeIndex : Nat)
  | capacity (opcodeIndex height : Nat)
  deriving DecidableEq, Repr

/-- Diagnostic traversal with the same step and post-step capacity guard as
`ByteMachine.run`. The error records whether an opcode itself failed or the
resulting stack exceeded Core's modeled 1000-cell limit. -/
def diagnose (hashes : Hashes) : Nat → List Op → State → Except Failure State
  | _, [], s => .ok s
  | index, op :: rest, s =>
      match step hashes op s with
      | none => .error (.step index)
      | some next =>
          if next.stack.length > 1000 then
            .error (.capacity index next.stack.length)
          else diagnose hashes (index + 1) rest next

theorem diagnose_toOption (hashes : Hashes) (index : Nat)
    (ops : List Op) (s : State) :
    (diagnose hashes index ops s).toOption = run hashes ops s := by
  induction ops generalizing index s with
  | nil => rfl
  | cons op rest ih =>
      simp only [diagnose, run]
      cases hstep : step hashes op s with
      | none => rfl
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large, Except.toOption]
          · simp [large, ih]

theorem canonical_peak :
    (runPeak ByteWitness.hashes ByteLayout.program (input 0)).map
      (fun result => (finalTruth result.1, result.2,
        result.1.stack.length)) = some (true, 615, 569) := by
  decide

/-- The extra bottom cells are outside this witness's reached roll region.
The accepted modeled path reaches exactly the 1000-cell capacity boundary. -/
theorem extra_385_at_limit :
    (runPeak ByteWitness.hashes ByteLayout.program (input 385)).map
      (fun result => (finalTruth result.1, result.2,
        result.1.stack.length)) = some (true, 1000, 954) := by
  decide

theorem extra_386_over_limit :
    runPeak ByteWitness.hashes ByteLayout.program (input 386) = none := by
  decide

theorem extra_386_capacity_failure :
    diagnose ByteWitness.hashes 0 ByteLayout.program (input 386) =
      .error (.capacity 754 1001) := by
  decide

theorem extra_386_byte_run_rejects :
    run ByteWitness.hashes ByteLayout.program (input 386) = none := by
  simpa [extra_386_capacity_failure] using
    (diagnose_toOption ByteWitness.hashes 0 ByteLayout.program
      (input 386)).symm

end QSB.BytePrefixCapacity
