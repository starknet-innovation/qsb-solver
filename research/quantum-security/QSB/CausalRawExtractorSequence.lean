import QSB.ClassicalMachineSequence
import QSB.WorldIndexedRawCacheMachine

/-!
Run a first classical H/R machine that returns a complete raw-extractor input,
then run the conditional raw response-cache machine on that returned input.
The combined machine uses the same oracle pair, and the theorem charges both
stages in one ordered query log. The first stage must halt within its stated
budget; no fallback behavior is asserted here.

For a security game, one fixed first-stage machine and an oracle-independent
initial state must produce the relevant lock, raw submission, checker inputs,
and scriptSig contract. The theorem below does not establish that game-level
realization, witness a concrete scriptSig evaluator, refine compiled Bitcoin
Core, or handle coherent quantum queries.
-/
namespace QSB.CausalRawExtractorSequence
open ByteMachine (Bytes)
open CausalQueryAlgorithm (Query Machine run)

variable {S : Type*}

/-- The first stage chooses `p`; the second computes its source-model raw
extractor result with a fresh response cache. -/
def machine (first : Machine S WorldIndexedRawCacheMachine.FixedInput) :=
  ClassicalMachineSequence.sequence first
    WorldIndexedRawCacheMachine.machine
    (fun _ => ([] : CheckedRunCacheMachine.Cache))

/-- A halted first stage and the conditional 1697-request raw cache yield
one combined classical run with the exact concatenated query log. -/
theorem run_q_plus_1697_exact
    (first : Machine S WorldIndexedRawCacheMachine.FixedInput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S)
    (p : WorldIndexedRawCacheMachine.FixedInput)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial = (some p, firstLog)) :
    run (machine first) functions (q + 1697) (.inl initial) =
      (some (p, WorldIndexedRawCacheMachine.rawResult p functions),
        firstLog ++
          (run (WorldIndexedRawCacheMachine.machine p) functions 1697
            ([] : CheckedRunCacheMachine.Cache)).2) := by
  have secondHalt :
      run (WorldIndexedRawCacheMachine.machine p) functions 1697
        ([] : CheckedRunCacheMachine.Cache) =
          (some (WorldIndexedRawCacheMachine.rawResult p functions),
            (run (WorldIndexedRawCacheMachine.machine p) functions 1697
              ([] : CheckedRunCacheMachine.Cache)).2) :=
    Prod.ext (WorldIndexedRawCacheMachine.run_1697_correct p functions).1
      rfl
  exact ClassicalMachineSequence.run_sequence first
    WorldIndexedRawCacheMachine.machine
    (fun _ => ([] : CheckedRunCacheMachine.Cache)) functions
    q initial p firstLog 1697
    (WorldIndexedRawCacheMachine.rawResult p functions)
    (run (WorldIndexedRawCacheMachine.machine p) functions 1697
      ([] : CheckedRunCacheMachine.Cache)).2
    firstHalt secondHalt

/-- The combined run requests at most the sum of the first-stage budget and
the conditional raw cache's 1697 requests, including raw extraction failure. -/
theorem run_q_plus_1697_length_le
    (first : Machine S WorldIndexedRawCacheMachine.FixedInput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S)
    (p : WorldIndexedRawCacheMachine.FixedInput)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial = (some p, firstLog)) :
    (run (machine first) functions (q + 1697) (.inl initial)).2.length ≤
      q + 1697 := by
  have secondHalt :
      run (WorldIndexedRawCacheMachine.machine p) functions 1697
        ([] : CheckedRunCacheMachine.Cache) =
          (some (WorldIndexedRawCacheMachine.rawResult p functions),
            (run (WorldIndexedRawCacheMachine.machine p) functions 1697
              ([] : CheckedRunCacheMachine.Cache)).2) :=
    Prod.ext (WorldIndexedRawCacheMachine.run_1697_correct p functions).1
      rfl
  have bound := ClassicalMachineSequence.run_sequence_length_le first
    WorldIndexedRawCacheMachine.machine
    (fun _ => ([] : CheckedRunCacheMachine.Cache)) functions q initial
    p firstLog 1697 (WorldIndexedRawCacheMachine.rawResult p functions)
    (run (WorldIndexedRawCacheMachine.machine p) functions 1697
      ([] : CheckedRunCacheMachine.Cache)).2 firstHalt secondHalt
  simpa [run_q_plus_1697_exact first functions q initial p firstLog firstHalt]
    using bound

end QSB.CausalRawExtractorSequence
