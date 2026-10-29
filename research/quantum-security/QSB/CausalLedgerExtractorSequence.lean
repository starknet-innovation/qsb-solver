import QSB.ClassicalMachineSequence
import QSB.FiniteBranchingInputBound
import QSB.LedgerBoundRawCacheMachine
import QSB.JointRawSourceWorld

/-!
Compose a first classical H/R machine that produces the attack transcript and
source context with the ledger-bound raw extractor cache. The submitted bytes
and selected input come from the transcript's output; selected-target binding
then derives the spent script from the supplied ledger. Failed binding is
included in the 1697-request result and costs no extractor requests.

The first stage must halt within its stated budget. Matching its context and
output to a source world is a separate, pointwise premise. An actual game must
construct that first stage from oracle-independent initial data, account for
all setup and callback work, and relate its transcript to disclosures and
releases. This module does not refine compiled Bitcoin Core or coherent QROM
queries.
-/
namespace QSB.CausalLedgerExtractorSequence
open ByteMachine (Bytes)
open CausalQueryAlgorithm (Query Machine Transcript run)

/-- The first stage supplies the source context but cannot choose a different
raw submission for the extractor. -/
structure Context where
  contract : ScriptSigBoundedCausalContract.Contract
  lock : DynamicCheckedCertificate.Lock
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool
  ledger : Game.Outpoint → Game.Output
  target : Game.Outpoint

abbrev RawTranscript :=
  Transcript (Fin 150) LedgerBoundRawSource.Submission

abbrev FirstOutput := RawTranscript × Context

/-- The ledger-bound input's submission is definitionally the transcript's
submitted transaction and selected input. -/
def fixedInput (t : RawTranscript) (ctx : Context) :
    LedgerBoundRawCacheMachine.FixedInput where
  contract := ctx.contract
  lock := ctx.lock
  validKey := ctx.validKey
  ecdsa := ctx.ecdsa
  ledger := ctx.ledger
  target := ctx.target
  submission := t.output

theorem submission_eq_output (t : RawTranscript) (ctx : Context) :
    (fixedInput t ctx).submission = t.output := rfl

variable {S : Type*}

/-- First run the transcript/context producer, then the ledger-bound cache
with a fresh response cache against the same H/R functions. -/
def machine (first : Machine S FirstOutput) :=
  ClassicalMachineSequence.sequence first
    (fun tc => LedgerBoundRawCacheMachine.machine (fixedInput tc.1 tc.2))
    (fun _ => ([] : CheckedRunCacheMachine.Cache))

/-- A halted first stage and the ledger-bound raw cache form one exact
classical run. In particular, a failed target binding is an ordinary `none`
extractor result, not a missing second-stage halt. -/
theorem run_q_plus_1697_exact
    (first : Machine S FirstOutput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial =
      (some (t, ctx), firstLog)) :
    run (machine first) functions (q + 1697) (.inl initial) =
      (some ((t, ctx),
        LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx)
          functions),
        firstLog ++
          (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
            functions 1697 ([] : CheckedRunCacheMachine.Cache)).2) := by
  have secondHalt :
      run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
          functions 1697 ([] : CheckedRunCacheMachine.Cache) =
        (some (LedgerBoundRawCacheMachine.ledgerResult
          (fixedInput t ctx) functions),
          (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
            functions 1697 ([] : CheckedRunCacheMachine.Cache)).2) :=
    Prod.ext
      (LedgerBoundRawCacheMachine.run_1697_correct
        (fixedInput t ctx) functions).1 rfl
  exact ClassicalMachineSequence.run_sequence first
    (fun tc => LedgerBoundRawCacheMachine.machine (fixedInput tc.1 tc.2))
    (fun _ => ([] : CheckedRunCacheMachine.Cache)) functions
    q initial (t, ctx) firstLog 1697
    (LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx) functions)
    (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
      functions 1697 ([] : CheckedRunCacheMachine.Cache)).2
    firstHalt secondHalt

/-- The first-stage budget and the 1697-request ledger-bound cache budget
bound the actual concatenated H/R transcript. -/
theorem run_q_plus_1697_length_le
    (first : Machine S FirstOutput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial =
      (some (t, ctx), firstLog)) :
    (run (machine first) functions (q + 1697) (.inl initial)).2.length ≤
      q + 1697 := by
  have bound := CausalQueryAlgorithm.run_length_le (machine first) functions
    (q + 1697) (.inl initial)
  simpa [run_q_plus_1697_exact first functions q initial t ctx firstLog
    firstHalt] using bound

/-- For one fixed first machine, state, and fuel, actual combined requests
have some finite input-byte width across all H/R worlds. The width is
existential and may depend on oracle advice in the fixed initial state; it
is not a uniform bound over varying first-stage machines or inputs. -/
theorem fixed_combined_machine_input_bound
    (first : Machine S FirstOutput) (q : Nat) (initial : S) :
    ∃ bound : Nat,
      ∀ functions : JointSourceChecks.Functions,
        ∀ entry ∈
          (run (machine first) functions (q + 1697)
            (.inl initial)).2,
          entry.1.input.length ≤ bound :=
  FiniteBranchingInputBound.exists_run_input_bound (machine first)
    (q + 1697) (.inl initial)

/-- Pointwise equality of the first stage's source context with the world
used by the ledger-bound source game. This is an explicit realization
obligation; it is not inferred from the first machine's query bound. -/
structure ContextMatches {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω) (ctx : Context) : Prop where
  lock : ctx.lock = w.lock ω
  validKey : ctx.validKey = w.validKey ω
  ecdsa : ctx.ecdsa = w.ecdsa ω
  ledger : ctx.ledger = w.ledger ω
  target : ctx.target = w.target ω
  evalScriptSig : ctx.contract.eval (w.functions ω) = w.evalScriptSig ω

/-- Under the pointwise context equations, the cache computes exactly the
source world's extractor on the transcript's submitted transaction. -/
theorem ledgerResult_eq_world {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω)
    (t : RawTranscript) (ctx : Context)
    (ctxMatches : ContextMatches w ω ctx) :
    LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx)
        (w.functions ω) =
      (JointRawSourceWorld.experiment w).extractor ω t.output := by
  change LedgerBoundRawSource.extractor (w.functions ω)
    ctx.lock ctx.validKey ctx.ecdsa
    (ctx.contract.eval (w.functions ω)) ctx.ledger ctx.target t.output =
    LedgerBoundRawSource.extractor (w.functions ω)
      (w.lock ω) (w.validKey ω) (w.ecdsa ω)
      (w.evalScriptSig ω) (w.ledger ω) (w.target ω) t.output
  rw [ctxMatches.lock, ctxMatches.validKey, ctxMatches.ecdsa,
    ctxMatches.ledger, ctxMatches.target, ctxMatches.evalScriptSig]

/-- If the first stage's submitted transaction and source context realize
one sampled world, the combined run's extractor output is that world's
source-game extractor on its actual submitted transaction. -/
theorem run_world_result {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω)
    (first : Machine S FirstOutput)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first (w.functions ω) q initial =
      (some (t, ctx), firstLog))
    (ctxMatches : ContextMatches w ω ctx)
    (outputEq : t.output = w.output ω) :
    (run (machine first) (w.functions ω) (q + 1697)
      (.inl initial)).1 =
      some ((t, ctx),
        (JointRawSourceWorld.experiment w).extractor ω
          (w.output ω)) := by
  calc
    (run (machine first) (w.functions ω) (q + 1697)
        (.inl initial)).1 =
        some ((t, ctx), LedgerBoundRawCacheMachine.ledgerResult
          (fixedInput t ctx) (w.functions ω)) := by
      simpa using congrArg Prod.fst
        (run_q_plus_1697_exact first (w.functions ω) q initial t ctx
          firstLog firstHalt)
    _ = some ((t, ctx),
        (JointRawSourceWorld.experiment w).extractor ω
          (w.output ω)) := by
      rw [ledgerResult_eq_world w ω t ctx ctxMatches, outputEq]

end QSB.CausalLedgerExtractorSequence
