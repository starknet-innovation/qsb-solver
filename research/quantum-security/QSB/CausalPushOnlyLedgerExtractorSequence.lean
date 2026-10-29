import QSB.ClassicalMachineSequence
import QSB.CausalLedgerExtractorSequence
import QSB.PushOnlyLedgerRawCacheMachine

/-!
Compose a first-stage classical H/R transcript/context machine with the
fixed-ledger raw cache specialized to the source-level push-only scriptSig
evaluator. The scriptSig contract is fixed by definition, and the submitted
raw transaction is the first stage's transcript output. If the first stage
halts within `q` requests, the combined run has its exact result and ordered
log within `q + 1295` explicit classical H/R requests.

The push-only evaluator can represent the pinned builder's push-only witness
grammar, but this module does not prove the builder-byte bridge or compiled
Bitcoin Core correspondence. A source world must separately match the
context, output, and evaluator; arbitrary attacker scriptSigs, hidden callback
work, oracle-independent initial setup, timeout fallback, and coherent QROM
accounting remain outside these theorems.
-/
namespace QSB.CausalPushOnlyLedgerExtractorSequence
open ByteMachine (Bytes)
open CausalQueryAlgorithm (Query Machine Transcript run)

/-- The first stage supplies source context. Its scriptSig evaluator is fixed
to `PushOnlyScriptSig.contract` by `fixedInput` below. -/
structure Context where
  lock : DynamicCheckedCertificate.Lock
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool
  ledger : Game.Outpoint → Game.Output
  target : Game.Outpoint

abbrev RawTranscript :=
  Transcript (Fin 150) LedgerBoundRawSource.Submission

abbrev FirstOutput := RawTranscript × Context

/-- The transcript chooses the submitted raw bytes; the context cannot
replace them or choose a different scriptSig contract. -/
def fixedInput (t : RawTranscript) (ctx : Context) :
    LedgerBoundRawCacheMachine.FixedInput where
  contract := PushOnlyScriptSig.contract
  lock := ctx.lock
  validKey := ctx.validKey
  ecdsa := ctx.ecdsa
  ledger := ctx.ledger
  target := ctx.target
  submission := t.output

theorem submission_eq_output (t : RawTranscript) (ctx : Context) :
    (fixedInput t ctx).submission = t.output := rfl

theorem contract_eq_pushOnly (t : RawTranscript) (ctx : Context) :
    (fixedInput t ctx).contract = PushOnlyScriptSig.contract := rfl

/-- The generic ledger machine on this fixed input is the concrete push-only
ledger machine. -/
theorem pushOnly_machine_eq (t : RawTranscript) (ctx : Context) :
    LedgerBoundRawCacheMachine.machine (fixedInput t ctx) =
      PushOnlyLedgerRawCacheMachine.machine ctx.lock ctx.validKey
        ctx.ecdsa ctx.ledger ctx.target t.output := by
  simp [fixedInput, PushOnlyLedgerRawCacheMachine.machine,
    PushOnlyLedgerRawCacheMachine.fixedInput]

theorem pushOnly_result_eq (t : RawTranscript) (ctx : Context)
    (functions : JointSourceChecks.Functions) :
    LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx) functions =
      PushOnlyLedgerRawCacheMachine.ledgerResult functions ctx.lock
        ctx.validKey ctx.ecdsa ctx.ledger ctx.target t.output := by
  simp [LedgerBoundRawCacheMachine.ledgerResult, fixedInput,
    PushOnlyLedgerRawCacheMachine.ledgerResult, PushOnlyScriptSig.contract]

variable {S : Type*}

/-- First run the transcript/context producer, then start the push-only
ledger cache from an empty response cache in the same H/R world. -/
def machine (first : Machine S FirstOutput) :=
  ClassicalMachineSequence.sequence first
    (fun tc => LedgerBoundRawCacheMachine.machine (fixedInput tc.1 tc.2))
    (fun _ => ([] : CheckedRunCacheMachine.Cache))

/-- Under first-stage termination, the combined result and ordered log are
exactly the first stage followed by the push-only ledger-bound extractor. -/
theorem run_q_plus_1295_exact
    (first : Machine S FirstOutput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial =
      (some (t, ctx), firstLog)) :
    run (machine first) functions (q + 1295) (.inl initial) =
      (some ((t, ctx),
        LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx)
          functions),
        firstLog ++
          (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
            functions 1295 ([] : CheckedRunCacheMachine.Cache)).2) := by
  have pushOnly := PushOnlyLedgerRawCacheMachine.run_1295_correct
    ctx.lock ctx.validKey ctx.ecdsa ctx.ledger ctx.target t.output
    functions
  have secondHalt :
      run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
          functions 1295 ([] : CheckedRunCacheMachine.Cache) =
        (some (LedgerBoundRawCacheMachine.ledgerResult
          (fixedInput t ctx) functions),
          (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
            functions 1295 ([] : CheckedRunCacheMachine.Cache)).2) := by
    rw [pushOnly_machine_eq t ctx, pushOnly_result_eq t ctx functions]
    exact Prod.ext pushOnly.1 rfl
  exact ClassicalMachineSequence.run_sequence first
    (fun tc => LedgerBoundRawCacheMachine.machine (fixedInput tc.1 tc.2))
    (fun _ => ([] : CheckedRunCacheMachine.Cache)) functions
    q initial (t, ctx) firstLog 1295
    (LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx) functions)
    (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
      functions 1295 ([] : CheckedRunCacheMachine.Cache)).2
    firstHalt secondHalt

/-- The combined exact run makes at most `q + 1295` explicit classical H/R
requests across both stages. -/
theorem run_q_plus_1295_length_le
    (first : Machine S FirstOutput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial =
      (some (t, ctx), firstLog)) :
    (run (machine first) functions (q + 1295) (.inl initial)).2.length ≤
      q + 1295 := by
  have bound := CausalQueryAlgorithm.run_length_le (machine first) functions
    (q + 1295) (.inl initial)
  simpa [run_q_plus_1295_exact first functions q initial t ctx firstLog
    firstHalt] using bound

/-- Pointwise realization of one sampled source world. The evaluator field
must equal the restricted push-only evaluator in this world; this does not
follow from the first-stage query bound. -/
structure ContextMatches {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω) (ctx : Context) : Prop where
  lock : ctx.lock = w.lock ω
  validKey : ctx.validKey = w.validKey ω
  ecdsa : ctx.ecdsa = w.ecdsa ω
  ledger : ctx.ledger = w.ledger ω
  target : ctx.target = w.target ω
  evalScriptSig : PushOnlyScriptSig.eval = w.evalScriptSig ω

/-- Under those context equations, the cache result is the same source-world
extractor applied to the transcript's submitted transaction. -/
theorem ledgerResult_eq_world {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω)
    (t : RawTranscript) (ctx : Context)
    (ctxMatches : ContextMatches w ω ctx) :
    LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx)
        (w.functions ω) =
      (JointRawSourceWorld.experiment w).extractor ω t.output := by
  change LedgerBoundRawSource.extractor (w.functions ω)
    ctx.lock ctx.validKey ctx.ecdsa
    (PushOnlyScriptSig.contract.eval (w.functions ω))
    ctx.ledger ctx.target t.output =
    LedgerBoundRawSource.extractor (w.functions ω)
      (w.lock ω) (w.validKey ω) (w.ecdsa ω)
      (w.evalScriptSig ω) (w.ledger ω) (w.target ω) t.output
  rw [ctxMatches.lock, ctxMatches.validKey, ctxMatches.ecdsa,
    ctxMatches.ledger, ctxMatches.target]
  change LedgerBoundRawSource.extractor (w.functions ω)
    (w.lock ω) (w.validKey ω) (w.ecdsa ω)
    PushOnlyScriptSig.eval (w.ledger ω) (w.target ω) t.output =
    LedgerBoundRawSource.extractor (w.functions ω)
      (w.lock ω) (w.validKey ω) (w.ecdsa ω)
      (w.evalScriptSig ω) (w.ledger ω) (w.target ω) t.output
  rw [ctxMatches.evalScriptSig]

/-- If the first stage produces the actual source-world submission and
context, the combined run returns that world's extractor result. -/
theorem run_world_result {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω)
    (first : Machine S FirstOutput)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first (w.functions ω) q initial =
      (some (t, ctx), firstLog))
    (ctxMatches : ContextMatches w ω ctx)
    (outputEq : t.output = w.output ω) :
    (run (machine first) (w.functions ω) (q + 1295)
      (.inl initial)).1 =
      some ((t, ctx),
        (JointRawSourceWorld.experiment w).extractor ω
          (w.output ω)) := by
  calc
    (run (machine first) (w.functions ω) (q + 1295)
        (.inl initial)).1 =
        some ((t, ctx), LedgerBoundRawCacheMachine.ledgerResult
          (fixedInput t ctx) (w.functions ω)) := by
      simpa using congrArg Prod.fst
        (run_q_plus_1295_exact first (w.functions ω) q initial t ctx
          firstLog firstHalt)
    _ = some ((t, ctx),
        (JointRawSourceWorld.experiment w).extractor ω
          (w.output ω)) := by
      rw [ledgerResult_eq_world w ω t ctx ctxMatches, outputEq]

end QSB.CausalPushOnlyLedgerExtractorSequence
