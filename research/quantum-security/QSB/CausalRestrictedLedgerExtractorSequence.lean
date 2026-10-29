import QSB.ClassicalMachineSequence
import QSB.CausalLedgerExtractorSequence
import QSB.RestrictedLedgerRawCacheMachine

/-!
Compose one first-stage classical H/R machine that produces an attack
transcript and source context with the restricted ledger-bound raw cache. The
context contains an explicit proof that its scriptSig contract is the
restricted direct-push HASH160 witness. Successful first-stage termination
within `q` requests gives one exact run and concatenated log within
`q + 1297` actual classical H/R requests, including ledger-binding failure.

The restricted evaluator returns only one stack cell. A sampled source world
must separately match the context, transcript output, and restricted
scriptSig evaluator. No general QSB spend, compiled Bitcoin Core refinement,
hidden callback charge, first-stage timeout fallback, or coherent-query/QROM
bound follows.
-/
namespace QSB.CausalRestrictedLedgerExtractorSequence
open ByteMachine (Bytes)
open CausalQueryAlgorithm (Query Machine Transcript run)

/-- A first-stage source context whose scriptSig contract is explicitly the
concrete restricted witness. Other values may still contain oracle advice. -/
structure Context where
  contract : ScriptSigBoundedCausalContract.Contract
  restricted : contract = RestrictedScriptSigHash160.contract
  lock : DynamicCheckedCertificate.Lock
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool
  ledger : Game.Outpoint → Game.Output
  target : Game.Outpoint

abbrev RawTranscript :=
  Transcript (Fin 150) LedgerBoundRawSource.Submission

abbrev FirstOutput := RawTranscript × Context

/-- The only submission passed to the extractor is the first-stage
transcript's output. -/
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

/-- The proof carried by the context identifies the second-stage machine
with the concrete restricted ledger cache. -/
theorem restricted_machine_eq (t : RawTranscript) (ctx : Context) :
    LedgerBoundRawCacheMachine.machine (fixedInput t ctx) =
      RestrictedLedgerRawCacheMachine.machine ctx.lock ctx.validKey
        ctx.ecdsa ctx.ledger ctx.target t.output := by
  simp [fixedInput, RestrictedLedgerRawCacheMachine.machine,
    RestrictedLedgerRawCacheMachine.fixedInput, ctx.restricted]

theorem restricted_result_eq (t : RawTranscript) (ctx : Context)
    (functions : JointSourceChecks.Functions) :
    LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx) functions =
      RestrictedLedgerRawCacheMachine.ledgerResult functions ctx.lock
        ctx.validKey ctx.ecdsa ctx.ledger ctx.target t.output := by
  simp [LedgerBoundRawCacheMachine.ledgerResult, fixedInput,
    RestrictedLedgerRawCacheMachine.ledgerResult, ctx.restricted,
    RestrictedScriptSigHash160.contract]

variable {S : Type*}

/-- First run the transcript/context producer, then start the restricted
ledger cache from an empty response cache in the same H/R world. -/
def machine (first : Machine S FirstOutput) :=
  ClassicalMachineSequence.sequence first
    (fun tc => LedgerBoundRawCacheMachine.machine (fixedInput tc.1 tc.2))
    (fun _ => ([] : CheckedRunCacheMachine.Cache))

/-- Both stages halt under the stated first-stage halt premise; the combined
log is exactly the first log followed by the restricted ledger cache log. -/
theorem run_q_plus_1297_exact
    (first : Machine S FirstOutput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial =
      (some (t, ctx), firstLog)) :
    run (machine first) functions (q + 1297) (.inl initial) =
      (some ((t, ctx),
        LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx)
          functions),
        firstLog ++
          (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
            functions 1297 ([] : CheckedRunCacheMachine.Cache)).2) := by
  have restricted := RestrictedLedgerRawCacheMachine.run_1297_correct
    ctx.lock ctx.validKey ctx.ecdsa ctx.ledger ctx.target t.output
    functions
  have secondHalt :
      run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
          functions 1297 ([] : CheckedRunCacheMachine.Cache) =
        (some (LedgerBoundRawCacheMachine.ledgerResult
          (fixedInput t ctx) functions),
          (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
            functions 1297 ([] : CheckedRunCacheMachine.Cache)).2) := by
    rw [restricted_machine_eq t ctx, restricted_result_eq t ctx functions]
    exact Prod.ext restricted.1 rfl
  exact ClassicalMachineSequence.run_sequence first
    (fun tc => LedgerBoundRawCacheMachine.machine (fixedInput tc.1 tc.2))
    (fun _ => ([] : CheckedRunCacheMachine.Cache)) functions
    q initial (t, ctx) firstLog 1297
    (LedgerBoundRawCacheMachine.ledgerResult (fixedInput t ctx) functions)
    (run (LedgerBoundRawCacheMachine.machine (fixedInput t ctx))
      functions 1297 ([] : CheckedRunCacheMachine.Cache)).2
    firstHalt secondHalt

/-- The exact combined run has at most `q + 1297` explicit classical H/R
requests, counting both stages. -/
theorem run_q_plus_1297_length_le
    (first : Machine S FirstOutput)
    (functions : JointSourceChecks.Functions)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first functions q initial =
      (some (t, ctx), firstLog)) :
    (run (machine first) functions (q + 1297) (.inl initial)).2.length ≤
      q + 1297 := by
  have bound := CausalQueryAlgorithm.run_length_le (machine first) functions
    (q + 1297) (.inl initial)
  simpa [run_q_plus_1297_exact first functions q initial t ctx firstLog
    firstHalt] using bound

/-- Pointwise realization of a sampled source world. In particular, this
world must use the restricted evaluator at this oracle world; the first-stage
query bound alone cannot establish any of these equations. -/
structure ContextMatches {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω) (ctx : Context) : Prop where
  lock : ctx.lock = w.lock ω
  validKey : ctx.validKey = w.validKey ω
  ecdsa : ctx.ecdsa = w.ecdsa ω
  ledger : ctx.ledger = w.ledger ω
  target : ctx.target = w.target ω
  evalScriptSig : RestrictedScriptSigHash160.eval (w.functions ω) =
    w.evalScriptSig ω

/-- Under explicit context equations, the restricted cache result is exactly
the source world's ledger-bound extractor on the submitted transaction. -/
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
    ctxMatches.ledger, ctxMatches.target, ctx.restricted]
  change LedgerBoundRawSource.extractor (w.functions ω)
    (w.lock ω) (w.validKey ω) (w.ecdsa ω)
    (RestrictedScriptSigHash160.eval (w.functions ω))
    (w.ledger ω) (w.target ω) t.output =
    LedgerBoundRawSource.extractor (w.functions ω)
      (w.lock ω) (w.validKey ω) (w.ecdsa ω)
      (w.evalScriptSig ω) (w.ledger ω) (w.target ω) t.output
  rw [ctxMatches.evalScriptSig]

/-- With first-stage and context realization, the same combined run returns
the source world's extractor result on its actual submission. -/
theorem run_world_result {Ω : Type*}
    (w : JointRawSourceWorld.World Ω) (ω : Ω)
    (first : Machine S FirstOutput)
    (q : Nat) (initial : S) (t : RawTranscript) (ctx : Context)
    (firstLog : List (Query × Bytes))
    (firstHalt : run first (w.functions ω) q initial =
      (some (t, ctx), firstLog))
    (ctxMatches : ContextMatches w ω ctx)
    (outputEq : t.output = w.output ω) :
    (run (machine first) (w.functions ω) (q + 1297)
      (.inl initial)).1 =
      some ((t, ctx),
        (JointRawSourceWorld.experiment w).extractor ω
          (w.output ω)) := by
  calc
    (run (machine first) (w.functions ω) (q + 1297)
        (.inl initial)).1 =
        some ((t, ctx), LedgerBoundRawCacheMachine.ledgerResult
          (fixedInput t ctx) (w.functions ω)) := by
      simpa using congrArg Prod.fst
        (run_q_plus_1297_exact first (w.functions ω) q initial t ctx
          firstLog firstHalt)
    _ = some ((t, ctx),
        (JointRawSourceWorld.experiment w).extractor ω
          (w.output ω)) := by
      rw [ledgerResult_eq_world w ω t ctx ctxMatches, outputEq]

end QSB.CausalRestrictedLedgerExtractorSequence
