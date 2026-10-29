import QSB.JointRawSourceWorld

/-!
A local simulation interface for a Core execution trace of a Config A bare
locking script. The abstract Core state may retain program counters, altstack,
and other implementation data; `view` projects only the main stack and opcode
counter needed by `CoreCheckedStep`. Each local obligation concerns one reached
opcode. Ordinary opcodes are related to `CoreOpcodeStep`; the two signature
families are related separately to the checked source evaluator.

This module does not establish that compiled Bitcoin Core supplies such a
trace, that its parser agrees with the Lean parser, or that its ECDSA checker
equals the supplied functions. Those are explicit premises at the boundary.
-/
namespace QSB.CoreTraceSimulation
open ByteMachine
open MeasureTheory
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- A local refinement contract for one fixed lock and checker. `totalCells`
may include Core's altstack, so the source main stack need only be no longer
than that count. -/
structure LocalBridge (C : Type*) (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) where
  view : C → CoreCheckedStep.State
  totalCells : C → Nat
  mainCells_le_total : ∀ c, (view c).stack.length ≤ totalCells c
  coreStep : Op → C → Option (C × Option Bool)
  ordinary : ∀ op c next record,
    op ≠ .checksigverify → op ≠ .checkmultisig →
    coreStep op c = some (next, record) →
    record = none ∧
      CoreOpcodeStep.step hashes op
        ⟨(view c).stack, [], (view c).ops⟩ =
          some ⟨(view next).stack, [], (view next).ops⟩
  checksig : ∀ c next record,
    coreStep .checksigverify c = some (next, record) →
    record = some true ∧
      CoreCheckedStep.checkedChecksig script validKey verify (view c) =
        some (view next)
  multisig : ∀ c next record,
    coreStep .checkmultisig c = some (next, record) →
    ∃ result,
      record = some result ∧
      CoreCheckedStep.checkedMultisig script validKey verify (view c) =
        some (view next, result)

variable {C : Type*} {hashes : Hashes} {script : Bytes}
  {validKey : Bytes → Bool} {verify : CoreChecksigEval.VerifyECDSA}

/-- An abstract Core trace runner. The step relation and total-cell count
must still be connected to the compiled interpreter. -/
def runCore (bridge : LocalBridge C hashes script validKey verify) :
    List Op → C → Option (C × List Bool)
  | [], c => some (c, [])
  | op :: rest, c => do
      let (next, record) ← bridge.coreStep op c
      if bridge.totalCells next > 1000 then none else
      let (final, later) ← runCore bridge rest next
      some (final, record.toList ++ later)

/-- Each successful external ordinary or signature transition induces the
corresponding checked Lean transition. This proof uses only local cases. -/
theorem step_refines (bridge : LocalBridge C hashes script validKey verify)
    (op : Op) (c next : C) (record : Option Bool)
    (transition : bridge.coreStep op c = some (next, record)) :
    CoreCheckedStep.step hashes script validKey verify op (bridge.view c) =
      some (bridge.view next, record) := by
  by_cases hsig : op = .checksigverify
  · subst op
    obtain ⟨recordEq, checked⟩ := bridge.checksig c next record transition
    subst record
    simp [CoreCheckedStep.step, checked]
  · by_cases hmulti : op = .checkmultisig
    · subst op
      obtain ⟨result, recordEq, checked⟩ :=
        bridge.multisig c next record transition
      subst record
      simp [CoreCheckedStep.step, checked]
    · obtain ⟨recordEq, ordinary⟩ :=
        bridge.ordinary op c next record hsig hmulti transition
      subst record
      cases op <;> simp_all [CoreCheckedStep.step]

/-- Induction over an externally supplied, successful local trace gives one
complete checked-source run, including the signature-result record order. The
size premise follows from Core's total main-plus-altstack limit. -/
theorem run_refines (bridge : LocalBridge C hashes script validKey verify) :
    ∀ (ops : List Op) (initial final : C) (records : List Bool),
      runCore bridge ops initial = some (final, records) →
      CoreCheckedStep.run hashes script validKey verify ops
        (bridge.view initial) = some (bridge.view final, records)
  | [], initial, final, records, success => by
      simp [runCore] at success
      rcases success with ⟨rfl, rfl⟩
      rfl
  | op :: rest, initial, final, records, success => by
      simp only [runCore] at success
      cases hstep : bridge.coreStep op initial with
      | none => simp [hstep] at success
      | some pair =>
          obtain ⟨next, record⟩ := pair
          by_cases large : bridge.totalCells next > 1000
          · simp [hstep, large] at success
          · cases htail : runCore bridge rest next with
            | none => simp [hstep, large, htail] at success
            | some pair =>
                obtain ⟨after, later⟩ := pair
                have output : final = after ∧
                    records = record.toList ++ later := by
                  simpa [hstep, large, htail] using success.symm
                rcases output with ⟨rfl, rfl⟩
                have sourceStep := step_refines bridge op initial next
                  record hstep
                have sourceSmall :
                    ¬ (bridge.view next).stack.length > 1000 := by
                  have dominated := bridge.mainCells_le_total next
                  omega
                have sourceTail := run_refines bridge rest next final later htail
                simp [CoreCheckedStep.run, sourceStep, sourceSmall,
                  sourceTail]

/-- Exact supplied lock bytes and the modeled parser turn the local Core trace
into a checked source run. `handoff` is the separate scriptSig-stack and fresh
opcode-counter obligation. -/
theorem checkedWire_run_of_core_trace
    (lock : DynamicCheckedCertificate.Lock) (supplied : Bytes)
    (stack : List Bytes)
    (bridge : LocalBridge C hashes
      (DynamicCheckedCertificate.wire lock) validKey verify)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (wireMatched : CoreCheckedWire.matchesWire supplied lock = true)
    (initial final : C) (records : List Bool)
    (handoff : bridge.view initial = ⟨stack.reverse, 0⟩)
    (trace : runCore bridge (DynamicCheckedCertificate.program lock)
      initial = some (final, records)) :
    CoreCheckedWire.run hashes lock supplied stack validKey verify =
      some (bridge.view final, records) := by
  rw [CoreCheckedWire.run_eq_model hashes lock supplied wireMatched
    firstWidth secondWidth pinShort nonce0Short nonce1Short
    stack validKey verify]
  have modeled := run_refines bridge _ initial final records trace
  simpa [handoff] using modeled

/-- Under transaction validity and final truth, the local Core trace supplies
the checked source-game acceptance predicate. The arbitrary `validKey` and
`ecdsa` implementations remain external. -/
theorem sourceAccepted_of_core_trace
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt)
    (bridge : LocalBridge C (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.wire lock) validKey
      (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa))
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (validTx : SighashAllWire.valid attempt.tx)
    (wireMatched : CoreCheckedWire.matchesWire attempt.supplied lock = true)
    (initial final : C) (records : List Bool)
    (handoff : bridge.view initial = ⟨attempt.stack.reverse, 0⟩)
    (trace : runCore bridge (DynamicCheckedCertificate.program lock)
      initial = some (final, records))
    (truth : CoreFinalTruth.castToBool
      ((bridge.view final).stack.getLast?.getD []) = true) :
    DynamicSourceGame.sourceAccepted functions lock validKey ecdsa
      attempt := by
  refine ⟨validTx, wireMatched, bridge.view final, records, ?_, truth⟩
  change CoreCheckedWire.run (JointSourceChecks.hashes functions) lock
    attempt.supplied attempt.stack validKey
    (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa) =
      some (bridge.view final, records)
  exact checkedWire_run_of_core_trace lock attempt.supplied attempt.stack
    bridge firstWidth secondWidth pinShort nonce0Short nonce1Short
    wireMatched initial final records handoff trace

/-- A strict raw-byte parse, selected scriptSig handoff, ledger-bound spent
script, and the local lock trace jointly imply the source acceptance used by
the reduction. No one premise here claims compiled-Core correctness. -/
theorem ledger_sourceAccepted_of_core_trace
    (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (evalScriptSig : DynamicRawSource.EvalScriptSig)
    (ledger : Game.Outpoint → Game.Output)
    (target : Game.Outpoint)
    (raw : LedgerBoundRawSource.Submission)
    (bound : DynamicRawSource.RawAttempt)
    (attempt : DynamicSourceGame.Attempt)
    (bridge : LocalBridge C (JointSourceChecks.hashes functions)
      (DynamicCheckedCertificate.wire lock) validKey
      (JointSourceChecks.checker functions attempt.tx attempt.selected ecdsa))
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (boundRaw : LedgerBoundRawSource.bindRaw ledger target raw = some bound)
    (prepared : DynamicRawSource.prepare evalScriptSig bound = some attempt)
    (validTx : SighashAllWire.valid attempt.tx)
    (wireMatched : CoreCheckedWire.matchesWire attempt.supplied lock = true)
    (initial final : C) (records : List Bool)
    (handoff : bridge.view initial = ⟨attempt.stack.reverse, 0⟩)
    (trace : runCore bridge (DynamicCheckedCertificate.program lock)
      initial = some (final, records))
    (truth : CoreFinalTruth.castToBool
      ((bridge.view final).stack.getLast?.getD []) = true) :
    LedgerBoundRawSource.sourceAccepted functions lock validKey ecdsa
      evalScriptSig ledger target raw := by
  refine ⟨bound, boundRaw, attempt, prepared, ?_⟩
  exact sourceAccepted_of_core_trace functions lock validKey ecdsa
    attempt bridge firstWidth secondWidth pinShort nonce0Short nonce1Short
    validTx wireMatched initial final records handoff trace truth

/-! ### Same-world Core refinement certificate -/

/-- A local trace certificate for one externally accepted submission in one
sampled world. It packages raw-byte parsing, ledger script binding, the
scriptSig handoff, per-opcode simulation, and final truth; it does not contain
or assume source acceptance as a field. The claim that compiled Core supplies
these fields is deliberately outside this structure. -/
structure CoreTraceCertificate {Ω : Type*} (C : Type*)
    (w : JointRawSourceWorld.World Ω) (ω : Ω)
    (raw : LedgerBoundRawSource.Submission) where
  bound : DynamicRawSource.RawAttempt
  attempt : DynamicSourceGame.Attempt
  bridge : LocalBridge C (JointSourceChecks.hashes (w.functions ω))
    (DynamicCheckedCertificate.wire (w.lock ω)) (w.validKey ω)
    (JointSourceChecks.checker (w.functions ω) attempt.tx
      attempt.selected (w.ecdsa ω))
  initial : C
  final : C
  records : List Bool
  boundRaw : LedgerBoundRawSource.bindRaw (w.ledger ω) (w.target ω) raw =
    some bound
  prepared : DynamicRawSource.prepare (w.evalScriptSig ω) bound =
    some attempt
  validTx : SighashAllWire.valid attempt.tx
  wireMatched : CoreCheckedWire.matchesWire attempt.supplied (w.lock ω) = true
  handoff : bridge.view initial = ⟨attempt.stack.reverse, 0⟩
  trace : runCore bridge (DynamicCheckedCertificate.program (w.lock ω))
    initial = some (final, records)
  truth : CoreFinalTruth.castToBool
    ((bridge.view final).stack.getLast?.getD []) = true

/-- If every externally accepted selected-target submission supplies the
concrete local trace certificate in its own world, the pointwise `coreRefines`
premise follows. All four external Core obligations remain visible in the
certificate fields rather than a monolithic source-acceptance assumption. -/
theorem coreRefines_of_certificates {Ω : Type*} (C : Type*)
    (w : JointRawSourceWorld.World Ω)
    (coreAcceptedTarget : Ω → LedgerBoundRawSource.Submission → Prop)
    (firstWidth : ∀ ω i, ((w.lock ω).firstCommitment i).length = 20)
    (secondWidth : ∀ ω i, ((w.lock ω).secondCommitment i).length = 20)
    (pinShort : ∀ ω, (w.lock ω).pin.length < 76)
    (nonce0Short : ∀ ω, (w.lock ω).nonce0.length < 76)
    (nonce1Short : ∀ ω, (w.lock ω).nonce1.length < 76)
    (certify : ∀ ω raw, coreAcceptedTarget ω raw →
      CoreTraceCertificate C w ω raw) :
    ∀ ω raw, coreAcceptedTarget ω raw →
      LedgerBoundRawSource.sourceAccepted (w.functions ω) (w.lock ω)
        (w.validKey ω) (w.ecdsa ω) (w.evalScriptSig ω)
        (w.ledger ω) (w.target ω) raw := by
  intro ω raw accepted
  let cert := certify ω raw accepted
  exact ledger_sourceAccepted_of_core_trace
    (w.functions ω) (w.lock ω) (w.validKey ω) (w.ecdsa ω)
    (w.evalScriptSig ω) (w.ledger ω) (w.target ω)
    raw cert.bound cert.attempt cert.bridge
    (firstWidth ω) (secondWidth ω) (pinShort ω)
    (nonce0Short ω) (nonce1Short ω) cert.boundRaw cert.prepared
    cert.validTx cert.wireMatched cert.initial cert.final cert.records
    cert.handoff cert.trace cert.truth

/-- The original same-world probability transfer can therefore be stated
with local Core-trace certificates in place of its opaque `coreRefines`
premise. This still requires the separate joint-QROM and setup-event bounds. -/
theorem core_unauthorized_measure_bound_of_certificates
    {Ω : Type*} [MeasurableSpace Ω] (C : Type*)
    (w : JointRawSourceWorld.World Ω) (μ : Measure Ω)
    (coreAcceptedTarget : Ω → LedgerBoundRawSource.Submission → Prop)
    (certify : ∀ ω raw, coreAcceptedTarget ω raw →
      CoreTraceCertificate C w ω raw)
    (setupEq : JointRawSourceWorld.SetupMatches w)
    (firstWidth : ∀ ω i, ((w.lock ω).firstCommitment i).length = 20)
    (secondWidth : ∀ ω i, ((w.lock ω).secondCommitment i).length = 20)
    (pinShort : ∀ ω, (w.lock ω).pin.length < 76)
    (nonce0Short : ∀ ω, (w.lock ω).nonce0.length < 76)
    (nonce1Short : ∀ ω, (w.lock ω).nonce1.length < 76)
    (pinAll : ∀ ω, (w.lock ω).pin.getLast? = some 0x01)
    (nonceAll : ∀ ω, (w.lock ω).nonce1.getLast? = some 0x01)
    (honest : ∀ ω, AuthorizedRelease
      (LedgerBoundRawSource.projection (w.ledger ω))
      (w.authorized ω) (w.released ω))
    (εjoint εsetup : ENNReal)
    (jointBound : μ {ω | JointOracleReduction.jointFailure
      (JointRawSourceWorld.experiment w) ω} ≤ εjoint)
    (setupBound : μ {ω | DynamicSourceGame.badSetup (w.lock ω)} ≤ εsetup) :
    μ {ω | JointRawSourceWorld.coreUnauthorized w coreAcceptedTarget ω} ≤
      εjoint + εsetup := by
  exact JointRawSourceWorld.core_unauthorized_measure_bound w μ
    coreAcceptedTarget
    (coreRefines_of_certificates C w coreAcceptedTarget firstWidth
      secondWidth pinShort nonce0Short nonce1Short certify)
    setupEq firstWidth secondWidth pinShort nonce0Short nonce1Short
    pinAll nonceAll honest εjoint εsetup jointBound setupBound

end QSB.CoreTraceSimulation
