import QSB.CoreStructuralRun
import QSB.CoreMultisigSourceScan
import QSB.CoreFinalChecksigEval
import QSB.FinalSignedChain
import QSB.CoreFinalTruth
import QSB.FinalBonusIndices
import QSB.FinalRoundWitness

/-!
Source-shaped execution of one BASE lock opcode with signature outcomes
computed at the reached stack. The four CHECKSIGVERIFY sites use the complete
Core push serialization before the DER gate; CHECKMULTISIG deletes every
reached signature push before its ordered scan. The returned Boolean is a
record of a signature site, not an input to this step.

This is still a Lean model. The key parser and ECDSA/transaction checker are
external, and no theorem here identifies this function with compiled Core.
The 880-opcode FindAndDelete fuel is for the Config A lock only.
-/
namespace QSB.CoreCheckedStep
open ByteMachine
set_option maxRecDepth 5000
set_option maxHeartbeats 10000000

structure State where
  stack : List Bytes  -- bottom first, as in Core's vector
  ops : Nat
  deriving DecidableEq, Repr

def checkedChecksig (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s : State) : Option State := do
  if s.ops + 1 > 201 then none else
  let top := s.stack.reverse
  let key ← top[0]?
  let sig ← top[1]?
  if CoreChecksigEval.evalBaseVerifyAllCore 880 script sig key
      validKey verify != some true then none else
  let next ← CoreChecksigStep.step ⟨s.stack, [true], s.ops⟩
  some ⟨next.stack, next.ops⟩

def checkedMultisig (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s : State) : Option (State × Bool) := do
  if s.ops + 1 > 201 then none else
  let n ← CoreMultisigCleanup.parseSourceCount s.stack 1
  if n < 0 ∨ n > 20 ∨ s.ops + 1 + n.toNat > 201 then none else
  let result ← CoreMultisigSourceScan.scanAtStack script
    (CoreFinalChecksigEval.checker validKey verify) s.stack
  let next ← CoreMultisigStep.step ⟨s.stack, [result], s.ops⟩
  some (⟨next.stack, next.ops⟩, result)

def step (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (op : Op) (s : State) : Option (State × Option Bool) :=
  match op with
  | .checksigverify =>
      (checkedChecksig script validKey verify s).map
        (fun next => (next, some true))
  | .checkmultisig =>
      (checkedMultisig script validKey verify s).map
        (fun (next, result) => (next, some result))
  | _ =>
      (CoreOpcodeStep.step hashes op ⟨s.stack, [], s.ops⟩).map
        (fun next => (⟨next.stack, next.ops⟩, none))

/-- A checked source-shaped run records the signature result at each reached
signature opcode. No list of outcomes is supplied by the caller. -/
def run (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA) :
    List Op → State → Option (State × List Bool)
  | [], s => some (s, [])
  | op :: rest, s => do
      let (next, record) ← step hashes script validKey verify op s
      if next.stack.length > 1000 then none else
      let (final, later) ← run hashes script validKey verify rest next
      some (final, record.toList ++ later)

/-- The checked interpreter composes across program boundaries while
concatenating its computed signature-result records in execution order. -/
theorem run_append (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (before after : List Op) (s : State) :
    run hashes script validKey verify (before ++ after) s = (do
      let (middle, first) ← run hashes script validKey verify before s
      let (final, later) ← run hashes script validKey verify after middle
      some (final, first ++ later)) := by
  induction before generalizing s with
  | nil => simp [run]
  | cons op rest ih =>
      simp only [List.cons_append, run]
      cases hstep : step hashes script validKey verify op s with
      | none => simp
      | some pair =>
          obtain ⟨next, record⟩ := pair
          by_cases large : next.stack.length > 1000
          · simp [large]
          · simp [large]
            rw [ih next]
            cases hbefore : run hashes script validKey verify rest next with
            | none => simp
            | some pair =>
                obtain ⟨middle, first⟩ := pair
                cases hafter : run hashes script validKey verify after middle with
                | none => simp [hafter]
                | some pair =>
                    obtain ⟨final, later⟩ := pair
                    simp [hafter, List.append_assoc]

def signatureSites : List Op → Nat
  | [] => 0
  | .checksigverify :: rest => 1 + signatureSites rest
  | .checkmultisig :: rest => 1 + signatureSites rest
  | _ :: rest => signatureSites rest

def lift (s : State) (outcomes : List Bool) : CoreOpcodeStep.State :=
  ⟨s.stack, outcomes, s.ops⟩

/-- A non-signature source step is parametric in an untouched outcome tail. -/
theorem ordinary_outcome_frame (hashes : Hashes) (op : Op)
    (s : State) (tail : List Bool)
    (ordinary : CoreOpcodeStep.supported op = true) :
    CoreOpcodeStep.step hashes op (lift s tail) =
      (CoreOpcodeStep.step hashes op (lift s [])).map
        (fun next => ⟨next.stack, tail, next.ops⟩) := by
  cases s with
  | mk stack ops =>
      cases op <;> simp [CoreOpcodeStep.supported] at ordinary
      all_goals
        cases hstack : stack.reverse with
        | nil =>
            simp [CoreOpcodeStep.step, lift, hstack] <;>
              split_ifs <;> simp_all
        | cons x xs =>
            cases xs with
            | nil =>
                simp [CoreOpcodeStep.step, lift, hstack] <;>
                  split_ifs <;> simp_all
            | cons y ys =>
                simp [CoreOpcodeStep.step, lift, hstack];
                  split_ifs <;> simp_all

/-- A successful CHECKSIGVERIFY consumes exactly its leading true outcome;
the later outcome tail is not inspected. -/
theorem checksig_outcome_frame (s : State) (tail : List Bool) :
    CoreChecksigStep.step (lift s (true :: tail)) =
      (CoreChecksigStep.step (lift s [true])).map
        (fun next => ⟨next.stack, tail, next.ops⟩) := by
  cases s with
  | mk stack ops =>
      simp [CoreChecksigStep.step, lift];
        split_ifs <;> simp_all

/-- CHECKMULTISIG consumes its computed scan result and leaves any later
outcomes untouched, for either true or false. -/
theorem multisig_outcome_frame (s : State) (result : Bool)
    (tail : List Bool) :
    CoreMultisigStep.step (lift s (result :: tail)) =
      (CoreMultisigStep.step (lift s [result])).map
        (fun next => ⟨next.stack, tail, next.ops⟩) := by
  cases s with
  | mk stack ops =>
      simp [CoreMultisigStep.step, lift];
        split_ifs <;> simp_all
      cases hn : CoreMultisigCleanup.parseSourceCount stack 1 with
      | none => simp
      | some n =>
          by_cases badN : n < 0 ∨ n > 20 ∨ ops + 1 + n.toNat > 201
          · simp [badN]
          · by_cases short : stack.length < n.toNat + 2
            · simp [badN, short]
            · cases hm : CoreMultisigCleanup.parseSourceCount stack
                  (n.toNat + 2) with
              | none => simp [badN, short, hm]
              | some m =>
                  by_cases badM : m < 0 ∨ m > n
                  · simp [badN, short, hm, badM]
                  · cases hc : CoreMultisigCleanup.cleanup stack n.toNat
                        m.toNat result with
                    | none => simp [badN, short, hm, badM, hc]
                    | some cleaned =>
                        simp [badN, short, hm, badM, hc]

theorem step_record_length (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (op : Op) (s next : State) (record : Option Bool)
    (success : step hashes script validKey verify op s =
      some (next, record)) :
    record.toList.length = signatureSites [op] := by
  cases op <;> simp [step, signatureSites] at success ⊢
  case checksigverify =>
    rcases success with ⟨_, h⟩
    subst record
    rfl
  case checkmultisig =>
    rcases success with ⟨_, (⟨_, _, h⟩ | ⟨_, _, h⟩)⟩ <;>
      subst record <;> rfl
  all_goals
    rcases success with ⟨_, _, _, h⟩
    subst record
    rfl

/-- Every successful run has exactly one recorded Boolean per reached
signature opcode. In particular, the first-round false result is recorded
instead of being silently assumed true. -/
theorem run_record_length (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (ops : List Op) (initial final : State) (records : List Bool)
    (success : run hashes script validKey verify ops initial =
      some (final, records)) :
    records.length = signatureSites ops := by
  induction ops generalizing initial final records with
  | nil =>
      simp [run] at success
      rcases success with ⟨rfl, rfl⟩
      rfl
  | cons op rest ih =>
      simp only [run] at success
      cases hstep : step hashes script validKey verify op initial with
      | none => simp [hstep] at success
      | some pair =>
          obtain ⟨next, record⟩ := pair
          by_cases large : next.stack.length > 1000
          · simp [hstep, large] at success
          · cases hrest : run hashes script validKey verify rest next with
            | none => simp [hstep, large, hrest] at success
            | some tail =>
                obtain ⟨after, later⟩ := tail
                have output : final = after ∧
                    records = record.toList ++ later := by
                  simpa [hstep, large, hrest] using success.symm
                have first := step_record_length hashes script validKey
                  verify op initial next record hstep
                have remaining := ih next after later hrest
                rw [output.2, List.length_append, first, remaining]
                cases op <;> simp [signatureSites]

theorem literal_signature_sites :
    signatureSites ByteLayout.program = 6 := by decide

/-- The complete literal lock contains six checked signature sites, for
every initial stack and every successful source-shaped execution. This does
not identify the model with compiled Bitcoin Core. -/
theorem literal_run_six_records (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records)) :
    records.length = 6 := by
  rw [run_record_length hashes EncodedLayout.chunks.flatten validKey
    verify ByteLayout.program initial final records success,
    literal_signature_sites]

/-- A one-of-one multisignature with a well-formed but invalid signature
computes `false`; a later truthy push can still make the short bare script
truthy. This models Core's non-VERIFY first-round behavior without supplying
the false outcome to the interpreter. The disposable example is not QSB. -/
theorem false_multisig_result_can_continue :
    let hashes : Hashes :=
      { h160 := fun _ => List.replicate 20 0x00
        h256 := fun _ => List.replicate 32 0x00
        h160_width := by intro _; simp
        h256_width := by intro _; simp }
    let sig : Bytes :=
      [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x01, 0x01]
    let initial : State :=
      ⟨[[], sig, [0x01], [0x02], [0x01]], 0⟩
    run hashes [0xae, 0x51] (fun _ => false)
      (fun _ _ _ _ => false) [.checkmultisig, .push [0x01]] initial =
        some (⟨[[], [0x01]], 2⟩, [false]) := by
  decide

/-- A successful checked CHECKSIGVERIFY step has actual reached operands and
a true source-shaped encoding/key/ECDSA result; the structural transition on
the same stack and budget then consumes a true outcome. -/
theorem checkedChecksig_sound (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State)
    (success : checkedChecksig script validKey verify s = some next) :
    ∃ sig key,
      s.stack.reverse[0]? = some key ∧
      s.stack.reverse[1]? = some sig ∧
      CoreChecksigEval.evalBaseVerifyAllCore 880 script sig key
        validKey verify = some true ∧
      ∃ reached,
        CoreChecksigStep.step ⟨s.stack, [true], s.ops⟩ =
          some reached ∧
        next = ⟨reached.stack, reached.ops⟩ := by
  unfold checkedChecksig at success
  have budget : ¬s.ops + 1 > 201 := by
    intro tooMany
    simp [tooMany] at success
  cases keyEq : s.stack.reverse[0]? with
  | none => simp [keyEq] at success
  | some key =>
      cases sigEq : s.stack.reverse[1]? with
      | none => simp [keyEq, sigEq] at success
      | some sig =>
          by_cases checked : CoreChecksigEval.evalBaseVerifyAllCore 880
              script sig key validKey verify = some true
          · cases stepEq : CoreChecksigStep.step
                ⟨s.stack, [true], s.ops⟩ with
            | none => simp [keyEq, sigEq, stepEq] at success
            | some reached =>
                have result : next = ⟨reached.stack, reached.ops⟩ := by
                  simpa [budget, keyEq, sigEq, checked, stepEq]
                    using success.symm
                exact ⟨sig, key, rfl, rfl, checked,
                  reached, rfl, result⟩
          · simp [keyEq, sigEq, checked] at success

/-- The checker-derived CHECKSIGVERIFY transition exposes its strict-DER
signature, actual low-byte hash type, and successful key/transaction checker
call on the source-shaped FindAndDelete scriptCode. -/
theorem checkedChecksig_reached_call (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State)
    (success : checkedChecksig script validKey verify s = some next) :
    ∃ sig key hashType,
      s.stack.reverse[0]? = some key ∧
      s.stack.reverse[1]? = some sig ∧
      sig.getLast? = some hashType ∧
      DERSyntax.valid sig = true ∧
      validKey key = true ∧
      verify sig.dropLast key
        (CoreFindAndDelete.run 880 script
          (ScriptCodeSelection.directPushPattern sig)) hashType = true := by
  obtain ⟨sig, key, keyAt, sigAt, coreChecked, _reached⟩ :=
    checkedChecksig_sound script validKey verify s next success
  have checked : CoreChecksigEval.evalBaseVerifyAll 880
      script sig key validKey verify = some true := by
    rw [CoreChecksigEval.evalBaseVerifyAll_eq_core]
    exact coreChecked
  obtain ⟨hashType, last, der, keyValid, verified⟩ :=
    CoreChecksigEval.successful_base_check 880
      script sig key validKey verify checked
  exact ⟨sig, key, hashType, keyAt, sigAt, last, der,
    keyValid, verified⟩

/-- A checked multisignature step derives its Boolean from the reached
count cells, common deleted scriptCode, DER gate, and ordered key scan. The
source-shaped structural step consumes that same Boolean, even when false. -/
theorem checkedMultisig_sound (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State) (result : Bool)
    (success : checkedMultisig script validKey verify s =
      some (next, result)) :
    CoreMultisigSourceScan.scanAtStack script
      (CoreFinalChecksigEval.checker validKey verify) s.stack =
        some result ∧
    ∃ reached,
      CoreMultisigStep.step ⟨s.stack, [result], s.ops⟩ =
        some reached ∧
      next = ⟨reached.stack, reached.ops⟩ := by
  unfold checkedMultisig at success
  have budget : ¬s.ops + 1 > 201 := by
    intro tooMany
    simp [tooMany] at success
  cases countEq : CoreMultisigCleanup.parseSourceCount s.stack 1 with
  | none => simp [budget, countEq] at success
  | some n =>
    by_cases badCount : n < 0 ∨ n > 20 ∨ s.ops + 1 + n.toNat > 201
    · simp [budget, countEq, badCount] at success
    · cases scanEq : CoreMultisigSourceScan.scanAtStack script
          (CoreFinalChecksigEval.checker validKey verify) s.stack with
      | none =>
          simp [budget, countEq, scanEq] at success
      | some actual =>
          cases stepEq : CoreMultisigStep.step
              ⟨s.stack, [actual], s.ops⟩ with
          | none =>
              simp [budget, countEq, scanEq, stepEq] at success
          | some reached =>
              have pair : (next, result) =
                  (⟨reached.stack, reached.ops⟩, actual) := by
                simpa [budget, countEq, badCount, scanEq, stepEq]
                  using success.symm
              have nextEq : next = ⟨reached.stack, reached.ops⟩ :=
                (Prod.mk.inj pair).1
              have resultEq : result = actual := (Prod.mk.inj pair).2
              subst next
              subst result
              exact ⟨rfl, reached, stepEq, rfl⟩

/-- The Boolean computed by a successful checked multisignature step is the
canonical cell pushed on the final stack, even when that Boolean is false. -/
theorem checkedMultisig_final_cell (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State) (result : Bool)
    (success : checkedMultisig script validKey verify s =
      some (next, result)) :
    ∃ tail, next.stack.reverse = boolBytes result :: tail := by
  obtain ⟨_, reached, sourceStep, nextEq⟩ :=
    checkedMultisig_sound script validKey verify s next result success
  have start : (⟨s.stack, [result], s.ops⟩ : CoreOpcodeStep.State) =
      CoreOpcodeStep.ofByte ⟨s.stack.reverse, [result], s.ops⟩ := by
    cases s
    simp [CoreOpcodeStep.ofByte]
  rw [start] at sourceStep
  obtain ⟨byteAfter, byteStep, sourceAfter⟩ :=
    CoreMultisigStep.successful_source_step_refines_byte hashes
      ⟨s.stack.reverse, [result], s.ops⟩ reached sourceStep
  obtain ⟨n, m, actual, _, _, cleanup, consumed, _⟩ :=
    CoreMultisigCleanup.successful_byte_multisig_source_cells hashes
      ⟨s.stack.reverse, [result], s.ops⟩ byteAfter byteStep
  have actualEq : actual = result := by
    simp at consumed
    exact consumed.1.symm
  obtain ⟨_, shape⟩ := CoreMultisigCleanup.cleanup_success
    s.stack.reverse n.toNat m.toNat actual byteAfter.stack.reverse cleanup
  refine ⟨s.stack.reverse.drop
    (CoreMultisigStack.sourceArgumentDepth n.toNat m.toNat), ?_⟩
  have byteShape := congrArg List.reverse shape
  have nextStack : next.stack.reverse = byteAfter.stack := by
    rw [nextEq, sourceAfter]
    simp [CoreOpcodeStep.ofByte]
  rw [nextStack]
  simpa [actualEq] using byteShape

/-- A truthy top after a checked multisignature step forces the computed
source-shaped signature scan to have returned true. -/
theorem checkedMultisig_true_of_final_truth (hashes : Hashes)
    (script : Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State) (result : Bool)
    (success : checkedMultisig script validKey verify s =
      some (next, result))
    (truth : ByteMachine.finalTruth
      ⟨next.stack.reverse, [], next.ops⟩ = true) :
    result = true := by
  obtain ⟨tail, shape⟩ := checkedMultisig_final_cell hashes script
    validKey verify s next result success
  cases result <;>
    simp [ByteMachine.finalTruth, shape, boolBytes] at truth ⊢

private theorem ordinary_map_frames (hashes : Hashes) (op : Op)
    (s next : State) (record : Option Bool) (tail : List Bool)
    (ordinary : CoreOpcodeStep.supported op = true)
    (success :
      (CoreOpcodeStep.step hashes op (lift s [])).map
        (fun reached =>
          (⟨reached.stack, reached.ops⟩, none)) =
        some (next, record)) :
    CoreStructuralRun.step hashes op
      (lift s (record.toList ++ tail)) = some (lift next tail) := by
  cases hsource : CoreOpcodeStep.step hashes op (lift s []) with
  | none => simp [hsource] at success
  | some reached =>
      have output : (next, record) =
          (⟨reached.stack, reached.ops⟩, none) := by
        simpa [hsource] using success.symm
      have nextEq := (Prod.mk.inj output).1
      have recordEq := (Prod.mk.inj output).2
      subst next
      subst record
      have ordinaryStep : CoreStructuralRun.step hashes op (lift s tail) =
          CoreOpcodeStep.step hashes op (lift s tail) := by
        cases op <;> simp [CoreOpcodeStep.supported,
          CoreStructuralRun.step] at ordinary ⊢
      simp only [Option.toList_none, List.nil_append]
      rw [ordinaryStep, ordinary_outcome_frame hashes op s tail ordinary,
        hsource]
      rfl

/-- One computed signature-site record is exactly the outcome consumed by
the older structural transition. Ordinary opcodes preserve the still-future
record list. This is a Lean-to-Lean step simulation, not compiled Core. -/
theorem checked_step_frames (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (op : Op) (s next : State) (record : Option Bool)
    (success : step hashes script validKey verify op s =
      some (next, record)) (tail : List Bool) :
    CoreStructuralRun.step hashes op
      (lift s (record.toList ++ tail)) = some (lift next tail) := by
  cases op <;> simp only [step] at success
  case checksigverify =>
    cases hcheck : checkedChecksig script validKey verify s with
    | none => simp [hcheck] at success
    | some reached =>
        have pair : (next, record) = (reached, some true) := by
          simpa [hcheck] using success.symm
        have nextEq := (Prod.mk.inj pair).1
        have recordEq := (Prod.mk.inj pair).2
        subst next
        subst record
        obtain ⟨_, _, _, _, _, sourceAfter, sourceStep, resultEq⟩ :=
          checkedChecksig_sound script validKey verify s reached hcheck
        simp only [CoreStructuralRun.step, Option.toList_some,
          List.singleton_append]
        rw [checksig_outcome_frame s tail]
        change CoreChecksigStep.step (lift s [true]) =
          some sourceAfter at sourceStep
        rw [sourceStep]
        simp [lift, resultEq]
  case checkmultisig =>
    cases hcheck : checkedMultisig script validKey verify s with
    | none => simp [hcheck] at success
    | some pair =>
        obtain ⟨reached, scanResult⟩ := pair
        have output : (next, record) =
            (reached, some scanResult) := by
          simpa [hcheck] using success.symm
        have nextEq := (Prod.mk.inj output).1
        have recordEq := (Prod.mk.inj output).2
        subst next
        subst record
        obtain ⟨_, sourceAfter, sourceStep, resultEq⟩ :=
          checkedMultisig_sound script validKey verify s reached
            scanResult hcheck
        simp only [CoreStructuralRun.step, Option.toList_some,
          List.singleton_append]
        rw [multisig_outcome_frame s scanResult tail]
        change CoreMultisigStep.step (lift s [scanResult]) =
          some sourceAfter at sourceStep
        rw [sourceStep]
        simp [lift, resultEq]
  all_goals
    exact ordinary_map_frames hashes _ s next record tail
      (by rfl) (by simpa [lift] using success)

/-- Every successful checker-derived run replays in the existing structural
interpreter with precisely its recorded site results in opcode order. No
caller-supplied outcome list is needed to obtain that run. -/
theorem checked_run_frames (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (ops : List Op) (initial final : State) (records tail : List Bool)
    (success : run hashes script validKey verify ops initial =
      some (final, records)) :
    CoreStructuralRun.run hashes ops (lift initial (records ++ tail)) =
      some (lift final tail) := by
  induction ops generalizing initial final records with
  | nil =>
      simp [run] at success
      rcases success with ⟨rfl, rfl⟩
      rfl
  | cons op rest ih =>
      simp only [run] at success
      cases hstep : step hashes script validKey verify op initial with
      | none => simp [hstep] at success
      | some pair =>
          obtain ⟨next, record⟩ := pair
          by_cases large : next.stack.length > 1000
          · simp [hstep, large] at success
          · cases hrest : run hashes script validKey verify rest next with
            | none => simp [hstep, large, hrest] at success
            | some pair =>
                obtain ⟨after, later⟩ := pair
                have output : final = after ∧
                    records = record.toList ++ later := by
                  simpa [hstep, large, hrest] using success.symm
                rw [output.1, output.2]
                have first := checked_step_frames hashes script validKey
                  verify op initial next record hstep (later ++ tail)
                have remaining := ih next after later hrest
                simp only [List.append_assoc, CoreStructuralRun.run]
                rw [first]
                have within : ¬(lift next (later ++ tail)).stack.length >
                    1000 := by simpa [lift] using large
                simp [within, remaining]

/-- The checker-derived run projects to the existing top-first byte machine
with exactly the computed records before any untouched future outcome tail. -/
theorem checked_run_refines_byte_tail (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (ops : List Op) (initial final : State)
    (records tail : List Bool)
    (success : run hashes script validKey verify ops initial =
      some (final, records)) :
    ByteMachine.run hashes ops
      ⟨initial.stack.reverse, records ++ tail, initial.ops⟩ =
        some ⟨final.stack.reverse, tail, final.ops⟩ := by
  have sourceRun := checked_run_frames hashes script validKey verify
    ops initial final records tail success
  have start : lift initial (records ++ tail) =
      CoreOpcodeStep.ofByte
        ⟨initial.stack.reverse, records ++ tail, initial.ops⟩ := by
    cases initial
    simp [lift, CoreOpcodeStep.ofByte]
  rw [start] at sourceRun
  obtain ⟨byteFinal, byteRun, resultEq⟩ :=
    CoreStructuralRun.run_refines_byte hashes ops
      ⟨initial.stack.reverse, records ++ tail, initial.ops⟩
      (lift final tail) sourceRun
  have byteEq : byteFinal =
      (⟨final.stack.reverse, tail, final.ops⟩ : ByteMachine.State) := by
    have projected := congrArg
      (fun source : CoreOpcodeStep.State =>
        (⟨source.stack.reverse, source.outcomes, source.ops⟩ :
          ByteMachine.State)) resultEq
    have components : byteFinal.stack = final.stack.reverse ∧
        byteFinal.outcomes = tail ∧ byteFinal.ops = final.ops := by
      simpa [lift, CoreOpcodeStep.ofByte] using projected.symm
    cases byteFinal with
    | mk stack outcomes ops =>
        rcases components with ⟨stackEq, outcomesEq, opsEq⟩
        cases stackEq
        cases outcomesEq
        cases opsEq
        rfl
  rw [byteEq] at byteRun
  exact byteRun

/-- A complete checked run needs no caller-supplied signature outcomes:
its own computed records replay in the byte interpreter and are consumed. -/
theorem checked_run_refines_byte (hashes : Hashes) (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (ops : List Op) (initial final : State) (records : List Bool)
    (success : run hashes script validKey verify ops initial =
      some (final, records)) :
    ByteMachine.run hashes ops
      ⟨initial.stack.reverse, records, initial.ops⟩ =
        some ⟨final.stack.reverse, [], final.ops⟩ := by
  simpa using checked_run_refines_byte_tail hashes script validKey verify
    ops initial final records [] success

/-- An accepted checked run ending in CHECKMULTISIG computes a true final
scan. Its result is not a Boolean chosen by the caller. -/
theorem checked_run_ending_multisig_true (hashes : Hashes)
    (script : Bytes) (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (ops : List Op) (initial final : State) (records : List Bool)
    (success : run hashes script validKey verify
      (ops ++ [.checkmultisig]) initial = some (final, records))
    (truth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true) :
    ∃ before previous,
      run hashes script validKey verify ops initial =
        some (before, previous) ∧
      checkedMultisig script validKey verify before =
        some (final, true) ∧
      records = previous ++ [true] := by
  rw [run_append] at success
  cases hprefix : run hashes script validKey verify ops initial with
  | none => simp [hprefix] at success
  | some pair =>
      obtain ⟨before, previous⟩ := pair
      simp [hprefix] at success
      cases last : checkedMultisig script validKey verify before with
      | none => simp [run, step, last] at success
      | some pair =>
          obtain ⟨next, result⟩ := pair
          by_cases capacity : next.stack.length > 1000
          · simp [run, step, last, capacity] at success
          · have lastRun : run hashes script validKey verify
                [.checkmultisig] before = some (next, [result]) := by
              simp [run, step, last, capacity]
            rw [lastRun] at success
            have output : (final, records) =
                (next, previous ++ [result]) := by
              simpa using success.symm
            have finalEq : final = next := (Prod.mk.inj output).1
            have recordsEq : records = previous ++ [result] :=
              (Prod.mk.inj output).2
            have finalTrue := checkedMultisig_true_of_final_truth
              hashes script validKey verify before next result last
              (by simpa [finalEq] using truth)
            subst result
            subst final
            exact ⟨before, previous, rfl, last, recordsEq⟩

/-- Source-shaped CastToBool of the complete checked run's final cell agrees
with the byte model's final truth test. This is a Lean-to-Lean relation. -/
theorem literal_checked_run_final_truth (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records)) :
    CoreFinalTruth.castToBool (final.stack.getLast?.getD []) =
      ByteMachine.finalTruth ⟨final.stack.reverse, [], final.ops⟩ := by
  have sourceRun := checked_run_frames hashes EncodedLayout.chunks.flatten
    validKey verify ByteLayout.program initial final records [] success
  have start : lift initial records =
      CoreOpcodeStep.ofByte
        ⟨initial.stack.reverse, records, initial.ops⟩ := by
    cases initial
    simp [lift, CoreOpcodeStep.ofByte]
  rw [List.append_nil, start] at sourceRun
  have connected := CoreFinalTruth.source_full_run_final_truth hashes
    ⟨initial.stack.reverse, records, initial.ops⟩ (lift final []) sourceRun
  simpa [CoreFinalTruth.coreFinalTruth, lift] using connected

/-- Any truthy complete checked execution of the literal lock computes a
true final source-shaped multisignature scan at its actually reached stack.
The six signature-site results are produced by the checker, not supplied. -/
theorem literal_checked_run_final_scan_true (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ before previous,
      run hashes EncodedLayout.chunks.flatten validKey verify
        (ByteLayout.program.take 879) initial = some (before, previous) ∧
      checkedMultisig EncodedLayout.chunks.flatten validKey verify before =
        some (final, true) ∧
      records = previous ++ [true] := by
  have truth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true := by
    rw [← literal_checked_run_final_truth hashes validKey verify
      initial final records success]
    exact accepted
  have split : ByteLayout.program =
      ByteLayout.program.take 879 ++ [.checkmultisig] := by decide
  rw [split] at success
  exact checked_run_ending_multisig_true hashes
    EncodedLayout.chunks.flatten validKey verify _ initial final
    records success truth

/-- The checked final scan reads the generated ten-key, ten-signature, and
NULLDUMMY cells at its actual reached stack. The byte layout facts are
transported back through the checked-run simulation with the final true
record left as the outcome tail for the prefix. -/
theorem literal_checked_run_final_source_layout (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ before previous,
      run hashes EncodedLayout.chunks.flatten validKey verify
        (ByteLayout.program.take 879) initial = some (before, previous) ∧
      checkedMultisig EncodedLayout.chunks.flatten validKey verify before =
        some (final, true) ∧
      records = previous ++ [true] ∧
      23 ≤ before.stack.length ∧
      before.stack.reverse[0]? = some [0x0a] ∧
      before.stack.reverse[11]? = some [0x0a] ∧
      before.stack.reverse[22]? = some [] := by
  have truth : ByteMachine.finalTruth
      ⟨final.stack.reverse, [], final.ops⟩ = true := by
    rw [← literal_checked_run_final_truth hashes validKey verify
      initial final records success]
    exact accepted
  have fullByte := checked_run_refines_byte hashes
    EncodedLayout.chunks.flatten validKey verify ByteLayout.program
    initial final records success
  obtain ⟨beforeByte, bytePrefix, enough, key, sig, dummy, _⟩ :=
    CoreMultisigStack.accepted_whole_byte_run_source_layout hashes
      ⟨initial.stack.reverse, records, initial.ops⟩
      ⟨final.stack.reverse, [], final.ops⟩ fullByte truth
  obtain ⟨before, previous, checkedPrefix, checkedFinal, recorded⟩ :=
    literal_checked_run_final_scan_true hashes validKey verify
      initial final records success accepted
  have projected := checked_run_refines_byte_tail hashes
    EncodedLayout.chunks.flatten validKey verify
    (ByteLayout.program.take 879) initial before previous [true]
    checkedPrefix
  rw [recorded] at bytePrefix
  have aligned : beforeByte =
      (⟨before.stack.reverse, [true], before.ops⟩ : ByteMachine.State) :=
    Option.some.inj (bytePrefix.symm.trans projected)
  subst beforeByte
  simp only [List.reverse_reverse, List.length_reverse]
    at enough key sig dummy
  have keyTop : before.stack.reverse[0]? = some [0x0a] := by
    have h : CoreMultisigStack.stacktopNeg before.stack 1 =
        before.stack.reverse[0]? := by
      simpa using CoreMultisigStack.stacktopNeg_reverse
        before.stack.reverse 1 (by simp; omega)
    exact h.symm.trans key
  have sigTop : before.stack.reverse[11]? = some [0x0a] := by
    have h : CoreMultisigStack.stacktopNeg before.stack 12 =
        before.stack.reverse[11]? := by
      simpa using CoreMultisigStack.stacktopNeg_reverse
        before.stack.reverse 12 (by simp; omega)
    exact h.symm.trans sig
  have dummyTop : before.stack.reverse[22]? = some [] := by
    have h : CoreMultisigStack.stacktopNeg before.stack 23 =
        before.stack.reverse[22]? := by
      simpa using CoreMultisigStack.stacktopNeg_reverse
        before.stack.reverse 23 (by simp; omega)
    exact h.symm.trans dummy
  exact ⟨before, previous, checkedPrefix, checkedFinal, recorded,
    enough, keyTop, sigTop, dummyTop⟩

/-- A successful checker-derived run of the literal lock computes seven
distinct final-round HORS opening positions from the actual initial stack.
Unlike the older byte theorem, its six signature results are returned by the
source-shaped checker run. This remains a Lean source model, not Core. -/
theorem literal_checked_run_seven_openings (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records)) :
    ∃ (trace : List (Fin 150 × Bytes))
      (remainingIds : List (Fin 150)),
      FinalSignedChain.extractWholeFinal hashes
        ⟨initial.stack.reverse, records, initial.ops⟩ = some trace ∧
      FinalSignedChain.extractWholeRemaining hashes
        ⟨initial.stack.reverse, records, initial.ops⟩ =
          some remainingIds ∧
      trace.length = 7 ∧
      (trace.map Prod.fst).Nodup ∧
      (∀ p ∈ trace,
        hashes.h160 p.2 = FinalSignedLoop.generatedCommitmentAt p.1) ∧
      List.Perm (trace.map Prod.fst ++ remainingIds)
        (List.finRange 150) := by
  exact FinalSignedChain.accepted_whole_program_final_signed_openings
    hashes _ _ (checked_run_refines_byte hashes
      EncodedLayout.chunks.flatten validKey verify ByteLayout.program
      initial final records success)

/-- At the reached ten-of-ten final layout, a true generic scan equals the
specialized final evaluator. Short pushes are derived from the successful
generic scan, so no signature-length premise is supplied by the caller. -/
theorem checkedMultisig_final_ten_eval (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State)
    (keys : s.stack.reverse[0]? = some [0x0a])
    (sigs : s.stack.reverse[11]? = some [0x0a])
    (dummy : s.stack.reverse[22]? = some [])
    (enough : 23 ≤ s.stack.length)
    (success : checkedMultisig script validKey verify s =
      some (next, true)) :
    CoreMultisigEval.finalTenEval script
      (CoreFinalChecksigEval.checker validKey verify)
      s.stack.reverse = some true := by
  have scanned := (checkedMultisig_sound script validKey verify
    s next true success).1
  have short : ∀ sig ∈ CoreMultisigSourceScan.reachedSignatures
      s.stack.reverse 10 10, sig.length < 76 := by
    apply CoreMultisigSourceScan.scanAtStack_finalTen_true_all_short
      script (CoreFinalChecksigEval.checker validKey verify)
      s.stack.reverse keys sigs (by simpa using enough)
    simpa using scanned
  have sourceEq := CoreMultisigSourceScan.scanAtStack_finalTen
    script (CoreFinalChecksigEval.checker validKey verify)
    s.stack.reverse keys sigs dummy (by simpa using enough) short
  simp only [List.reverse_reverse] at sourceEq
  rw [sourceEq] at scanned
  exact scanned

/-- At the reached ten-of-ten final layout, a computed true multisignature
result exposes all ten source-addressed strict-DER successful checker pairs.
Every reached signature is short because a true ten-of-ten generic scan must
attempt and accept each nonempty strict-DER signature. -/
theorem checkedMultisig_ten_pairs (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State)
    (keys : s.stack.reverse[0]? = some [0x0a])
    (sigs : s.stack.reverse[11]? = some [0x0a])
    (dummy : s.stack.reverse[22]? = some [])
    (enough : 23 ≤ s.stack.length)
    (success : checkedMultisig script validKey verify s =
      some (next, true))
    (j : Fin 10) :
    ∃ sig key,
      CoreMultisigStack.signatureAt s.stack 10 j.val = some sig ∧
      CoreMultisigStack.keyAt s.stack j.val = some key ∧
      CoreDEREncoding.valid sig = true ∧
      CoreFinalChecksigEval.checker validKey verify sig key
        (CoreMultisigEval.deletedScript script s.stack.reverse) = true := by
  have scanned := checkedMultisig_final_ten_eval script validKey verify
    s next keys sigs dummy enough success
  simpa only [List.reverse_reverse] using
    CoreMultisigEval.finalTenEval_success_pairs
    script (CoreFinalChecksigEval.checker validKey verify)
    s.stack.reverse scanned j

/-- A truthy complete checked execution of the literal lock reaches ten
source-addressed successful final signature/key checks, all strict DER and
using one common FindAndDelete scriptCode computed from the reached stack.
This is conditional on the external checker and source-model execution. -/
theorem literal_checked_run_final_ten_pairs (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ before previous,
      run hashes EncodedLayout.chunks.flatten validKey verify
        (ByteLayout.program.take 879) initial = some (before, previous) ∧
      checkedMultisig EncodedLayout.chunks.flatten validKey verify before =
        some (final, true) ∧
      records = previous ++ [true] ∧
      ∀ j : Fin 10, ∃ sig key,
        CoreMultisigStack.signatureAt before.stack 10 j.val = some sig ∧
        CoreMultisigStack.keyAt before.stack j.val = some key ∧
        CoreDEREncoding.valid sig = true ∧
        CoreFinalChecksigEval.checker validKey verify sig key
          (CoreMultisigEval.deletedScript
            EncodedLayout.chunks.flatten before.stack.reverse) = true := by
  obtain ⟨before, previous, checkedPrefix, finalCheck, recorded,
    enough, keys, sigs, dummy⟩ :=
    literal_checked_run_final_source_layout hashes validKey verify
      initial final records success accepted
  refine ⟨before, previous, checkedPrefix, finalCheck, recorded, ?_⟩
  intro j
  exact checkedMultisig_ten_pairs EncodedLayout.chunks.flatten
    validKey verify before final keys sigs dummy
    (by simpa using enough) finalCheck j

/-- In the one literal generated lock, a truthy checked execution fixes nine
distinct second-round pool positions: seven signed openings and two bonus
dummy signatures. No separate successful final-scan or DER premise is needed;
they follow from the computed checked scan. This fixture-specific theorem does
not remove the DER-shaped commitment setup exception for other vaults. -/
theorem literal_checked_run_nine_positions (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (beforeCheck : ByteMachine.State),
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨initial.stack.reverse, records, initial.ops⟩ = some beforeCheck ∧
      beforeCheck.stack[13]? = some (FinalSignedLoop.generatedDummyAt a) ∧
      beforeCheck.stack[12]? = some (FinalSignedLoop.generatedDummyAt b) ∧
      (∀ j : Nat, j < 7 → beforeCheck.stack[j + 14]? =
        (trace.map (fun p =>
          FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?) ∧
      beforeCheck.stack[21]? = some PoolRollInvariant.finalNonce ∧
      beforeCheck.stack[22]? = some [] ∧
      trace.length = 7 ∧
      (∀ p ∈ trace,
        hashes.h160 p.2 = FinalSignedLoop.generatedCommitmentAt p.1) ∧
      a ≠ b ∧ a ∉ trace.map Prod.fst ∧ b ∉ trace.map Prod.fst ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
      FinalSignedChain.extractWholeFinal hashes
        ⟨initial.stack.reverse, records, initial.ops⟩ = some trace := by
  obtain ⟨before, previous, checkedPrefix, finalCheck, recorded,
    enough, keys, sigs, dummy⟩ :=
    literal_checked_run_final_source_layout hashes validKey verify
      initial final records success accepted
  have fullByte := checked_run_refines_byte hashes
    EncodedLayout.chunks.flatten validKey verify ByteLayout.program
    initial final records success
  have projected := checked_run_refines_byte_tail hashes
    EncodedLayout.chunks.flatten validKey verify
    (ByteLayout.program.take 879) initial before previous [true]
    checkedPrefix
  have beforeByte : ByteMachine.run hashes
      (ByteLayout.program.take 879)
      ⟨initial.stack.reverse, records, initial.ops⟩ =
        some ⟨before.stack.reverse, [true], before.ops⟩ := by
    simpa [recorded] using projected
  have finalEval := checkedMultisig_final_ten_eval
    EncodedLayout.chunks.flatten validKey verify before final
    keys sigs dummy enough finalCheck
  let pairVerify : Bytes → Bytes → Bool := fun sig key =>
    DERSyntax.verifyAllEncoding sig &&
      CoreMultisigEval.nonemptyVerify
        (CoreFinalChecksigEval.checker validKey verify)
        (CoreMultisigEval.deletedScript
          EncodedLayout.chunks.flatten before.stack.reverse) sig key
  have verifySound : ∀ sig key, pairVerify sig key = true →
      DERSyntax.valid sig = true := by
    intro sig key hit
    have strict := (CoreMultisigEval.checkedPair_der
      EncodedLayout.chunks.flatten
      (CoreFinalChecksigEval.checker validKey verify)
      before.stack.reverse sig key hit).1
    rw [CoreDEREncoding.valid_eq_model] at strict
    exact strict
  have matched : ∀ beforeCheck : ByteMachine.State,
      ByteMachine.run hashes (ByteLayout.program.take 879)
        ⟨initial.stack.reverse, records, initial.ops⟩ =
          some beforeCheck →
      Multisig.matchSigs pairVerify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true := by
    intro beforeCheck reached
    have aligned : beforeCheck =
        (⟨before.stack.reverse, [true], before.ops⟩ :
          ByteMachine.State) := Option.some.inj
      (reached.symm.trans beforeByte)
    subst beforeCheck
    have pairs := CoreMultisigEval.finalTenEval_success_match
      EncodedLayout.chunks.flatten
      (CoreFinalChecksigEval.checker validKey verify)
      before.stack.reverse finalEval
    simpa [pairVerify, FinalScriptCode.reachedSignatures] using pairs
  exact FinalBonusIndices.matched_full_run_nine_positions_der
    hashes ⟨initial.stack.reverse, records, initial.ops⟩
    ⟨final.stack.reverse, [], final.ops⟩ fullByte
    pairVerify verifySound matched

/-- The concrete byte-model witness extractor succeeds on every truthy
checked literal run and returns seven valid openings plus two disjoint bonus
positions. Its key is read from the reached final stack; transaction-level
authorization and compiled-Core refinement remain separate. -/
theorem literal_checked_run_extract_witness (hashes : Hashes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (initial final : State) (records : List Bool)
    (success : run hashes EncodedLayout.chunks.flatten validKey verify
      ByteLayout.program initial = some (final, records))
    (accepted : CoreFinalTruth.castToBool
      (final.stack.getLast?.getD []) = true) :
    ∃ w : RoundWitness (Fin 150) Bytes Bytes,
      FinalRoundWitness.extractMatchedWitness hashes
        ⟨initial.stack.reverse, records, initial.ops⟩ = some w ∧
      FinalRoundShape w ∧
      OpeningsValid hashes.h160 FinalSignedLoop.generatedCommitmentAt
        w.signed w.opening ∧
      ∃ beforeCheck : ByteMachine.State,
        ByteMachine.run hashes (ByteLayout.program.take 879)
          ⟨initial.stack.reverse, records, initial.ops⟩ =
            some beforeCheck ∧
        beforeCheck.stack[10]? = some w.key := by
  obtain ⟨trace, a, b, beforeCheck, reached, firstSlot, lastSlot,
    _signedSlots, nonceSlot, _dummySlot, seven, hits,
    _different, _aUnopened, _bUnopened, distinct, _nine,
    traceComputed⟩ := literal_checked_run_nine_positions
      hashes validKey verify initial final records success accepted
  have keyIn : 10 < beforeCheck.stack.length := by
    have nonceIn := (List.getElem?_eq_some_iff.mp nonceSlot).choose
    omega
  let key := beforeCheck.stack[10]
  have keyAt : beforeCheck.stack[10]? = some key :=
    List.getElem?_eq_getElem keyIn
  have extracted : FinalRoundWitness.extractMatchedWitness hashes
      ⟨initial.stack.reverse, records, initial.ops⟩ =
        some (FinalRoundWitness.witnessFromTrace trace a b key) := by
    simp [FinalRoundWitness.extractMatchedWitness, traceComputed,
      reached, firstSlot, lastSlot, FinalRoundWitness.findDummy_exact,
      keyAt]
  obtain ⟨shape, openings⟩ :=
    FinalRoundWitness.witnessFromTrace_shape_and_openings
      hashes trace a b key seven distinct hits
  exact ⟨FinalRoundWitness.witnessFromTrace trace a b key,
    extracted, shape, openings, beforeCheck, reached, keyAt⟩

end QSB.CoreCheckedStep
