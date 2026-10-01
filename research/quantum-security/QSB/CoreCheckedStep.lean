import QSB.CoreStructuralRun
import QSB.CoreMultisigSourceScan
import QSB.CoreFinalChecksigEval

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

def signatureSites : List Op → Nat
  | [] => 0
  | .checksigverify :: rest => 1 + signatureSites rest
  | .checkmultisig :: rest => 1 + signatureSites rest
  | _ :: rest => signatureSites rest

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

/-- At the reached ten-of-ten final layout, a computed true multisignature
result exposes all ten source-addressed strict-DER successful checker pairs.
Short pushes are stated explicitly to connect the generic Core serializer to
the specialized final-ten evaluator; the full-lock source theorem establishes
this premise separately from its generated signature origins. -/
theorem checkedMultisig_ten_pairs (script : Bytes)
    (validKey : Bytes → Bool)
    (verify : CoreChecksigEval.VerifyECDSA)
    (s next : State)
    (keys : s.stack.reverse[0]? = some [0x0a])
    (sigs : s.stack.reverse[11]? = some [0x0a])
    (dummy : s.stack.reverse[22]? = some [])
    (enough : 23 ≤ s.stack.length)
    (short : ∀ sig ∈ CoreMultisigSourceScan.reachedSignatures
      s.stack.reverse 10 10, sig.length < 76)
    (success : checkedMultisig script validKey verify s =
      some (next, true))
    (j : Fin 10) :
    ∃ sig key,
      CoreMultisigStack.signatureAt s.stack 10 j.val = some sig ∧
      CoreMultisigStack.keyAt s.stack j.val = some key ∧
      CoreDEREncoding.valid sig = true ∧
      CoreFinalChecksigEval.checker validKey verify sig key
        (CoreMultisigEval.deletedScript script s.stack.reverse) = true := by
  have scanned := (checkedMultisig_sound script validKey verify
    s next true success).1
  have sourceEq := CoreMultisigSourceScan.scanAtStack_finalTen
    script (CoreFinalChecksigEval.checker validKey verify)
    s.stack.reverse keys sigs dummy (by simpa using enough) short
  simp only [List.reverse_reverse] at sourceEq
  rw [sourceEq] at scanned
  simpa only [List.reverse_reverse] using
    CoreMultisigEval.finalTenEval_success_pairs
    script (CoreFinalChecksigEval.checker validKey verify)
    s.stack.reverse scanned j

end QSB.CoreCheckedStep
