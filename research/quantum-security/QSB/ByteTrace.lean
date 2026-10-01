import QSB.ByteLayout

/-!
Execution-side extraction of the byte pairs consumed by OP_EQUALVERIFY. This
reads only the public starting stack and the generated locking script; it does
not look at private HORS setup state. A follow-up refinement must tie each
recorded commitment byte string to its locking-script source position and
each signature outcome to Core's byte-level checker.
-/
namespace QSB.ByteTrace
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

structure EqualPair where
  left : Bytes
  right : Bytes
  equal : left = right

structure HashOpening (hashes : Hashes) where
  opening : Bytes
  commitment : Bytes
  matched : hashes.h160 opening = commitment

def extractOpening (hashes : Hashes) (s : State) : Option (HashOpening hashes) :=
  match s.stack with
  | opening :: commitment :: _ =>
      if h : hashes.h160 opening = commitment then
        some { opening, commitment, matched := h }
      else none
  | _ => none

/-- Record the actual input and compared stack cell at a reached HASH160.
An unsuccessful comparison produces no record; a successful literal lock run
must subsequently execute the adjacent EQUALVERIFY. -/
def openingAtStep (hashes : Hashes) (op : Op) (s : State) :
    List (HashOpening hashes) :=
  match op with
  | .hash160 => (extractOpening hashes s).toList
  | _ => []

def runOpenings (hashes : Hashes) : List Op → State →
    Option (State × List (HashOpening hashes))
  | [], s => some (s, [])
  | op :: rest, s => do
      let atStep := openingAtStep hashes op s
      let s' ← step hashes op s
      if s'.stack.length > 1000 then none else do
        let (final, tail) ← runOpenings hashes rest s'
        some (final, atStep ++ tail)

/-- Recording matched hash openings does not change whether or how the byte
program executes. This holds for arbitrary initial stacks and hash functions. -/
theorem forget_openings (hashes : Hashes) (ops : List Op) (s : State) :
    (runOpenings hashes ops s).map Prod.fst = run hashes ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      simp only [runOpenings, run]
      cases hstep : step hashes op s with
      | none => simp
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large]
          · cases htail : runOpenings hashes rest next with
            | none => simp [htail, ← ih]
            | some value =>
                rcases value with ⟨final, openings⟩
                simp [large, htail, ← ih]

/-- Opening traces concatenate when a program is split at any opcode
boundary. This makes the final seven comparisons extractable by a fixed
suffix boundary once their source indices are linked to the reached stack. -/
theorem runOpenings_append (hashes : Hashes) (before after : List Op)
    (s : State) :
    runOpenings hashes (before ++ after) s =
      (runOpenings hashes before s).bind fun (middle, first) =>
        (runOpenings hashes after middle).map fun (final, second) =>
          (final, first ++ second) := by
  induction before generalizing s with
  | nil => simp [runOpenings]
  | cons op rest ih =>
      simp only [List.cons_append, runOpenings]
      cases hstep : step hashes op s with
      | none => simp
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large]
          · simp [large]
            rw [ih]
            cases hmiddle : runOpenings hashes rest next with
            | none => simp
            | some value =>
                rcases value with ⟨middle, first⟩
                cases hafter : runOpenings hashes after middle with
                | none => simp [hafter]
                | some value =>
                    rcases value with ⟨final, second⟩
                    simp [hafter, List.append_assoc]

theorem runOpenings_head_of_record (hashes : Hashes) (op : Op)
    (rest : List Op) (s final : State)
    (trace : List (HashOpening hashes)) (hit : HashOpening hashes)
    (recorded : openingAtStep hashes op s = [hit])
    (accepted : runOpenings hashes (op :: rest) s = some (final, trace)) :
    trace.head? = some hit := by
  simp only [runOpenings] at accepted
  cases hstep : step hashes op s with
  | none => simp [hstep] at accepted
  | some next =>
      by_cases large : next.stack.length > 1000
      · simp [hstep, large] at accepted
      · cases htail : runOpenings hashes rest next with
        | none => simp [hstep, large, htail] at accepted
        | some value =>
            rcases value with ⟨reached, tail⟩
            simp [hstep, large, htail, recorded] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            rfl

/-- Every successful reached HASH160/EQUALVERIFY pair contributes the actual
opening and compared commitment as the next trace record. The hash-equality
proof is obtained from execution, not supplied by the caller. -/
theorem successful_pair_records_opening (hashes : Hashes)
    (opening commitment : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (rest : List Op)
    (final : State) (trace : List (HashOpening hashes))
    (accepted : runOpenings hashes (.hash160 :: .equalverify :: rest)
      ⟨opening :: commitment :: tail, outcomes, cost⟩ =
        some (final, trace)) :
    ∃ hit : HashOpening hashes,
      hit.opening = opening ∧ hit.commitment = commitment ∧
      trace.head? = some hit := by
  have byteRun : run hashes (.hash160 :: .equalverify :: rest)
      ⟨opening :: commitment :: tail, outcomes, cost⟩ = some final := by
    have erased := forget_openings hashes
      (.hash160 :: .equalverify :: rest)
      ⟨opening :: commitment :: tail, outcomes, cost⟩
    rw [accepted] at erased
    exact erased.symm
  have matched : hashes.h160 opening = commitment :=
    ByteMachine.successful_hash_comparison hashes opening commitment
      tail outcomes cost rest (by rw [byteRun]; rfl)
  let hit : HashOpening hashes := ⟨opening, commitment, matched⟩
  have recorded : openingAtStep hashes .hash160
      ⟨opening :: commitment :: tail, outcomes, cost⟩ = [hit] := by
    simp [openingAtStep, extractOpening, matched, hit]
  exact ⟨hit, rfl, rfl,
    runOpenings_head_of_record hashes .hash160 (.equalverify :: rest)
      ⟨opening :: commitment :: tail, outcomes, cost⟩ final trace hit
      recorded accepted⟩

/-- Invert one successful traced step without assuming any witness layout. -/
theorem runOpenings_cons_success (hashes : Hashes) (op : Op)
    (rest : List Op) (s final : State)
    (trace : List (HashOpening hashes))
    (accepted : runOpenings hashes (op :: rest) s = some (final, trace)) :
    ∃ next tail,
      step hashes op s = some next ∧
      next.stack.length ≤ 1000 ∧
      runOpenings hashes rest next = some (final, tail) ∧
      trace = openingAtStep hashes op s ++ tail := by
  simp only [runOpenings] at accepted
  cases hstep : step hashes op s with
  | none => simp [hstep] at accepted
  | some next =>
      by_cases large : next.stack.length > 1000
      · simp [hstep, large] at accepted
      · cases htail : runOpenings hashes rest next with
        | none => simp [hstep, large, htail] at accepted
        | some value =>
            rcases value with ⟨reached, tail⟩
            simp [hstep, large, htail] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            exact ⟨next, tail, rfl, by omega, htail, rfl⟩

def hashesPaired : List Op → Bool
  | [] => true
  | .hash160 :: .equalverify :: rest => hashesPaired rest
  | .hash160 :: _ => false
  | _ :: rest => hashesPaired rest

def hashCount : List Op → Nat
  | [] => 0
  | .hash160 :: rest => 1 + hashCount rest
  | _ :: rest => hashCount rest

theorem literal_hashes_paired : hashesPaired ByteLayout.program = true := by
  decide

theorem literal_hash_count : hashCount ByteLayout.program = 15 := by
  decide

private theorem reached_hash_pair_has_record (hashes : Hashes)
    (rest : List Op) (s final : State)
    (trace : List (HashOpening hashes))
    (accepted : runOpenings hashes (.hash160 :: .equalverify :: rest) s =
      some (final, trace)) :
    (openingAtStep hashes .hash160 s).length = 1 := by
  have byteRun : run hashes (.hash160 :: .equalverify :: rest) s =
      some final := by
    have erased := forget_openings hashes
      (.hash160 :: .equalverify :: rest) s
    rw [accepted] at erased
    exact erased.symm
  cases s with
  | mk stack outcomes cost =>
      cases stack with
      | nil =>
          simp only [ByteMachine.run] at byteRun
          unfold ByteMachine.step at byteRun
          simp at byteRun
      | cons opening below =>
          cases below with
          | nil =>
              simp only [ByteMachine.run] at byteRun
              unfold ByteMachine.step at byteRun
              by_cases cap : cost + 1 > 201
              · simp [cap] at byteRun
              · simp [cap] at byteRun
          | cons commitment tail =>
              have hit : hashes.h160 opening = commitment :=
                ByteMachine.successful_hash_comparison hashes
                  opening commitment tail outcomes cost rest
                  (by rw [byteRun]; rfl)
              simp [openingAtStep, extractOpening, hit]

/-- A successful run of a program in which every HASH160 is immediately
checked by EQUALVERIFY records exactly one opening for each HASH160. -/
theorem runOpenings_length_of_paired (hashes : Hashes)
    (ops : List Op) (s final : State)
    (trace : List (HashOpening hashes))
    (paired : hashesPaired ops = true)
    (accepted : runOpenings hashes ops s = some (final, trace)) :
    trace.length = hashCount ops := by
  induction ops generalizing s final trace with
  | nil =>
      simp [runOpenings] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      rfl
  | cons op rest ih =>
      obtain ⟨next, tail, _, _, tailRun, traceEq⟩ :=
        runOpenings_cons_success hashes op rest s final trace accepted
      by_cases isHash : op = .hash160
      · subst op
        cases rest with
        | nil => simp [hashesPaired] at paired
        | cons following remaining =>
            cases following <;> simp [hashesPaired] at paired
            have firstLength :
                (openingAtStep hashes .hash160 s).length = 1 :=
              reached_hash_pair_has_record hashes remaining s final trace accepted
            have restPaired :
                hashesPaired (.equalverify :: remaining) = true := by
              simpa [hashesPaired] using paired
            have tailLength := ih next final tail restPaired tailRun
            simpa [traceEq, List.length_append, hashCount,
              firstLength] using tailLength
      · have restPaired : hashesPaired rest = true := by
          cases op <;> simp_all [hashesPaired]
        have noRecord : openingAtStep hashes op s = [] := by
          cases op <;> simp_all [openingAtStep]
        have sameCount : hashCount (op :: rest) = hashCount rest := by
          cases op <;> simp_all [hashCount]
        have tailLength := ih next final tail restPaired tailRun
        simpa [traceEq, noRecord, sameCount] using tailLength

theorem accepted_literal_has_fifteen_openings (hashes : Hashes)
    (s final : State) (trace : List (HashOpening hashes))
    (accepted : runOpenings hashes ByteLayout.program s =
      some (final, trace)) :
    trace.length = 15 := by
  have counted := runOpenings_length_of_paired hashes ByteLayout.program
    s final trace literal_hashes_paired accepted
  simpa [literal_hash_count] using counted

/-- Compute the last seven opening records from a terminating byte-model run.
The ordinal split is syntactic; identifying these records with the intended
final-round source positions requires a further reached-stack refinement. -/
def finalSevenOpenings (hashes : Hashes) (s : State) :
    Option (State × List (HashOpening hashes)) :=
  (runOpenings hashes ByteLayout.program s).map fun (final, trace) =>
    (final, trace.drop 8)

theorem finalSevenOpenings_length (hashes : Hashes) (s final : State)
    (seven : List (HashOpening hashes))
    (extracted : finalSevenOpenings hashes s = some (final, seven)) :
    seven.length = 7 := by
  unfold finalSevenOpenings at extracted
  cases hrun : runOpenings hashes ByteLayout.program s with
  | none => simp [hrun] at extracted
  | some value =>
      rcases value with ⟨reached, trace⟩
      simp [hrun] at extracted
      rcases extracted with ⟨rfl, rfl⟩
      have fifteen := accepted_literal_has_fifteen_openings hashes s
        reached trace hrun
      simp [List.length_drop, fifteen]

def comparedAt (op : Op) (s : State) : List EqualPair :=
  match op, s.stack with
  | .equalverify, x :: y :: _ =>
      if h : x = y then [{ left := x, right := y, equal := h }] else []
  | _, _ => []

def runCompared (hashes : Hashes) : List Op → State →
    Option (State × List EqualPair)
  | [], s => some (s, [])
  | op :: rest, s => do
      let pair := comparedAt op s
      let s' ← step hashes op s
      if s'.stack.length > 1000 then none else do
        let (final, tail) ← runCompared hashes rest s'
        some (final, pair ++ tail)

theorem forget_trace (hashes : Hashes) (ops : List Op) (s : State) :
    (runCompared hashes ops s).map Prod.fst = run hashes ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      simp only [runCompared, run]
      cases hstep : step hashes op s with
      | none => simp
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large]
          · cases htail : runCompared hashes rest next with
            | none => simp [htail, ← ih]
            | some value =>
                rcases value with ⟨final, pairs⟩
                simp [large, htail, ← ih]

end QSB.ByteTrace
