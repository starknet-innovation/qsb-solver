import QSB.CausalQueryAlgorithm

/-!
Sequential composition of two classical H/R query machines. The second
machine and its initial state may depend on the first machine's returned
value. Because `Machine.step` has no silent transition, a first-stage halt
inlines the second stage's first step; `resume` switches phases when that
step requests a query.

The exact log theorem requires both stages to halt within their respective
budgets. It does not specify a fallback after first-stage fuel exhaustion,
show that a supplied initial state is free of oracle advice, or connect either
machine to Bitcoin Core or a coherent quantum algorithm.
-/
namespace QSB.ClassicalMachineSequence
open ByteMachine (Bytes)
open CausalQueryAlgorithm (Query answer Machine run)

variable {S A T B : Type*}

/-- A first-stage state or a second-stage state retaining the first result. -/
abbrev State (S A T : Type*) := S ⊕ (A × T)

/-- Run the first machine, then immediately inspect the second machine when
the first halts. Both stages use the same H/R oracle pair. -/
def sequence (first : Machine S A) (second : A → Machine T B)
    (start : A → T) : Machine (State S A T) (A × B) where
  step := fun
    | .inl s =>
        match first.step s with
        | .inr query => .inr query
        | .inl a =>
            match (second a).step (start a) with
            | .inl b => .inl (a, b)
            | .inr query => .inr query
    | .inr (a, t) =>
        match (second a).step t with
        | .inl b => .inl (a, b)
        | .inr query => .inr query
  resume := fun state reply =>
    match state with
    | .inl s =>
        match first.step s with
        | .inr _ => .inl (first.resume s reply)
        | .inl a => .inr (a, (second a).resume (start a) reply)
    | .inr (a, t) => .inr (a, (second a).resume t reply)

private def withFirst (a : A)
    (result : Option B × List (Query × Bytes)) :
    Option (A × B) × List (Query × Bytes) :=
  (result.1.map (fun b => (a, b)), result.2)

private def prepend {Out : Type*} (query : Query) (reply : Bytes)
    (result : Option Out × List (Query × Bytes)) :
    Option Out × List (Query × Bytes) :=
  (result.1, (query, reply) :: result.2)

private theorem run_query (machine : Machine S A)
    (functions : JointSourceChecks.Functions) (fuel : Nat) (state : S)
    (query : Query) (asks : machine.step state = .inr query) :
    run machine functions (fuel + 1) state =
      prepend query (answer functions query)
        (run machine functions fuel
          (machine.resume state (answer functions query))) := by
  simp [run, prepend, asks]

private theorem prepend_withFirst (a : A) (query : Query) (reply : Bytes)
    (result : Option B × List (Query × Bytes)) :
    prepend query reply (withFirst a result) =
      withFirst a (prepend query reply result) := rfl

/-- In the second phase the composed machine exactly reuses the second
machine's output and query log. -/
theorem run_second (first : Machine S A) (second : A → Machine T B)
    (start : A → T) (functions : JointSourceChecks.Functions) (a : A) :
    ∀ (fuel : Nat) (t : T),
      run (sequence first second start) functions fuel (.inr (a, t)) =
        withFirst a (run (second a) functions fuel t)
  | 0, t => by
      cases hstep : (second a).step t with
      | inl b => simp [run, sequence, withFirst, hstep]
      | inr query => simp [run, sequence, withFirst, hstep]
  | fuel + 1, t => by
      cases hstep : (second a).step t with
      | inl b => simp [run, sequence, withFirst, hstep]
      | inr query =>
          have tail := run_second first second start functions a fuel
            ((second a).resume t (answer functions query))
          have seqStep : (sequence first second start).step
              (.inr (a, t)) = .inr query := by
            simp [sequence, hstep]
          have seqResume : (sequence first second start).resume
              (.inr (a, t)) (answer functions query) =
                .inr (a, (second a).resume t
                  (answer functions query)) := rfl
          calc
            run (sequence first second start) functions (fuel + 1)
                (.inr (a, t)) =
                prepend query (answer functions query)
                  (run (sequence first second start) functions fuel
                    (.inr (a, (second a).resume t
                      (answer functions query)))) := by
                        simpa [seqResume] using
                          (run_query (sequence first second start) functions
                            fuel (.inr (a, t)) query seqStep)
            _ = prepend query (answer functions query)
                  (withFirst a (run (second a) functions fuel
                    ((second a).resume t (answer functions query)))) := by
                      rw [tail]
            _ = withFirst a (run (second a) functions (fuel + 1) t) := by
                  rw [run_query (second a) functions fuel t query hstep]
                  exact prepend_withFirst a query (answer functions query) _

/-- A first-stage halt inlines the second stage without consuming a query
or a unit of query fuel. -/
theorem run_first_after_halt (first : Machine S A)
    (second : A → Machine T B) (start : A → T)
    (functions : JointSourceChecks.Functions) (s : S) (a : A)
    (halt : first.step s = .inl a) (fuel : Nat) :
    run (sequence first second start) functions fuel (.inl s) =
      withFirst a (run (second a) functions fuel (start a)) := by
  cases fuel with
  | zero =>
      cases hstep : (second a).step (start a) with
      | inl b => simp [run, sequence, withFirst, halt, hstep]
      | inr query => simp [run, sequence, withFirst, halt, hstep]
  | succ remaining =>
      cases hstep : (second a).step (start a) with
      | inl b => simp [run, sequence, withFirst, halt, hstep]
      | inr query =>
          have tail := run_second first second start functions a remaining
            ((second a).resume (start a) (answer functions query))
          have seqStep : (sequence first second start).step (.inl s) =
              .inr query := by simp [sequence, halt, hstep]
          have seqResume : (sequence first second start).resume (.inl s)
              (answer functions query) =
                .inr (a, (second a).resume (start a)
                  (answer functions query)) := by
            simp [sequence, halt]
          calc
            run (sequence first second start) functions (remaining + 1)
                (.inl s) =
                prepend query (answer functions query)
                  (run (sequence first second start) functions remaining
                    (.inr (a, (second a).resume (start a)
                      (answer functions query)))) := by
                        simpa [seqResume] using
                          (run_query (sequence first second start) functions
                            remaining (.inl s) query seqStep)
            _ = prepend query (answer functions query)
                  (withFirst a (run (second a) functions remaining
                    ((second a).resume (start a)
                      (answer functions query)))) := by rw [tail]
            _ = withFirst a
                  (run (second a) functions (remaining + 1) (start a)) := by
                    rw [run_query (second a) functions remaining (start a)
                      query hstep]
                    exact prepend_withFirst a query (answer functions query) _

/-- Once a bounded run has halted, one extra unit of query fuel changes
neither its result nor its recorded requests. -/
theorem run_succ_of_halted (machine : Machine S A)
    (functions : JointSourceChecks.Functions) :
    ∀ (fuel : Nat) (state : S) (out : A)
      (log : List (Query × Bytes)),
      run machine functions fuel state = (some out, log) →
      run machine functions (fuel + 1) state = (some out, log)
  | 0, state, out, log, halted => by
      cases hstep : machine.step state with
      | inl result =>
          have eq : result = out ∧ log = [] := by
            simpa [run, hstep] using halted
          rcases eq with ⟨rfl, rfl⟩
          simp [run, hstep]
      | inr query => simp [run, hstep] at halted
  | fuel + 1, state, out, log, halted => by
      cases hstep : machine.step state with
      | inl result =>
          have eq : result = out ∧ log = [] := by
            simpa [run, hstep] using halted
          rcases eq with ⟨rfl, rfl⟩
          simp [run, hstep]
      | inr query =>
          cases htail : run machine functions fuel
              (machine.resume state (answer functions query)) with
          | mk outcome tailLog =>
              cases outcome with
              | none => simp [run, hstep, htail] at halted
              | some result =>
                  have eq : result = out ∧
                      (query, answer functions query) :: tailLog = log := by
                    simpa [run, hstep, htail] using halted
                  rcases eq with ⟨rfl, rfl⟩
                  have tailMore := run_succ_of_halted machine functions fuel
                    (machine.resume state (answer functions query)) result
                    tailLog htail
                  rw [show fuel + 1 + 1 = (fuel + 1) + 1 by omega]
                  rw [run_query machine functions (fuel + 1) state query
                    hstep, tailMore]
                  rfl

/-- A halted run is stable under any additional query fuel. This statement
does not apply to a run that exhausted its original fuel. -/
theorem run_add_of_halted (machine : Machine S A)
    (functions : JointSourceChecks.Functions) (fuel : Nat)
    (state : S) (out : A) (log : List (Query × Bytes))
    (halted : run machine functions fuel state = (some out, log)) :
    ∀ extra, run machine functions (fuel + extra) state =
      (some out, log)
  | 0 => by simpa using halted
  | extra + 1 => by
      have stable := run_add_of_halted machine functions fuel state out log
        halted extra
      rw [Nat.add_succ]
      exact run_succ_of_halted machine functions (fuel + extra) state out log
        stable

/-- If both stages halt within their separate budgets, one composed run
halts within their sum and records exactly the concatenated query logs. -/
theorem run_sequence (first : Machine S A) (second : A → Machine T B)
    (start : A → T) (functions : JointSourceChecks.Functions) :
    ∀ (firstFuel : Nat) (s : S) (a : A)
      (firstLog : List (Query × Bytes)) (secondFuel : Nat) (b : B)
      (secondLog : List (Query × Bytes)),
      run first functions firstFuel s = (some a, firstLog) →
      run (second a) functions secondFuel (start a) =
        (some b, secondLog) →
      run (sequence first second start) functions
          (firstFuel + secondFuel) (.inl s) =
        (some (a, b), firstLog ++ secondLog)
  | 0, s, a, firstLog, secondFuel, b, secondLog, firstHalt,
      secondHalt => by
      cases hstep : first.step s with
      | inl actual =>
          have eq : actual = a ∧ firstLog = [] := by
            simpa [run, hstep] using firstHalt
          rcases eq with ⟨rfl, rfl⟩
          rw [run_first_after_halt first second start functions s actual
            hstep]
          simp [withFirst, secondHalt]
      | inr query => simp [run, hstep] at firstHalt
  | firstFuel + 1, s, a, firstLog, secondFuel, b, secondLog,
      firstHalt, secondHalt => by
      cases hstep : first.step s with
      | inl actual =>
          have eq : actual = a ∧ firstLog = [] := by
            simpa [run, hstep] using firstHalt
          rcases eq with ⟨rfl, rfl⟩
          have secondMore := run_add_of_halted (second actual) functions
            secondFuel (start actual) b secondLog secondHalt
            (firstFuel + 1)
          rw [run_first_after_halt first second start functions s actual
            hstep]
          have fuelEq : firstFuel + 1 + secondFuel =
              secondFuel + (firstFuel + 1) := by omega
          rw [fuelEq, secondMore]
          simp [withFirst]
      | inr query =>
          let next := first.resume s (answer functions query)
          cases htail : run first functions firstFuel next with
          | mk outcome tailLog =>
              cases outcome with
              | none => simp [run, hstep, next, htail] at firstHalt
              | some actual =>
                  have eq : actual = a ∧
                      (query, answer functions query) :: tailLog =
                        firstLog := by
                    simpa [run, hstep, next, htail] using firstHalt
                  rcases eq with ⟨rfl, rfl⟩
                  have tail := run_sequence first second start functions
                    firstFuel next actual tailLog secondFuel b secondLog
                    htail secondHalt
                  have seqStep : (sequence first second start).step
                      (.inl s) = .inr query := by
                    simp [sequence, hstep]
                  have seqResume : (sequence first second start).resume
                      (.inl s) (answer functions query) =
                        .inl next := by simp [sequence, hstep, next]
                  have one := run_query (sequence first second start)
                    functions (firstFuel + secondFuel) (.inl s) query seqStep
                  rw [show firstFuel + 1 + secondFuel =
                    (firstFuel + secondFuel) + 1 by omega]
                  rw [one, seqResume, tail]
                  rfl

/-- The exact concatenated log is bounded by the sum of the two budgets. -/
theorem run_sequence_length_le (first : Machine S A)
    (second : A → Machine T B) (start : A → T)
    (functions : JointSourceChecks.Functions) (firstFuel : Nat)
    (s : S) (a : A) (firstLog : List (Query × Bytes))
    (secondFuel : Nat) (b : B)
    (secondLog : List (Query × Bytes))
    (firstHalt : run first functions firstFuel s = (some a, firstLog))
    (secondHalt : run (second a) functions secondFuel (start a) =
      (some b, secondLog)) :
    (firstLog ++ secondLog).length ≤ firstFuel + secondFuel := by
  have combined := run_sequence first second start functions firstFuel s a
    firstLog secondFuel b secondLog firstHalt secondHalt
  have bound := CausalQueryAlgorithm.run_length_le
    (sequence first second start) functions (firstFuel + secondFuel)
      (.inl s)
  simpa [combined] using bound

end QSB.ClassicalMachineSequence
