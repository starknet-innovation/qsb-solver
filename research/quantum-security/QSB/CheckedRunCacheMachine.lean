import QSB.FullCheckedRunCausality

/-!
A classical response-cache machine for one fixed source-shaped checked lock
run. The machine step uses only its cached replies: it completes missing H
and R answers with fixed width-correct zeros, recomputes the source-model
dependency trace, and asks its first uncached tagged query. It returns the
checked result only when that completed trace is covered by the cache.

The 81-query termination theorem below is conditional on `TracePrefixCausal`:
the first missing query under a sound completed cache must occur in the true
source-model trace. This is a local prefix-causality obligation, not a QROM
success claim. The key parser and ECDSA functions are fixed pure inputs;
oracle work hidden in them, compiled-Core refinement, and quantum coherence
are outside this machine. Every theorem is pointwise for one fixed
`FixedInput`: a larger security game must construct its lock, transaction,
initial checked state, key validator, and ECDSA predicate independently of
the oracle or account for their own causal oracle work. The type alone does
not establish that condition.
-/
namespace QSB.CheckedRunCacheMachine
open ByteMachine
open CausalQueryAlgorithm (Query answer Machine run)

abbrev Cache := List (Query × Bytes)
abbrev Result := Option (CoreCheckedStep.State × List Bool)

structure FixedInput where
  lock : DynamicCheckedCertificate.Lock
  tx : SighashAllWire.TxFields
  selected : Nat
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool
  initial : CoreCheckedStep.State

def trace (p : FixedInput) (functions : JointSourceChecks.Functions) :
    List Query :=
  FullCheckedRunQueries.runQueries functions p.tx p.selected p.validKey
    p.ecdsa (DynamicCheckedCertificate.wire p.lock)
    (DynamicCheckedCertificate.program p.lock) p.initial

def checkedResult (p : FixedInput)
    (functions : JointSourceChecks.Functions) : Result :=
  CoreCheckedStep.run (JointSourceChecks.hashes functions)
    (DynamicCheckedCertificate.wire p.lock) p.validKey
    (JointSourceChecks.checker functions p.tx p.selected p.ecdsa)
    (DynamicCheckedCertificate.program p.lock) p.initial

/-- First recorded reply for a tagged query. The running machine asks a
query only when it has no cached reply, so reachable caches have no repeated
query keys. -/
def lookup : Cache → Query → Option Bytes
  | [], _ => none
  | (cached, reply) :: rest, q =>
      if cached = q then some reply else lookup rest q

theorem lookup_cons_self (cache : Cache) (q : Query) (reply : Bytes) :
    lookup ((q, reply) :: cache) q = some reply := by
  simp [lookup]

theorem lookup_mem {cache : Cache} {q : Query} {reply : Bytes}
    (found : lookup cache q = some reply) : (q, reply) ∈ cache := by
  induction cache with
  | nil => simp [lookup] at found
  | cons head tail ih =>
      rcases head with ⟨cached, value⟩
      by_cases same : cached = q
      · subst cached
        simp [lookup] at found
        subst reply
        simp
      · simp [lookup, same] at found
        exact List.mem_cons.mpr (Or.inr (ih found))

theorem lookup_none_iff_not_mem (cache : Cache) (q : Query) :
    lookup cache q = none ↔ q ∉ cache.map Prod.fst := by
  induction cache with
  | nil => simp [lookup]
  | cons head tail ih =>
      rcases head with ⟨cached, value⟩
      by_cases same : cached = q
      · subst cached
        simp [lookup]
      · have reverse : q ≠ cached := fun h => same h.symm
        simp [lookup, same, ih, reverse]

def width : Query → Nat
  | .H _ => 32
  | .R _ => 20

def defaultReply (q : Query) : Bytes :=
  List.replicate (width q) (0 : UInt8)

def completeAnswer (cache : Cache) (q : Query) : Bytes :=
  match lookup cache q with
  | none => defaultReply q
  | some reply =>
      if reply.length = width q then reply else defaultReply q

theorem completeAnswer_width (cache : Cache) (q : Query) :
    (completeAnswer cache q).length = width q := by
  unfold completeAnswer
  cases found : lookup cache q with
  | none => simp [defaultReply]
  | some reply =>
      by_cases valid : reply.length = width q
      · simp [valid]
      · simp [valid, defaultReply]

/-- A total width-correct pair, built entirely from cached replies and fixed
defaults. In particular, this function contains no pointer to the true
oracle used later by `CausalQueryAlgorithm.run`. -/
def completedFunctions (cache : Cache) : JointSourceChecks.Functions where
  H := fun x => completeAnswer cache (.H x)
  R := fun x => completeAnswer cache (.R x)
  H_width := by
    intro x
    exact completeAnswer_width cache (.H x)
  R_width := by
    intro x
    exact completeAnswer_width cache (.R x)

theorem answer_completed (cache : Cache) (q : Query) :
    answer (completedFunctions cache) q = completeAnswer cache q := by
  cases q <;> rfl

theorem answer_width (functions : JointSourceChecks.Functions)
    (q : Query) : (answer functions q).length = width q := by
  cases q with
  | H x => exact functions.H_width x
  | R x => exact functions.R_width x

def CacheSound (functions : JointSourceChecks.Functions)
    (cache : Cache) : Prop :=
  ∀ q reply, (q, reply) ∈ cache → reply = answer functions q

theorem complete_agrees_of_lookup
    (functions : JointSourceChecks.Functions) (cache : Cache)
    (sound : CacheSound functions cache) (q : Query) (reply : Bytes)
    (found : lookup cache q = some reply) :
    answer (completedFunctions cache) q = answer functions q := by
  have correct : reply = answer functions q :=
    sound q reply (lookup_mem found)
  have valid : reply.length = width q := by
    rw [correct]
    exact answer_width functions q
  rw [answer_completed]
  unfold completeAnswer
  rw [found]
  dsimp only
  rw [if_pos valid]
  exact correct

/-- The first query in a trace without a cached reply. Repeated queries are
covered by their first cached answer. -/
def firstMissing (cache : Cache) : List Query → Option Query
  | [] => none
  | q :: rest =>
      match lookup cache q with
      | none => some q
      | some _ => firstMissing cache rest

theorem firstMissing_some_missing (cache : Cache) (queries : List Query)
    (q : Query) (missing : firstMissing cache queries = some q) :
    lookup cache q = none := by
  induction queries with
  | nil => simp [firstMissing] at missing
  | cons head tail ih =>
      cases found : lookup cache head with
      | none =>
          simp [firstMissing, found] at missing
          cases missing
          exact found
      | some reply =>
          simp [firstMissing, found] at missing
          exact ih missing

theorem firstMissing_none_covered (cache : Cache)
    (queries : List Query) (covered : firstMissing cache queries = none) :
    ∀ q ∈ queries, ∃ reply, lookup cache q = some reply := by
  induction queries with
  | nil => simp
  | cons head tail ih =>
      cases found : lookup cache head with
      | none => simp [firstMissing, found] at covered
      | some reply =>
          have tailCovered : firstMissing cache tail = none := by
            simpa [firstMissing, found] using covered
          intro q member
          rcases List.mem_cons.mp member with same | later
          · subst q
            exact ⟨reply, found⟩
          · exact ih tailCovered q later

/-- A found missing query has an entirely cached prefix in the completed
trace. This decomposition is what the separate prefix-causality premise uses. -/
theorem firstMissing_some_prefix (cache : Cache) (queries : List Query)
    (q : Query) (missing : firstMissing cache queries = some q) :
    ∃ before after,
      queries = before ++ q :: after ∧
      (∀ x ∈ before, ∃ reply, lookup cache x = some reply) ∧
      lookup cache q = none := by
  induction queries with
  | nil => simp [firstMissing] at missing
  | cons head tail ih =>
      cases found : lookup cache head with
      | none =>
          simp [firstMissing, found] at missing
          subst q
          exact ⟨[], tail, by simp, by simp, found⟩
      | some reply =>
          have tailMissing : firstMissing cache tail = some q := by
            simpa [firstMissing, found] using missing
          obtain ⟨before, after, shape, covered, uncached⟩ :=
            ih tailMissing
          refine ⟨head :: before, after, ?_, ?_, uncached⟩
          · simp [shape]
          · intro x member
            rcases List.mem_cons.mp member with same | later
            · subst x
              exact ⟨reply, found⟩
            · exact covered x later

def machine (p : FixedInput) : Machine Cache Result where
  step := fun cache =>
    let functions := completedFunctions cache
    match firstMissing cache (trace p functions) with
    | some q => .inr q
    | none => .inl (checkedResult p functions)
  resume := fun cache reply =>
    match firstMissing cache (trace p (completedFunctions cache)) with
    | some q => (q, reply) :: cache
    | none => cache

/-- The trace-level premise needed to turn a cache lookup into a bounded
adaptive machine. It is deliberately separate from whole-run causality and
is not assumed by the definition of `machine`. -/
def TracePrefixCausal (p : FixedInput) : Prop :=
  ∀ functions functions' k,
    k < (trace p functions).length →
    (∀ q ∈ (trace p functions).take k,
      answer functions' q = answer functions q) →
    (trace p functions').take (k + 1) =
      (trace p functions).take (k + 1)

/-- Under prefix causality, a sound cache's first missing query is an input
of the true oracle's fixed checked-run dependency trace. -/
theorem firstMissing_true_mem
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (prefixCausal : TracePrefixCausal p)
    (cache : Cache) (sound : CacheSound functions cache)
    (q : Query) (missing : firstMissing cache
      (trace p (completedFunctions cache)) = some q) :
    q ∈ trace p functions := by
  obtain ⟨before, after, shape, covered, _⟩ :=
    firstMissing_some_prefix cache _ q missing
  let completed := completedFunctions cache
  have index : before.length < (trace p completed).length := by
    rw [shape]
    simp
  have takeBefore : (trace p completed).take before.length = before := by
    rw [shape]
    simp
  have agreeBefore : ∀ x ∈ (trace p completed).take before.length,
      answer functions x = answer completed x := by
    intro x member
    have inBefore : x ∈ before := by simpa [takeBefore] using member
    obtain ⟨reply, found⟩ := covered x inBefore
    exact (complete_agrees_of_lookup functions cache sound x reply found).symm
  have samePrefix := prefixCausal completed functions before.length index agreeBefore
  have prefixShape : (trace p completed).take (before.length + 1) =
      before ++ [q] := by
    rw [shape]
    simp [List.take_append]
  have qInPrefix : q ∈ (trace p functions).take (before.length + 1) := by
    rw [samePrefix, prefixShape]
    simp
  exact (List.take_sublist _ _).subset qInPrefix

structure GoodCache (p : FixedInput)
    (functions : JointSourceChecks.Functions) (cache : Cache) : Prop where
  sound : CacheSound functions cache
  nodup : (cache.map Prod.fst).Nodup
  inTrace : ∀ entry ∈ cache, entry.1 ∈ trace p functions

theorem goodCache_nil (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    GoodCache p functions [] := by
  constructor <;> simp [CacheSound]

theorem goodCache_cons
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : Cache) (good : GoodCache p functions cache)
    (q : Query) (missing : lookup cache q = none)
    (inTrace : q ∈ trace p functions) :
    GoodCache p functions ((q, answer functions q) :: cache) := by
  refine ⟨?_, ?_, ?_⟩
  · intro query reply member
    rcases List.mem_cons.mp member with same | later
    · cases same
      rfl
    · exact good.sound query reply later
  · have notMem := (lookup_none_iff_not_mem cache q).mp missing
    simp [notMem, good.nodup]
  · intro entry member
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact inTrace
    · exact good.inTrace entry later

theorem goodCache_length_le_trace
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : Cache) (good : GoodCache p functions cache) :
    cache.length ≤ (trace p functions).length := by
  have subset : (cache.map Prod.fst).toFinset ⊆
      (trace p functions).toFinset := by
    intro q member
    have inKeys : q ∈ cache.map Prod.fst := by simpa using member
    obtain ⟨entry, inCache, same⟩ := List.mem_map.mp inKeys
    have inTrue := good.inTrace entry inCache
    simpa [same] using inTrue
  calc
    cache.length = (cache.map Prod.fst).length := by simp
    _ = (cache.map Prod.fst).toFinset.card :=
      (List.toFinset_card_of_nodup good.nodup).symm
    _ ≤ (trace p functions).toFinset.card := Finset.card_le_card subset
    _ ≤ (trace p functions).length := List.toFinset_card_le _

theorem trace_length_le_81 (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    (trace p functions).length ≤ 81 :=
  FullCheckedRunQueries.lock_queries_le_81 functions p.tx p.selected
    p.validKey p.ecdsa p.lock p.initial

/-- Whole-run source-model causality makes a fully covered, sound cache's
checked result equal to the result under the actual oracle. -/
theorem covered_checkedResult_eq
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : Cache) (sound : CacheSound functions cache)
    (covered : firstMissing cache
      (trace p (completedFunctions cache)) = none) :
    checkedResult p (completedFunctions cache) = checkedResult p functions ∧
      trace p (completedFunctions cache) = trace p functions := by
  have agree : ∀ q ∈ trace p (completedFunctions cache),
      answer functions q = answer (completedFunctions cache) q := by
    intro q member
    obtain ⟨reply, found⟩ :=
      firstMissing_none_covered cache _ covered q member
    exact (complete_agrees_of_lookup functions cache sound q reply found).symm
  obtain ⟨sameRun, sameTrace⟩ :=
    FullCheckedRunCausality.checked_lock_run_and_queries_congr
      (completedFunctions cache) functions p.tx p.selected p.validKey
      p.ecdsa p.lock p.initial agree
  exact ⟨sameRun.symm, sameTrace.symm⟩

/-- Every halted run is correct, irrespective of its budget. The separate
prefix-causality premise below is needed to prove that it halts by 81 calls. -/
theorem halted_result_correct (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : Cache) (out : Result),
      CacheSound functions cache →
      (run (machine p) functions budget cache).1 = some out →
      out = checkedResult p functions
  | 0, cache, out, sound, halted => by
      cases missing : firstMissing cache
          (trace p (completedFunctions cache)) with
      | none =>
          have correct := (covered_checkedResult_eq p functions cache
            sound missing).1
          have outEq : checkedResult p (completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          simp [CausalQueryAlgorithm.run, machine, missing] at halted
  | budget + 1, cache, out, sound, halted => by
      cases missing : firstMissing cache
          (trace p (completedFunctions cache)) with
      | none =>
          have correct := (covered_checkedResult_eq p functions cache
            sound missing).1
          have outEq : checkedResult p (completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          have nextSound : CacheSound functions
              ((q, answer functions q) :: cache) := by
            intro query reply member
            rcases List.mem_cons.mp member with same | later
            · cases same
              rfl
            · exact sound query reply later
          have tail :
              (run (machine p) functions budget
                ((q, answer functions q) :: cache)).1 = some out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact halted_result_correct p functions budget _ out nextSound tail

/-- A sound cache with enough remaining calls cannot exhaust the budget:
each new query is distinct and belongs to the true trace. -/
theorem run_halts_of_enough
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (prefixCausal : TracePrefixCausal p) :
    ∀ (budget : Nat) (cache : Cache),
      GoodCache p functions cache →
      (trace p functions).length ≤ cache.length + budget →
      ∃ out, (run (machine p) functions budget cache).1 = some out
  | 0, cache, good, enough => by
      cases missing : firstMissing cache
          (trace p (completedFunctions cache)) with
      | none =>
          exact ⟨checkedResult p (completedFunctions cache), by
            simp [CausalQueryAlgorithm.run, machine, missing]⟩
      | some q =>
          have uncached := firstMissing_some_missing cache _ q missing
          have trueMember := firstMissing_true_mem p functions prefixCausal cache
            good.sound q missing
          have nextGood := goodCache_cons p functions cache good q
            uncached trueMember
          have bound := goodCache_length_le_trace p functions _ nextGood
          simp only [List.length_cons, Nat.add_zero] at enough bound
          omega
  | budget + 1, cache, good, enough => by
      cases missing : firstMissing cache
          (trace p (completedFunctions cache)) with
      | none =>
          exact ⟨checkedResult p (completedFunctions cache), by
            simp [CausalQueryAlgorithm.run, machine, missing]⟩
      | some q =>
          have uncached := firstMissing_some_missing cache _ q missing
          have trueMember := firstMissing_true_mem p functions prefixCausal cache
            good.sound q missing
          have nextGood := goodCache_cons p functions cache good q
            uncached trueMember
          have enough' : (trace p functions).length ≤
              ((q, answer functions q) :: cache).length + budget := by
            simpa only [List.length_cons, Nat.add_succ, Nat.succ_add]
              using enough
          obtain ⟨out, tail⟩ :=
            run_halts_of_enough p functions prefixCausal budget _ nextGood enough'
          exact ⟨out, by
            simpa [CausalQueryAlgorithm.run, machine, missing] using tail⟩

/-- Conditional implementation theorem. A separate proof of
`TracePrefixCausal` for the concrete source trace would discharge the only
extra causality premise; `run_and_queries_congr` already supplies terminal
result correctness. The machine makes at most 81 actual calls for this fixed
`FixedInput`; constructing that input causally in a world-indexed game is a
separate obligation. -/
theorem run_81_correct
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (prefixCausal : TracePrefixCausal p) :
    ∃ out,
      (run (machine p) functions 81 []).1 = some out ∧
      out = checkedResult p functions ∧
      (run (machine p) functions 81 []).2.length ≤ 81 := by
  obtain ⟨out, halted⟩ := run_halts_of_enough p functions prefixCausal 81 []
    (goodCache_nil p functions) (by
      simpa using trace_length_le_81 p functions)
  exact ⟨out, halted,
    halted_result_correct p functions 81 [] out (by simp [CacheSound]) halted,
    CausalQueryAlgorithm.run_length_le (machine p) functions 81 []⟩

end QSB.CheckedRunCacheMachine
