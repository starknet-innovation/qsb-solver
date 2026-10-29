import QSB.ScriptSigAllRunRawBound
import QSB.DynamicSourceExtractorCacheMachine

/-!
A conditional classical response-cache algorithm for a world-indexed raw
source extractor. Strict transaction parsing selects a scriptSig, an externally
supplied `ScriptSigBoundedCausalContract.Contract` provides its evaluator and
charged H/R trace, and the prepared attempt enters the source extractor.
The combined eager dependency order can differ from source execution and may
include downstream work skipped after an earlier failure.

The contract is assumed, not concretely witnessed or refined to Bitcoin Core.
The raw bytes, lock, key validator, ECDSA predicate, and contract are fixed
across oracle worlds; these values may carry oracle advice. The ≤1697 bound
counts only this classical machine's explicit H/R requests, excluding oracle
work hidden in supplied callbacks, lock construction, and compiled Core. It
makes no coherent-query/QROM claim.
-/
namespace QSB.WorldIndexedRawCacheMachine
open ByteMachine
open CausalQueryAlgorithm (Query answer)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- All external inputs, including the world-indexed scriptSig evaluator and
its causal trace contract, are fixed while H/R functions vary. -/
structure FixedInput where
  contract : ScriptSigBoundedCausalContract.Contract
  lock : DynamicCheckedCertificate.Lock
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool
  raw : DynamicRawSource.RawAttempt

def trace (p : FixedInput) (functions : JointSourceChecks.Functions) :
    List Query :=
  WorldIndexedScriptSigExtractor.combinedDependencies
    p.contract.toContract functions p.lock p.validKey p.ecdsa p.raw

def rawResult (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    Option (Bytes × RoundWitness (Fin 150) Bytes Bytes) :=
  DynamicRawSource.extractor functions p.lock p.validKey p.ecdsa
    (p.contract.eval functions) p.raw

/-- The cache machine computes its next request from stored replies and
width-correct fixed defaults, never by consulting the true oracle inside
its own `step`. -/
def machine (p : FixedInput) :
    CausalQueryAlgorithm.Machine CheckedRunCacheMachine.Cache
      (Option (Bytes × RoundWitness (Fin 150) Bytes Bytes)) where
  step := fun cache =>
    let completed := CheckedRunCacheMachine.completedFunctions cache
    match CheckedRunCacheMachine.firstMissing cache (trace p completed) with
    | some q => .inr q
    | none => .inl (rawResult p completed)
  resume := fun cache reply =>
    match CheckedRunCacheMachine.firstMissing cache
        (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
    | some q => (q, reply) :: cache
    | none => cache

/-- The raw extractor's first uncached dependency under a sound completed cache
also occurs in the true combined dependency list. -/
theorem firstMissing_true_mem
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (sound : CheckedRunCacheMachine.CacheSound functions cache)
    (q : Query)
    (missing : CheckedRunCacheMachine.firstMissing cache
      (trace p (CheckedRunCacheMachine.completedFunctions cache)) = some q) :
    q ∈ trace p functions := by
  obtain ⟨before, after, shape, covered, _⟩ :=
    CheckedRunCacheMachine.firstMissing_some_prefix cache _ q missing
  let completed := CheckedRunCacheMachine.completedFunctions cache
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
    exact (CheckedRunCacheMachine.complete_agrees_of_lookup functions
      cache sound x reply found).symm
  have samePrefix := ScriptSigAllRunRawBound.combinedDependencies_prefix
    p.contract p.lock p.validKey p.ecdsa p.raw completed functions
    before.length index agreeBefore
  have prefixShape : (trace p completed).take (before.length + 1) =
      before ++ [q] := by
    rw [shape]
    simp [List.take_append]
  have qInPrefix : q ∈ (trace p functions).take (before.length + 1) := by
    change q ∈ (WorldIndexedScriptSigExtractor.combinedDependencies
      p.contract.toContract functions p.lock p.validKey p.ecdsa p.raw).take
        (before.length + 1)
    rw [samePrefix]
    change q ∈ (trace p completed).take (before.length + 1)
    rw [prefixShape]
    simp
  exact (List.take_sublist _ _).subset qInPrefix

structure GoodCache (p : FixedInput)
    (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache) : Prop where
  sound : CheckedRunCacheMachine.CacheSound functions cache
  nodup : (cache.map Prod.fst).Nodup
  inTrace : ∀ entry ∈ cache, entry.1 ∈ trace p functions

theorem goodCache_nil (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    GoodCache p functions [] := by
  constructor <;> simp [CheckedRunCacheMachine.CacheSound]

theorem goodCache_cons
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (good : GoodCache p functions cache)
    (q : Query)
    (missing : CheckedRunCacheMachine.lookup cache q = none)
    (inTrace : q ∈ trace p functions) :
    GoodCache p functions ((q, answer functions q) :: cache) := by
  refine ⟨?_, ?_, ?_⟩
  · intro query reply member
    rcases List.mem_cons.mp member with same | later
    · cases same
      rfl
    · exact good.sound query reply later
  · have notMem :=
      (CheckedRunCacheMachine.lookup_none_iff_not_mem cache q).mp missing
    simp [notMem, good.nodup]
  · intro entry member
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact inTrace
    · exact good.inTrace entry later

theorem goodCache_length_le_trace
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (good : GoodCache p functions cache) :
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

theorem trace_length_le_1697 (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    (trace p functions).length ≤ 1697 :=
  ScriptSigAllRunRawBound.combinedDependencies_length_le_1697
    p.contract functions p.lock p.validKey p.ecdsa p.raw

/-- Fully cached combined dependencies determine the extractor's exact
optional result under the true oracle pair. -/
theorem covered_rawResult_eq
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (sound : CheckedRunCacheMachine.CacheSound functions cache)
    (covered : CheckedRunCacheMachine.firstMissing cache
      (trace p (CheckedRunCacheMachine.completedFunctions cache)) = none) :
    rawResult p (CheckedRunCacheMachine.completedFunctions cache) =
      rawResult p functions := by
  have agree : ∀ q ∈ trace p (CheckedRunCacheMachine.completedFunctions cache),
      answer functions q =
        answer (CheckedRunCacheMachine.completedFunctions cache) q := by
    intro q member
    obtain ⟨reply, found⟩ :=
      CheckedRunCacheMachine.firstMissing_none_covered cache _ covered
        q member
    exact (CheckedRunCacheMachine.complete_agrees_of_lookup functions
      cache sound q reply found).symm
  exact (WorldIndexedScriptSigExtractor.raw_extractor_congr
    p.contract.toContract (CheckedRunCacheMachine.completedFunctions cache)
    functions p.lock p.validKey p.ecdsa p.raw agree).symm

/-- Any halted cache run computes the true raw extractor result. -/
theorem halted_result_correct (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : CheckedRunCacheMachine.Cache)
      (out : Option (Bytes × RoundWitness (Fin 150) Bytes Bytes)),
      CheckedRunCacheMachine.CacheSound functions cache →
      (CausalQueryAlgorithm.run (machine p) functions budget cache).1 =
        some out →
      out = rawResult p functions
  | 0, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_rawResult_eq p functions cache sound
            missing
          have outEq : rawResult p
              (CheckedRunCacheMachine.completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          simp [CausalQueryAlgorithm.run, machine, missing] at halted
  | budget + 1, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_rawResult_eq p functions cache sound
            missing
          have outEq : rawResult p
              (CheckedRunCacheMachine.completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          have nextSound : CheckedRunCacheMachine.CacheSound functions
              ((q, answer functions q) :: cache) := by
            intro query reply member
            rcases List.mem_cons.mp member with same | later
            · cases same
              rfl
            · exact sound query reply later
          have tail :
              (CausalQueryAlgorithm.run (machine p) functions budget
                ((q, answer functions q) :: cache)).1 = some out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact halted_result_correct p functions budget _ out nextSound tail

/-- A good cache with enough remaining requests cannot exhaust its fuel:
every requested query is distinct and belongs to the true eager inventory. -/
theorem run_halts_of_enough
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : CheckedRunCacheMachine.Cache),
      GoodCache p functions cache →
      (trace p functions).length ≤ cache.length + budget →
      ∃ out, (CausalQueryAlgorithm.run (machine p) functions budget
        cache).1 = some out
  | 0, cache, good, enough => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          exact ⟨rawResult p
            (CheckedRunCacheMachine.completedFunctions cache), by
            simp [CausalQueryAlgorithm.run, machine, missing]⟩
      | some q =>
          have uncached := CheckedRunCacheMachine.firstMissing_some_missing
            cache _ q missing
          have trueMember := firstMissing_true_mem p functions cache
            good.sound q missing
          have nextGood := goodCache_cons p functions cache good q
            uncached trueMember
          have bound := goodCache_length_le_trace p functions _ nextGood
          simp only [List.length_cons, Nat.add_zero] at enough bound
          omega
  | budget + 1, cache, good, enough => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          exact ⟨rawResult p
            (CheckedRunCacheMachine.completedFunctions cache), by
            simp [CausalQueryAlgorithm.run, machine, missing]⟩
      | some q =>
          have uncached := CheckedRunCacheMachine.firstMissing_some_missing
            cache _ q missing
          have trueMember := firstMissing_true_mem p functions cache
            good.sound q missing
          have nextGood := goodCache_cons p functions cache good q
            uncached trueMember
          have enough' : (trace p functions).length ≤
              ((q, answer functions q) :: cache).length + budget := by
            simpa only [List.length_cons, Nat.add_succ, Nat.succ_add]
              using enough
          obtain ⟨out, tail⟩ :=
            run_halts_of_enough p functions budget _ nextGood enough'
          exact ⟨out, by
            simpa [CausalQueryAlgorithm.run, machine, missing] using tail⟩

/-- The fixed-input world-indexed raw source extractor can be computed by
one classical response-cache machine with at most 1697 actual H/R requests.
The eager inventory may query sites skipped by source short-circuiting and
reorders some source calls. The required scriptSig contract is an assumption,
not a witnessed evaluator implementation. -/
theorem run_1697_correct
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run (machine p) functions 1697 []).1 =
        some (rawResult p functions) ∧
      (CausalQueryAlgorithm.run (machine p) functions 1697 []).2.length ≤
        1697 := by
  obtain ⟨out, halted⟩ := run_halts_of_enough p functions 1697 []
    (goodCache_nil p functions) (by
      simpa using trace_length_le_1697 p functions)
  have correct := halted_result_correct p functions 1697 [] out
    (by simp [CheckedRunCacheMachine.CacheSound]) halted
  exact ⟨by simpa [correct] using halted,
    CausalQueryAlgorithm.run_length_le (machine p) functions 1697 []⟩

end QSB.WorldIndexedRawCacheMachine
