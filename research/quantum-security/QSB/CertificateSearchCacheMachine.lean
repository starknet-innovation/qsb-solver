import QSB.CertificateCandidateCacheMachine
import QSB.CertificateSearchCausality

/-!
A classical response-cache algorithm for fixed-input source-model certificate
search. The eager dependency list concatenates the false and true candidate
inventories. It may query conservative sites that source search short-circuits,
and its order can differ from source execution. Prefix causality makes each
next request depend only on earlier H/R replies. Full-list agreement fixes the
exact optional `(Bool × CoreOpcodeStep.State)` search result.

The lock, transaction, selected input, stack, key validator, and ECDSA
predicate stay fixed across oracle worlds. The ≤598 bound counts actual H/R
requests by this `CausalQueryAlgorithm.Machine`; it excludes oracle use hidden
inside externally supplied values or functions, scriptSig evaluation, and
compiled Bitcoin Core. It does not claim a coherent-query/QROM reduction.
-/
namespace QSB.CertificateSearchCacheMachine
open ByteMachine
open CausalQueryAlgorithm (Query answer)
open FullCheckedRunPrefixCausality (PrefixCausal)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

theorem prefixCausal_congr
    (trace : JointSourceChecks.Functions → List Query)
    (causal : PrefixCausal trace)
    (functions functions' : JointSourceChecks.Functions)
    (agree : ∀ q ∈ trace functions,
      answer functions' q = answer functions q) :
    trace functions' = trace functions := by
  have sameTake : ∀ k ≤ (trace functions).length,
      (trace functions').take k = (trace functions).take k := by
    intro k le
    cases k with
    | zero => simp
    | succ j =>
        apply causal functions functions' j (by omega)
        intro q mem
        exact agree q ((List.take_sublist _ _).subset mem)
  have firstCovered : (trace functions').take (trace functions).length =
      trace functions := by
    simpa using sameTake (trace functions).length (by omega)
  have secondLength : (trace functions').length ≤ (trace functions).length := by
    by_contra notLe
    have longer : (trace functions).length < (trace functions').length := by omega
    have reverseAgree : ∀ q ∈ (trace functions').take (trace functions).length,
        answer functions q = answer functions' q := by
      intro q mem
      rw [firstCovered] at mem
      exact (agree q mem).symm
    have next := causal functions' functions (trace functions).length
      longer reverseAgree
    have leftLength := congrArg List.length next
    simp only [List.length_take] at leftLength
    omega
  have secondLength' : (trace functions).length ≤
      (trace functions').length := by
    have lengths := congrArg List.length firstCovered
    simp only [List.length_take] at lengths
    omega
  have sameLength : (trace functions').length = (trace functions).length := by
    omega
  rw [← sameLength, List.take_length] at firstCovered
  exact firstCovered

theorem searchDependencies_prefix
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    PrefixCausal (fun functions =>
      CertificateSearchCausality.searchDependencies functions tx selected
        lock stack validKey ecdsa) := by
  let head : JointSourceChecks.Functions → List Query := fun functions =>
    CertificateCandidateCausality.candidateDependencies functions tx selected
      lock stack false validKey ecdsa
  let tail : JointSourceChecks.Functions → List Query := fun functions =>
    CertificateCandidateCausality.candidateDependencies functions tx selected
      lock stack true validKey ecdsa
  have headPrefix : PrefixCausal head := by
    simpa [head] using
      CertificateCandidateCacheMachine.candidateDependencies_prefix
        tx selected lock stack false validKey ecdsa
  have tailPrefix : PrefixCausal tail := by
    simpa [tail] using
      CertificateCandidateCacheMachine.candidateDependencies_prefix
        tx selected lock stack true validKey ecdsa
  have headCongr : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      head functions' = head functions := by
    intro functions functions' agree
    exact prefixCausal_congr head headPrefix functions functions' agree
  have combined := FullCheckedRunPrefixCausality.append_prefix head tail
    headPrefix headCongr
    (by
      intro functions functions' _ k available agree
      exact tailPrefix functions functions' k available agree)
  simpa [head, tail, CertificateSearchCausality.searchDependencies]
    using combined


/-! ### A fixed-input classical search machine -/


structure FixedInput where
  lock : DynamicCheckedCertificate.Lock
  tx : SighashAllWire.TxFields
  selected : Nat
  stack : List Bytes
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool

def trace (p : FixedInput) (functions : JointSourceChecks.Functions) :
    List Query :=
  CertificateSearchCausality.searchDependencies functions p.tx
    p.selected p.lock p.stack p.validKey p.ecdsa

def searchResult (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    Option (Bool × CoreOpcodeStep.State) :=
  DynamicCheckedCertificate.search (JointSourceChecks.hashes functions)
    p.lock p.stack p.validKey
    (JointSourceChecks.checker functions p.tx p.selected p.ecdsa)

/-- The cache machine computes its next request from stored replies and
width-correct fixed defaults, never by consulting the true oracle inside
its own `step`. -/
def machine (p : FixedInput) :
    CausalQueryAlgorithm.Machine CheckedRunCacheMachine.Cache
      (Option (Bool × CoreOpcodeStep.State)) where
  step := fun cache =>
    let completed := CheckedRunCacheMachine.completedFunctions cache
    match CheckedRunCacheMachine.firstMissing cache (trace p completed) with
    | some q => .inr q
    | none => .inl (searchResult p completed)
  resume := fun cache reply =>
    match CheckedRunCacheMachine.firstMissing cache
        (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
    | some q => (q, reply) :: cache
    | none => cache

/-- The search's first uncached dependency under a sound completed cache
also occurs in the true search dependency list. -/
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
  have samePrefix := searchDependencies_prefix p.tx p.selected p.lock
    p.stack p.validKey p.ecdsa completed functions
    before.length index agreeBefore
  have prefixShape : (trace p completed).take (before.length + 1) =
      before ++ [q] := by
    rw [shape]
    simp [List.take_append]
  have qInPrefix : q ∈ (trace p functions).take (before.length + 1) := by
    change q ∈ (CertificateSearchCausality.searchDependencies
      functions p.tx p.selected p.lock p.stack p.validKey
      p.ecdsa).take (before.length + 1)
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

theorem trace_length_le_598 (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    (trace p functions).length ≤ 598 :=
  CertificateSearchCausality.searchDependencies_length_le_598
    functions p.tx p.selected p.lock p.stack p.validKey p.ecdsa

/-- Fully cached search dependencies determine the search's exact
optional result under the true oracle pair. -/
theorem covered_searchResult_eq
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (sound : CheckedRunCacheMachine.CacheSound functions cache)
    (covered : CheckedRunCacheMachine.firstMissing cache
      (trace p (CheckedRunCacheMachine.completedFunctions cache)) = none) :
    searchResult p (CheckedRunCacheMachine.completedFunctions cache) =
      searchResult p functions := by
  have agree : ∀ q ∈ trace p (CheckedRunCacheMachine.completedFunctions cache),
      answer functions q =
        answer (CheckedRunCacheMachine.completedFunctions cache) q := by
    intro q member
    obtain ⟨reply, found⟩ :=
      CheckedRunCacheMachine.firstMissing_none_covered cache _ covered
        q member
    exact (CheckedRunCacheMachine.complete_agrees_of_lookup functions
      cache sound q reply found).symm
  exact (CertificateSearchCausality.search_congr
    (CheckedRunCacheMachine.completedFunctions cache) functions p.tx
    p.selected p.lock p.stack p.validKey p.ecdsa agree).symm

/-- Any halted cache run computes the true search result. -/
theorem halted_result_correct (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : CheckedRunCacheMachine.Cache)
      (out : Option (Bool × CoreOpcodeStep.State)),
      CheckedRunCacheMachine.CacheSound functions cache →
      (CausalQueryAlgorithm.run (machine p) functions budget cache).1 =
        some out →
      out = searchResult p functions
  | 0, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_searchResult_eq p functions cache sound
            missing
          have outEq : searchResult p
              (CheckedRunCacheMachine.completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          simp [CausalQueryAlgorithm.run, machine, missing] at halted
  | budget + 1, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_searchResult_eq p functions cache sound
            missing
          have outEq : searchResult p
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
          exact ⟨searchResult p
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
          exact ⟨searchResult p
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

/-- The fixed-input source-model certificate search can be computed by
one classical response-cache machine with at most 598 actual H/R requests.
The eager inventory may query checks the source search short-circuits and
reorders the final structural prefix before signature digests. -/
theorem run_598_correct
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run (machine p) functions 598 []).1 =
        some (searchResult p functions) ∧
      (CausalQueryAlgorithm.run (machine p) functions 598 []).2.length ≤
        598 := by
  obtain ⟨out, halted⟩ := run_halts_of_enough p functions 598 []
    (goodCache_nil p functions) (by
      simpa using trace_length_le_598 p functions)
  have correct := halted_result_correct p functions 598 [] out
    (by simp [CheckedRunCacheMachine.CacheSound]) halted
  exact ⟨by simpa [correct] using halted,
    CausalQueryAlgorithm.run_length_le (machine p) functions 598 []⟩

end QSB.CertificateSearchCacheMachine
