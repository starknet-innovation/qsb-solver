import QSB.CertificateSearchCacheMachine
import QSB.DynamicSourceExtractorCausality

/-!
A classical response-cache algorithm for the source-model extractor on one
fixed, already-prepared attempt. Its eager dependency list includes a repeated
certificate search and structural runs that source extraction may skip. The
request order is an analytic causal order and need not match source execution.

The lock, attempt, key validator, and ECDSA predicate stay fixed across oracle
worlds. The eventual request bound excludes preparation, scriptSig execution,
oracle use hidden inside external functions, and compiled Bitcoin Core. It is
not a coherent-query/QROM reduction.
-/
namespace QSB.DynamicSourceExtractorCacheMachine
open ByteMachine
open CausalQueryAlgorithm (Query answer)
open FullCheckedRunPrefixCausality (PrefixCausal)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Two independent prefix-causal lists can be concatenated. -/
theorem append_prefix_of_prefix
    (head tail : JointSourceChecks.Functions → List Query)
    (headPrefix : PrefixCausal head) (tailPrefix : PrefixCausal tail) :
    PrefixCausal (fun functions => head functions ++ tail functions) :=
  FullCheckedRunPrefixCausality.append_prefix head tail headPrefix
    (fun functions functions' agree =>
      CertificateSearchCacheMachine.prefixCausal_congr head headPrefix
        functions functions' agree)
    (by
      intro functions functions' _
      exact tailPrefix functions functions')

private def initialByte (attempt : DynamicSourceGame.Attempt)
    (firstRound : Bool) : State :=
  ⟨attempt.stack, CoreCheckedCertificate.outcomes firstRound, 0⟩

private def priorAndFirst (lock : DynamicCheckedCertificate.Lock) : List Op :=
  DynamicFullSerialized.priorOps lock.pin lock.nonce0
    lock.firstCommitment ++ [.checkmultisig]

private def pinTrace (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) : List Query :=
  ByteMachineQueries.runQueries functions
    ((DynamicCheckedCertificate.program lock).take 2)
    (initialByte attempt firstRound)

private def extractionTrace (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) : List Query :=
  ByteMachineQueries.runQueries functions (priorAndFirst lock)
    (initialByte attempt firstRound)

private def finalPrefixTrace (functions : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) : List Query :=
  ByteMachineQueries.runQueries functions
    (DynamicCheckedCertificate.beforeFinalProgram lock)
    (initialByte attempt firstRound)

/-- Once the first search fixes a round, the four eager continuation lists
have a causal concatenation. -/
theorem roundContinuation_prefix
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt) (firstRound : Bool) :
    PrefixCausal (fun functions =>
      pinTrace functions lock attempt firstRound ++
      CertificateSearchCausality.searchDependencies functions attempt.tx
        attempt.selected lock attempt.stack validKey ecdsa ++
      extractionTrace functions lock attempt firstRound ++
      finalPrefixTrace functions lock attempt firstRound) := by
  let pin : JointSourceChecks.Functions → List Query := fun functions =>
    pinTrace functions lock attempt firstRound
  let search : JointSourceChecks.Functions → List Query := fun functions =>
    CertificateSearchCausality.searchDependencies functions attempt.tx
      attempt.selected lock attempt.stack validKey ecdsa
  let extract : JointSourceChecks.Functions → List Query := fun functions =>
    extractionTrace functions lock attempt firstRound
  let final : JointSourceChecks.Functions → List Query := fun functions =>
    finalPrefixTrace functions lock attempt firstRound
  have pinPrefix : PrefixCausal pin := by
    simpa [pin, pinTrace] using
      CertificateStructuralPrefixCausality.byteRunQueries_prefix
        ((DynamicCheckedCertificate.program lock).take 2)
        (initialByte attempt firstRound)
  have searchPrefix : PrefixCausal search := by
    simpa [search] using
      CertificateSearchCacheMachine.searchDependencies_prefix
        attempt.tx attempt.selected lock attempt.stack validKey ecdsa
  have extractPrefix : PrefixCausal extract := by
    simpa [extract, extractionTrace] using
      CertificateStructuralPrefixCausality.byteRunQueries_prefix
        (priorAndFirst lock) (initialByte attempt firstRound)
  have finalPrefix : PrefixCausal final := by
    simpa [final, finalPrefixTrace] using
      CertificateStructuralPrefixCausality.byteRunQueries_prefix
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (initialByte attempt firstRound)
  have first := append_prefix_of_prefix pin search pinPrefix searchPrefix
  have second := append_prefix_of_prefix
    (fun functions => pin functions ++ search functions) extract
    first extractPrefix
  have third := append_prefix_of_prefix
    (fun functions => pin functions ++ search functions ++ extract functions)
    final second finalPrefix
  simpa [pin, search, extract, final, List.append_assoc] using third

/-- Prefix causality for the complete eager source-extractor inventory on one
fixed, prepared attempt. -/
theorem extractorDependencies_prefix
    (lock : DynamicCheckedCertificate.Lock)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (attempt : DynamicSourceGame.Attempt) :
    PrefixCausal (fun functions =>
      DynamicSourceExtractorCausality.extractorDependencies functions lock
        validKey ecdsa attempt) := by
  let head : JointSourceChecks.Functions → List Query := fun functions =>
    CertificateSearchCausality.searchDependencies functions attempt.tx
      attempt.selected lock attempt.stack validKey ecdsa
  let tail : JointSourceChecks.Functions → List Query := fun functions =>
    DynamicSourceExtractorCausality.continuationDependencies functions lock
      validKey ecdsa attempt
  have headPrefix : PrefixCausal head := by
    simpa [head] using
      CertificateSearchCacheMachine.searchDependencies_prefix
        attempt.tx attempt.selected lock attempt.stack validKey ecdsa
  have headCongr : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      head functions' = head functions := by
    intro functions functions' agree
    exact CertificateSearchCacheMachine.prefixCausal_congr head headPrefix
      functions functions' agree
  have tailPrefix : ∀ functions functions',
      (∀ q ∈ head functions,
        answer functions' q = answer functions q) →
      ∀ k, k < (tail functions).length →
        (∀ q ∈ (tail functions).take k,
          answer functions' q = answer functions q) →
        (tail functions').take (k + 1) =
          (tail functions).take (k + 1) := by
    intro functions functions' headAgree
    have searchEq := CertificateSearchCausality.search_congr
      functions functions' attempt.tx attempt.selected lock attempt.stack
      validKey ecdsa headAgree
    cases found : DynamicCheckedCertificate.search
        (JointSourceChecks.hashes functions) lock attempt.stack validKey
        (JointSourceChecks.checker functions attempt.tx attempt.selected
          ecdsa) with
    | none =>
        intro k available _
        have tailEmpty : tail functions = [] := by
          simp [tail, DynamicSourceExtractorCausality.continuationDependencies,
            found]
        simp [tailEmpty] at available
    | some pair =>
        obtain ⟨firstRound, sourceFinal⟩ := pair
        have found' : DynamicCheckedCertificate.search
            (JointSourceChecks.hashes functions') lock attempt.stack validKey
            (JointSourceChecks.checker functions' attempt.tx
              attempt.selected ecdsa) = some (firstRound, sourceFinal) :=
          searchEq.trans found
        let cont : JointSourceChecks.Functions → List Query :=
          fun f =>
            pinTrace f lock attempt firstRound ++
            CertificateSearchCausality.searchDependencies f attempt.tx
              attempt.selected lock attempt.stack validKey ecdsa ++
            extractionTrace f lock attempt firstRound ++
            finalPrefixTrace f lock attempt firstRound
        have contPrefix : PrefixCausal cont := by
          simpa [cont] using roundContinuation_prefix lock validKey ecdsa
            attempt firstRound
        have tailEq : tail functions = cont functions := by
          simp only [tail, DynamicSourceExtractorCausality.continuationDependencies,
            found]
          rfl
        have tailEq' : tail functions' = cont functions' := by
          simp only [tail, DynamicSourceExtractorCausality.continuationDependencies,
            found']
          rfl
        intro k available agree
        rw [tailEq] at available agree
        rw [tailEq', tailEq]
        exact contPrefix functions functions' k available agree
  have combined := FullCheckedRunPrefixCausality.append_prefix head tail
    headPrefix headCongr tailPrefix
  simpa [head, tail, DynamicSourceExtractorCausality.extractorDependencies]
    using combined


/-! ### A fixed-input classical source-extractor machine -/


structure FixedInput where
  lock : DynamicCheckedCertificate.Lock
  validKey : Bytes → Bool
  ecdsa : Bytes → Bytes → Bytes → Bool
  attempt : DynamicSourceGame.Attempt

def trace (p : FixedInput) (functions : JointSourceChecks.Functions) :
    List Query :=
  DynamicSourceExtractorCausality.extractorDependencies functions p.lock
    p.validKey p.ecdsa p.attempt

def extractorResult (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    Option (Bytes × RoundWitness (Fin 150) Bytes Bytes) :=
  DynamicSourceGame.extractor functions p.lock p.validKey p.ecdsa p.attempt

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
    | none => .inl (extractorResult p completed)
  resume := fun cache reply =>
    match CheckedRunCacheMachine.firstMissing cache
        (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
    | some q => (q, reply) :: cache
    | none => cache

/-- The extractor's first uncached dependency under a sound completed cache
also occurs in the true extractor dependency list. -/
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
  have samePrefix := extractorDependencies_prefix p.lock p.validKey
    p.ecdsa p.attempt completed functions before.length index agreeBefore
  have prefixShape : (trace p completed).take (before.length + 1) =
      before ++ [q] := by
    rw [shape]
    simp [List.take_append]
  have qInPrefix : q ∈ (trace p functions).take (before.length + 1) := by
    change q ∈ (DynamicSourceExtractorCausality.extractorDependencies
      functions p.lock p.validKey p.ecdsa p.attempt).take (before.length + 1)
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

theorem trace_length_le_1295 (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    (trace p functions).length ≤ 1295 :=
  DynamicSourceExtractorCausality.extractorDependencies_length_le_1295
    functions p.lock p.validKey p.ecdsa p.attempt

/-- Fully cached extractor dependencies determine the extractor's exact
optional result under the true oracle pair. -/
theorem covered_extractorResult_eq
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (sound : CheckedRunCacheMachine.CacheSound functions cache)
    (covered : CheckedRunCacheMachine.firstMissing cache
      (trace p (CheckedRunCacheMachine.completedFunctions cache)) = none) :
    extractorResult p (CheckedRunCacheMachine.completedFunctions cache) =
      extractorResult p functions := by
  have agree : ∀ q ∈ trace p (CheckedRunCacheMachine.completedFunctions cache),
      answer functions q =
        answer (CheckedRunCacheMachine.completedFunctions cache) q := by
    intro q member
    obtain ⟨reply, found⟩ :=
      CheckedRunCacheMachine.firstMissing_none_covered cache _ covered
        q member
    exact (CheckedRunCacheMachine.complete_agrees_of_lookup functions
      cache sound q reply found).symm
  exact (DynamicSourceExtractorCausality.extractor_congr
    (CheckedRunCacheMachine.completedFunctions cache) functions p.lock
    p.validKey p.ecdsa p.attempt agree).symm

/-- Any halted cache run computes the true extractor result. -/
theorem halted_result_correct (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : CheckedRunCacheMachine.Cache)
      (out : Option (Bytes × RoundWitness (Fin 150) Bytes Bytes)),
      CheckedRunCacheMachine.CacheSound functions cache →
      (CausalQueryAlgorithm.run (machine p) functions budget cache).1 =
        some out →
      out = extractorResult p functions
  | 0, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_extractorResult_eq p functions cache sound
            missing
          have outEq : extractorResult p
              (CheckedRunCacheMachine.completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          simp [CausalQueryAlgorithm.run, machine, missing] at halted
  | budget + 1, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_extractorResult_eq p functions cache sound
            missing
          have outEq : extractorResult p
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
          exact ⟨extractorResult p
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
          exact ⟨extractorResult p
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

/-- The fixed-input source-model certificate extractor can be computed by
one classical response-cache machine with at most 1295 actual H/R requests.
The eager inventory may query checks the source extractor short-circuits and
reorders the final structural prefix before signature digests. -/
theorem run_1295_correct
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run (machine p) functions 1295 []).1 =
        some (extractorResult p functions) ∧
      (CausalQueryAlgorithm.run (machine p) functions 1295 []).2.length ≤
        1295 := by
  obtain ⟨out, halted⟩ := run_halts_of_enough p functions 1295 []
    (goodCache_nil p functions) (by
      simpa using trace_length_le_1295 p functions)
  have correct := halted_result_correct p functions 1295 [] out
    (by simp [CheckedRunCacheMachine.CacheSound]) halted
  exact ⟨by simpa [correct] using halted,
    CausalQueryAlgorithm.run_length_le (machine p) functions 1295 []⟩

end QSB.DynamicSourceExtractorCacheMachine
