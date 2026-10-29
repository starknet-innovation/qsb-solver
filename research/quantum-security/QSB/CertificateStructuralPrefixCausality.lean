import QSB.CertificateStructuralQueries
import QSB.FullCheckedRunPrefixCausality
import QSB.CheckedRunCacheMachine

/-!
Prefix causality for the conservative ordered H/R dependencies of seven
structural certificate runs. Each run starts from the same fixed stack and
supplied first-round outcome; the list counts repeated prefix work and can
include sites skipped by certificate short-circuiting. Signature digest
queries and source execution order of the full candidate are separate.
-/
namespace QSB.CertificateStructuralPrefixCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)
open FullCheckedRunPrefixCausality (PrefixCausal append_prefix empty_prefix)
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- Full agreement on one byte-run query list fixes that list itself. -/
theorem byteRunQueries_congr
    (functions functions' : JointSourceChecks.Functions) :
    ∀ (ops : List Op) (s : State),
      (∀ q ∈ ByteMachineQueries.runQueries functions ops s,
        answer functions' q = answer functions q) →
      ByteMachineQueries.runQueries functions' ops s =
        ByteMachineQueries.runQueries functions ops s
  | [], s, _ => by simp [ByteMachineQueries.runQueries]
  | op :: rest, s, agree => by
      have headAgree : ∀ q ∈ ByteMachineQueries.stepQueries functions op
          s.stack, answer functions' q = answer functions q :=
        fun q mem => agree q
          (ByteMachineQueries.stepQueries_mem_runQueries functions op rest
            s q mem)
      have sameHead := FullCheckedRunCausality.opcodeStepQueries_congr
        functions functions' op s.stack headAgree
      have sameStep := ByteMachineQueries.step_congr functions functions'
        op s headAgree
      simp only [ByteMachineQueries.runQueries, sameHead, sameStep]
      cases hstep : ByteMachine.step (JointSourceChecks.hashes functions)
          op s with
      | none => rfl
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large]
          · have tailAgree : ∀ q ∈ ByteMachineQueries.runQueries
                functions rest next,
                answer functions' q = answer functions q :=
              fun q mem => agree q
                (ByteMachineQueries.restQueries_mem_runQueries functions
                  op rest s next hstep (by simpa using large) q mem)
            have tailEq := byteRunQueries_congr functions functions' rest
              next tailAgree
            simp [large, tailEq]

/-- A byte-machine run's next query depends only on prior listed answers. -/
theorem byteRunQueries_prefix :
    ∀ (ops : List Op) (s : State),
      PrefixCausal (fun functions =>
        ByteMachineQueries.runQueries functions ops s)
  | [], s => by
      simpa [ByteMachineQueries.runQueries] using empty_prefix
  | op :: rest, s => by
      let head : JointSourceChecks.Functions → List Query :=
        fun functions => ByteMachineQueries.stepQueries functions op s.stack
      let tail : JointSourceChecks.Functions → List Query :=
        fun functions =>
          match ByteMachine.step (JointSourceChecks.hashes functions) op s with
          | none => []
          | some next =>
              if next.stack.length > 1000 then []
              else ByteMachineQueries.runQueries functions rest next
      have headPrefix : PrefixCausal head := by
        simpa [head] using
          FullCheckedRunPrefixCausality.opcodeStepQueries_prefix op s.stack
      have headCongr : ∀ functions functions',
          (∀ q ∈ head functions,
            answer functions' q = answer functions q) →
          head functions' = head functions := by
        intro functions functions' agree
        exact FullCheckedRunCausality.opcodeStepQueries_congr functions
          functions' op s.stack agree
      have tailPrefix : ∀ functions functions',
          (∀ q ∈ head functions,
            answer functions' q = answer functions q) →
          ∀ k, k < (tail functions).length →
            (∀ q ∈ (tail functions).take k,
              answer functions' q = answer functions q) →
            (tail functions').take (k + 1) =
              (tail functions).take (k + 1) := by
        intro functions functions' headAgree
        have stepEq := ByteMachineQueries.step_congr functions functions'
          op s headAgree
        dsimp [tail]
        rw [stepEq]
        cases hstep : ByteMachine.step (JointSourceChecks.hashes functions)
            op s with
        | none => simp
        | some next =>
            by_cases large : next.stack.length > 1000
            · simp [large]
            · simpa [large] using byteRunQueries_prefix rest next
                functions functions'
      have combined := append_prefix head tail headPrefix headCongr
        tailPrefix
      have traceEq :
          (fun functions => ByteMachineQueries.runQueries functions
            (op :: rest) s) =
          (fun functions => head functions ++ tail functions) := by
        funext functions
        simp only [ByteMachineQueries.runQueries, head, tail]
        cases ByteMachine.step (JointSourceChecks.hashes functions) op s with
        | none => simp
        | some next =>
            simp
            split_ifs <;> simp
      rw [traceEq]
      exact combined

/-- A fixed list of byte programs has a prefix-causal concatenation of its
individual dependency lists, even when those runs repeat prefixes. -/
theorem programs_prefix (programs : List (List Op)) (s : State) :
    PrefixCausal (fun functions => programs.flatMap fun ops =>
      ByteMachineQueries.runQueries functions ops s) := by
  induction programs with
  | nil =>
      simpa using empty_prefix
  | cons ops rest ih =>
      let head : JointSourceChecks.Functions → List Query :=
        fun functions => ByteMachineQueries.runQueries functions ops s
      let tail : JointSourceChecks.Functions → List Query :=
        fun functions => rest.flatMap fun other =>
          ByteMachineQueries.runQueries functions other s
      have headPrefix : PrefixCausal head := by
        simpa [head] using byteRunQueries_prefix ops s
      have headCongr : ∀ functions functions',
          (∀ q ∈ head functions,
            answer functions' q = answer functions q) →
          head functions' = head functions := by
        intro functions functions' agree
        exact byteRunQueries_congr functions functions' ops s agree
      have tailPrefix : ∀ functions functions',
          (∀ q ∈ head functions,
            answer functions' q = answer functions q) →
          ∀ k, k < (tail functions).length →
            (∀ q ∈ (tail functions).take k,
              answer functions' q = answer functions q) →
            (tail functions').take (k + 1) =
              (tail functions).take (k + 1) := by
        intro functions functions' _
        exact ih functions functions'
      have combined := append_prefix head tail headPrefix headCongr
        tailPrefix
      simpa [head, tail, List.flatMap_cons] using combined

/-- Prefix causality of the seven structural-run dependency lists for every
parameterized lock and fixed candidate stack/outcome. -/
theorem structuralDependencies_prefix
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) :
    PrefixCausal (fun functions =>
      CertificateStructuralQueries.structuralDependencies functions
        lock stack firstRound) := by
  simpa [CertificateStructuralQueries.structuralDependencies] using
    programs_prefix (CertificateStructuralQueries.sitePrograms lock)
      (CertificateStructuralQueries.initialByte stack firstRound)

/-- Agreement on the first `k` answers fixes the first `k + 1` structural
dependency entries. This is the direct cache-machine interface. -/
theorem structuralDependencies_prefix_next
    (functions functions' : JointSourceChecks.Functions)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (firstRound : Bool) (k : Nat)
    (available : k <
      (CertificateStructuralQueries.structuralDependencies functions
        lock stack firstRound).length)
    (agree : ∀ q ∈
      (CertificateStructuralQueries.structuralDependencies functions
        lock stack firstRound).take k,
      answer functions' q = answer functions q) :
    (CertificateStructuralQueries.structuralDependencies functions'
      lock stack firstRound).take (k + 1) =
    (CertificateStructuralQueries.structuralDependencies functions
      lock stack firstRound).take (k + 1) :=
  structuralDependencies_prefix lock stack firstRound functions functions'
    k available agree

/-! ### A cache machine for the seven structural results -/

structure FixedInput where
  lock : DynamicCheckedCertificate.Lock
  stack : List Bytes
  firstRound : Bool

def trace (p : FixedInput) (functions : JointSourceChecks.Functions) :
    List Query :=
  CertificateStructuralQueries.structuralDependencies functions p.lock
    p.stack p.firstRound

/-- The seven outcomes in dependency-list order. Each element is the
success or failure result of its own Core-shaped structural run from the
common candidate input. -/
def sevenResults (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    List (Option CoreOpcodeStep.State) :=
  (CertificateStructuralQueries.sitePrograms p.lock).map fun ops =>
    CoreStructuralRun.run (JointSourceChecks.hashes functions) ops
      (DynamicCheckedCertificate.initial p.stack p.firstRound)

/-- Agreement on all structural dependencies fixes every run result. -/
theorem sevenResults_congr
    (p : FixedInput)
    (functions functions' : JointSourceChecks.Functions)
    (agree : ∀ q ∈ trace p functions,
      answer functions' q = answer functions q) :
    sevenResults p functions' = sevenResults p functions := by
  unfold sevenResults
  apply List.map_congr_left
  intro ops member
  exact CertificateStructuralQueries.structural_runs_congr
    functions functions' p.lock p.stack p.firstRound agree ops member

/-- This machine reads only cached oracle replies and fixed width-correct
defaults when deciding which query to ask. It asks the first uncached query
of the conservative seven-run dependency list. -/
def machine (p : FixedInput) :
    CausalQueryAlgorithm.Machine CheckedRunCacheMachine.Cache
      (List (Option CoreOpcodeStep.State)) where
  step := fun cache =>
    let completed := CheckedRunCacheMachine.completedFunctions cache
    match CheckedRunCacheMachine.firstMissing cache (trace p completed) with
    | some q => .inr q
    | none => .inl (sevenResults p completed)
  resume := fun cache reply =>
    match CheckedRunCacheMachine.firstMissing cache
        (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
    | some q => (q, reply) :: cache
    | none => cache

/-- A sound cache's first missing candidate query is also in the true
seven-run dependency list. -/
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
  have samePrefix := structuralDependencies_prefix_next completed functions
    p.lock p.stack p.firstRound before.length index agreeBefore
  have prefixShape : (trace p completed).take (before.length + 1) =
      before ++ [q] := by
    rw [shape]
    simp [List.take_append]
  have qInPrefix : q ∈ (trace p functions).take (before.length + 1) := by
    change q ∈ (CertificateStructuralQueries.structuralDependencies
      functions p.lock p.stack p.firstRound).take (before.length + 1)
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

theorem trace_length_le_231 (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    (trace p functions).length ≤ 231 :=
  CertificateStructuralQueries.structuralDependencies_length_le_231
    functions p.lock p.stack p.firstRound

/-- Once the completed trace is fully cached, its seven structural results
equal the results under the true oracle pair. -/
theorem covered_sevenResults_eq
    (p : FixedInput) (functions : JointSourceChecks.Functions)
    (cache : CheckedRunCacheMachine.Cache)
    (sound : CheckedRunCacheMachine.CacheSound functions cache)
    (covered : CheckedRunCacheMachine.firstMissing cache
      (trace p (CheckedRunCacheMachine.completedFunctions cache)) = none) :
    sevenResults p (CheckedRunCacheMachine.completedFunctions cache) =
      sevenResults p functions := by
  have agree : ∀ q ∈ trace p (CheckedRunCacheMachine.completedFunctions cache),
      answer functions q =
        answer (CheckedRunCacheMachine.completedFunctions cache) q := by
    intro q member
    obtain ⟨reply, found⟩ :=
      CheckedRunCacheMachine.firstMissing_none_covered cache _ covered
        q member
    exact (CheckedRunCacheMachine.complete_agrees_of_lookup functions
      cache sound q reply found).symm
  exact (sevenResults_congr p
    (CheckedRunCacheMachine.completedFunctions cache) functions agree).symm

/-- Any halted cache-machine run returns the true seven structural results,
irrespective of the chosen fuel. -/
theorem halted_result_correct (p : FixedInput)
    (functions : JointSourceChecks.Functions) :
    ∀ (budget : Nat) (cache : CheckedRunCacheMachine.Cache)
      (out : List (Option CoreOpcodeStep.State)),
      CheckedRunCacheMachine.CacheSound functions cache →
      (CausalQueryAlgorithm.run (machine p) functions budget cache).1 =
        some out →
      out = sevenResults p functions
  | 0, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_sevenResults_eq p functions cache sound
            missing
          have outEq : sevenResults p
              (CheckedRunCacheMachine.completedFunctions cache) = out := by
            simpa [CausalQueryAlgorithm.run, machine, missing] using halted
          exact outEq.symm.trans correct
      | some q =>
          simp [CausalQueryAlgorithm.run, machine, missing] at halted
  | budget + 1, cache, out, sound, halted => by
      cases missing : CheckedRunCacheMachine.firstMissing cache
          (trace p (CheckedRunCacheMachine.completedFunctions cache)) with
      | none =>
          have correct := covered_sevenResults_eq p functions cache sound
            missing
          have outEq : sevenResults p
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

/-- A good cache with enough remaining query slots must halt. Each new
query is distinct and belongs to the true conservative dependency list. -/
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
          exact ⟨sevenResults p
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
          exact ⟨sevenResults p
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

/-- The seven structural-run results can be obtained by one classical
response-cache machine with at most 231 actual H/R requests. The fixed
candidate input and supplied first-round outcome are external; this is not
the source execution order or a complete candidate query budget. -/
theorem run_231_correct
    (p : FixedInput) (functions : JointSourceChecks.Functions) :
    (CausalQueryAlgorithm.run (machine p) functions 231 []).1 =
        some (sevenResults p functions) ∧
      (CausalQueryAlgorithm.run (machine p) functions 231 []).2.length ≤
        231 := by
  obtain ⟨out, halted⟩ := run_halts_of_enough p functions 231 []
    (goodCache_nil p functions) (by
      simpa using trace_length_le_231 p functions)
  have correct := halted_result_correct p functions 231 [] out
    (by simp [CheckedRunCacheMachine.CacheSound]) halted
  exact ⟨by simpa [correct] using halted,
    CausalQueryAlgorithm.run_length_le (machine p) functions 231 []⟩

end QSB.CertificateStructuralPrefixCausality
