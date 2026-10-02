import QSB.JointFreshCandidates

/-!
Classical postprocessing after the attacker output is measured. Each pair is
queried at both coordinates and the input trace is returned alongside the
responses. This gives an explicit upper bound on *additional* verification
queries. It does not count setup, signing, or adversarial queries, establish
that the source extractor is efficient, or formalize a quantum oracle circuit.
-/
namespace QSB.JointFreshPostprocessing
open ByteMachine

variable {Ω Index SignedTx : Type*} [LinearOrder Index]

/-- Eagerly query both coordinates of each candidate pair and retain the
ordered query inputs. The outputs remain paired with their raw inputs. -/
def queryPairs (oracle : Bytes → Bytes) :
    List (Bytes × Bytes) →
      List ((Bytes × Bytes) × (Bytes × Bytes)) × List Bytes
  | [] => ([], [])
  | pair :: rest =>
      let response := (oracle pair.1, oracle pair.2)
      let remaining := queryPairs oracle rest
      ((pair, response) :: remaining.1,
        pair.1 :: pair.2 :: remaining.2)

theorem queryPairs_values (oracle : Bytes → Bytes)
    (pairs : List (Bytes × Bytes)) :
    (queryPairs oracle pairs).1 =
      pairs.map fun pair => (pair, (oracle pair.1, oracle pair.2)) := by
  induction pairs with
  | nil => rfl
  | cons head tail ih => simp [queryPairs, ih]

theorem queryPairs_trace (oracle : Bytes → Bytes)
    (pairs : List (Bytes × Bytes)) :
    (queryPairs oracle pairs).2 =
      pairs.flatMap fun pair => [pair.1, pair.2] := by
  induction pairs with
  | nil => rfl
  | cons head tail ih => simp [queryPairs, ih]

theorem queryPairs_trace_length (oracle : Bytes → Bytes)
    (pairs : List (Bytes × Bytes)) :
    (queryPairs oracle pairs).2.length = 2 * pairs.length := by
  rw [queryPairs_trace]
  induction pairs with
  | nil => simp
  | cons head tail ih => simp [ih]; omega

theorem queryPairs_response_mem (oracle : Bytes → Bytes)
    (pairs : List (Bytes × Bytes)) (pair : Bytes × Bytes)
    (member : pair ∈ pairs) :
    (pair, (oracle pair.1, oracle pair.2)) ∈
      (queryPairs oracle pairs).1 := by
  rw [queryPairs_values]
  exact List.mem_map.mpr ⟨pair, member, rfl⟩

/-- The H stage uses two classical H calls per raw pair. -/
def hStage (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) :=
  queryPairs (e.functions ω).H
    (JointFreshCandidates.openingPairs e ω)

/-- The R stage first obtains the two H outputs for each raw pair, then
queries R at each resulting input. Both ordered query traces are retained. -/
def rStages (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) :=
  let h := hStage e ω
  let r := queryPairs (e.functions ω).R (h.1.map Prod.snd)
  (h, r)

theorem hStage_trace_length_le [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (hStage e ω).2.length ≤ 2 * Fintype.card Index := by
  rw [hStage, queryPairs_trace_length]
  exact Nat.mul_le_mul_left 2
    (JointFreshCandidates.openingPairs_length_le e ω)

theorem rStages_h_trace_length_le [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (rStages e ω).1.2.length ≤ 2 * Fintype.card Index := by
  exact hStage_trace_length_le e ω

theorem rStages_r_trace_length_le [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (rStages e ω).2.2.length ≤ 2 * Fintype.card Index := by
  simp only [rStages]
  rw [queryPairs_trace_length]
  simp only [List.length_map]
  have count : (hStage e ω).1.length =
      (JointFreshCandidates.openingPairs e ω).length := by
    rw [hStage, queryPairs_values]
    simp
  rw [count]
  exact Nat.mul_le_mul_left 2
    (JointFreshCandidates.openingPairs_length_le e ω)

theorem rStages_total_trace_length_le [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (rStages e ω).1.2.length + (rStages e ω).2.2.length ≤
      4 * Fintype.card Index := by
  have hBound := rStages_h_trace_length_le e ω
  have rBound := rStages_r_trace_length_le e ω
  omega

theorem concrete_h_trace_length_le_300
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω) :
    (hStage e ω).2.length ≤ 300 := by
  simpa using hStage_trace_length_le e ω

theorem concrete_r_total_trace_length_le_600
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω) :
    (rStages e ω).1.2.length + (rStages e ω).2.2.length ≤ 600 := by
  simpa using rStages_total_trace_length_le e ω

/-- This scanner compares cached inputs and responses only. It makes no new
H call after `hStage` has produced its response list. -/
def hVerifiedPost (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) :
    Option ((Bytes × Bytes) × (Bytes × Bytes)) × Nat :=
  JointFreshCandidates.firstPassing
    (fun entry => decide (entry.1.1 ≠ entry.1.2 ∧
      entry.2.1 = entry.2.2))
    (hStage e ω).1

/-- The R-route scanner likewise compares only the cached R responses. -/
def rVerifiedPost (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) :
    Option ((Bytes × Bytes) × (Bytes × Bytes)) × Nat :=
  JointFreshCandidates.firstPassing
    (fun entry => decide (entry.1.1 ≠ entry.1.2 ∧
      entry.2.1 = entry.2.2))
    (rStages e ω).2.1

/-- One evaluation of H produces both the cached scan result and its actual
ordered query-input trace. -/
def hPostTranscript (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) :
    (Option ((Bytes × Bytes) × (Bytes × Bytes)) × Nat) × List Bytes :=
  let stage := hStage e ω
  (JointFreshCandidates.firstPassing
      (fun entry => decide (entry.1.1 ≠ entry.1.2 ∧
        entry.2.1 = entry.2.2)) stage.1,
    stage.2)

/-- The R route evaluates H, then R, and scans the cached R responses.
The returned traces identify every additional H and R input. -/
def rPostTranscript (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) :
    (Option ((Bytes × Bytes) × (Bytes × Bytes)) × Nat) ×
      (List Bytes × List Bytes) :=
  let stages := rStages e ω
  (JointFreshCandidates.firstPassing
      (fun entry => decide (entry.1.1 ≠ entry.1.2 ∧
        entry.2.1 = entry.2.2)) stages.2.1,
    (stages.1.2, stages.2.2))

theorem hPostTranscript_result
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (hPostTranscript e ω).1 = hVerifiedPost e ω := rfl

theorem rPostTranscript_result
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (rPostTranscript e ω).1 = rVerifiedPost e ω := rfl

theorem concrete_h_post_trace_length_le_300
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω) :
    (hPostTranscript e ω).2.length ≤ 300 := by
  simpa [hPostTranscript] using concrete_h_trace_length_le_300 e ω

theorem concrete_r_post_total_trace_length_le_600
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω) :
    (rPostTranscript e ω).2.1.length +
      (rPostTranscript e ω).2.2.length ≤ 600 := by
  simpa [rPostTranscript] using concrete_r_total_trace_length_le_600 e ω

theorem h_route_cached_post_succeeds
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (collision : JointFreshRoutes.reachedHCollision e ω) :
    ∃ entry count, hVerifiedPost e ω = (some entry, count) ∧
      entry.1.1 ≠ entry.1.2 ∧ entry.2.1 = entry.2.2 ∧
      entry.2 = ((e.functions ω).H entry.1.1,
        (e.functions ω).H entry.1.2) := by
  obtain ⟨pair, member, different, equalH⟩ :=
    JointFreshCandidates.reached_h_collision_in_pairs e ω collision
  have recordMember :
      (pair, ((e.functions ω).H pair.1,
        (e.functions ω).H pair.2)) ∈ (hStage e ω).1 :=
    queryPairs_response_mem _ _ pair member
  obtain ⟨entry, count, result, entryMember, passes⟩ :=
    JointFreshCandidates.firstPassing_finds
      (fun (entry : (Bytes × Bytes) × (Bytes × Bytes)) =>
        decide (entry.1.1 ≠ entry.1.2 ∧ entry.2.1 = entry.2.2))
      (hStage e ω).1
      ⟨(pair, ((e.functions ω).H pair.1,
        (e.functions ω).H pair.2)), recordMember,
        by simp [different, equalH]⟩
  have response : entry.2 = ((e.functions ω).H entry.1.1,
      (e.functions ω).H entry.1.2) := by
    rw [hStage, queryPairs_values] at entryMember
    obtain ⟨raw, _rawMember, same⟩ := List.mem_map.mp entryMember
    simp only [← same]
  have passFacts : entry.1.1 ≠ entry.1.2 ∧
      entry.2.1 = entry.2.2 := by simpa using passes
  exact ⟨entry, count, result, passFacts.1, passFacts.2, response⟩

theorem r_route_cached_post_succeeds
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (collision : JointFreshRoutes.reachedRCollision e ω) :
    ∃ entry count, rVerifiedPost e ω = (some entry, count) ∧
      entry.1.1 ≠ entry.1.2 ∧ entry.2.1 = entry.2.2 ∧
      entry.2 = ((e.functions ω).R entry.1.1,
        (e.functions ω).R entry.1.2) := by
  obtain ⟨pair, member, different, equalR⟩ :=
    JointFreshCandidates.reached_r_collision_in_pairs e ω collision
  have hInputs : (hStage e ω).1.map Prod.snd =
      JointFreshCandidates.rInputPairs e ω := by
    simp [hStage, queryPairs_values,
      JointFreshCandidates.rInputPairs, List.map_map]
  have recordMember :
      (pair, ((e.functions ω).R pair.1,
        (e.functions ω).R pair.2)) ∈ (rStages e ω).2.1 := by
    change (pair, ((e.functions ω).R pair.1,
      (e.functions ω).R pair.2)) ∈
      (queryPairs (e.functions ω).R
        ((hStage e ω).1.map Prod.snd)).1
    rw [hInputs]
    exact queryPairs_response_mem _ _ pair member
  obtain ⟨entry, count, result, entryMember, passes⟩ :=
    JointFreshCandidates.firstPassing_finds
      (fun (entry : (Bytes × Bytes) × (Bytes × Bytes)) =>
        decide (entry.1.1 ≠ entry.1.2 ∧ entry.2.1 = entry.2.2))
      (rStages e ω).2.1
      ⟨(pair, ((e.functions ω).R pair.1,
        (e.functions ω).R pair.2)), recordMember,
        by simp [different, equalR]⟩
  have response : entry.2 = ((e.functions ω).R entry.1.1,
      (e.functions ω).R entry.1.2) := by
    change entry ∈ (queryPairs (e.functions ω).R
      ((hStage e ω).1.map Prod.snd)).1 at entryMember
    rw [hInputs, queryPairs_values] at entryMember
    obtain ⟨raw, _rawMember, same⟩ := List.mem_map.mp entryMember
    simp only [← same]
  have passFacts : entry.1.1 ≠ entry.1.2 ∧
      entry.2.1 = entry.2.2 := by simpa using passes
  exact ⟨entry, count, result, passFacts.1, passFacts.2, response⟩

/-- The concrete H collision route produces a checked pair with a recorded
classical H-query trace of at most 300 additional inputs. -/
theorem concrete_h_route_post_success
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω)
    (collision : JointFreshRoutes.reachedHCollision e ω) :
    ∃ entry count,
      (hPostTranscript e ω).1 = (some entry, count) ∧
      entry.1.1 ≠ entry.1.2 ∧ entry.2.1 = entry.2.2 ∧
      entry.2 = ((e.functions ω).H entry.1.1,
        (e.functions ω).H entry.1.2) ∧
      (hPostTranscript e ω).2.length ≤ 300 := by
  obtain ⟨entry, count, result, different, equalH, response⟩ :=
    h_route_cached_post_succeeds e ω collision
  exact ⟨entry, count, (hPostTranscript_result e ω).trans result,
    different, equalH, response,
    concrete_h_post_trace_length_le_300 e ω⟩

/-- The concrete R collision route produces a checked pair after at most
300 additional H-input calls and 300 additional R-input calls. -/
theorem concrete_r_route_post_success
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω)
    (collision : JointFreshRoutes.reachedRCollision e ω) :
    ∃ entry count,
      (rPostTranscript e ω).1 = (some entry, count) ∧
      entry.1.1 ≠ entry.1.2 ∧ entry.2.1 = entry.2.2 ∧
      entry.2 = ((e.functions ω).R entry.1.1,
        (e.functions ω).R entry.1.2) ∧
      (rPostTranscript e ω).2.1.length +
        (rPostTranscript e ω).2.2.length ≤ 600 := by
  obtain ⟨entry, count, result, different, equalR, response⟩ :=
    r_route_cached_post_succeeds e ω collision
  exact ⟨entry, count, (rPostTranscript_result e ω).trans result,
    different, equalR, response,
    concrete_r_post_total_trace_length_le_600 e ω⟩

end QSB.JointFreshPostprocessing
