import QSB.JointFreshRoutes

/-!
Finite, deterministic candidate lists for the reached fresh-opening collision
routes. The challenger knows the sampled setup secrets; the transaction
extractor supplies the attacker's opening bytes. The lists include every
signed position without inspecting which one collides. Converting this
classical enumeration into a quantum collision-finder still requires a causal
oracle algorithm and must charge any H evaluations used to form R inputs.
-/
namespace QSB.JointFreshCandidates
open ByteMachine

variable {Ω Index SignedTx : Type*} [LinearOrder Index]

/-- Enumerate all extracted signed opening/setup-secret pairs. The list is
empty when extraction fails; no oracle equality test chooses a pair. -/
def openingPairs (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) : List (Bytes × Bytes) :=
  match e.extractor ω (e.output ω) with
  | none => []
  | some (_, w) =>
      (w.signed.attach.sort (· ≤ ·)).map fun signed =>
        (w.opening signed.val signed.property, e.secrets ω signed.val)

/-- The potential input pairs for a collision of R. Forming these pairs
reads H at the candidate and secret inputs; a quantum reduction must charge
those reads unless the values are already in its causal transcript. -/
def rInputPairs (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) : List (Bytes × Bytes) :=
  (openingPairs e ω).map fun pair =>
    ((e.functions ω).H pair.1, (e.functions ω).H pair.2)

theorem openingPairs_length_le [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (openingPairs e ω).length ≤ Fintype.card Index := by
  cases extracted : e.extractor ω (e.output ω) with
  | none => simp [openingPairs, extracted]
  | some result =>
      rcases result with ⟨pinKey, w⟩
      have count : w.signed.card ≤ Fintype.card Index :=
        Finset.card_le_univ _
      simpa [openingPairs, extracted] using count

theorem rInputPairs_length_le [Fintype Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    (rInputPairs e ω).length ≤ Fintype.card Index := by
  simpa [rInputPairs] using openingPairs_length_le e ω

theorem reached_pair_mem
    (e : JointOracleReduction.Experiment Ω Index SignedTx)
    (ω : Ω) (i : Index) (candidate : Bytes)
    (reached : JointFreshRoutes.reachedOpening e ω i candidate) :
    (candidate, e.secrets ω i) ∈ openingPairs e ω := by
  obtain ⟨_, pinKey, w, membership, extracted,
    _, candidateEq, _⟩ := reached
  simp only [openingPairs, extracted]
  apply List.mem_map.mpr
  refine ⟨⟨i, membership⟩, ?_, ?_⟩
  · simp
  · simp [candidateEq]

theorem exact_secret_in_pairs
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (recovered : JointFreshRoutes.exactSecret e ω) :
    ∃ pair ∈ openingPairs e ω, pair.1 = pair.2 := by
  obtain ⟨i, candidate, reached, same⟩ := recovered
  exact ⟨(candidate, e.secrets ω i),
    reached_pair_mem e ω i candidate reached, same⟩

theorem reached_h_collision_in_pairs
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (collision : JointFreshRoutes.reachedHCollision e ω) :
    ∃ pair ∈ openingPairs e ω,
      pair.1 ≠ pair.2 ∧
      (e.functions ω).H pair.1 = (e.functions ω).H pair.2 := by
  obtain ⟨i, candidate, reached, different, equalH⟩ := collision
  exact ⟨(candidate, e.secrets ω i),
    reached_pair_mem e ω i candidate reached, different, equalH⟩

theorem reached_r_collision_in_pairs
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω)
    (collision : JointFreshRoutes.reachedRCollision e ω) :
    ∃ pair ∈ rInputPairs e ω,
      pair.1 ≠ pair.2 ∧
      (e.functions ω).R pair.1 = (e.functions ω).R pair.2 := by
  obtain ⟨i, candidate, reached, differentH⟩ := collision
  have rawMember := reached_pair_mem e ω i candidate reached
  have rMember :
      ((e.functions ω).H candidate,
        (e.functions ω).H (e.secrets ω i)) ∈ rInputPairs e ω := by
    exact List.mem_map.mpr
      ⟨(candidate, e.secrets ω i), rawMember, rfl⟩
  obtain ⟨_, pinKey, w, membership, extracted, undisclosed,
    candidateEq, matched⟩ := reached
  exact ⟨((e.functions ω).H candidate,
    (e.functions ω).H (e.secrets ω i)), rMember,
    differentH, matched⟩

end QSB.JointFreshCandidates
