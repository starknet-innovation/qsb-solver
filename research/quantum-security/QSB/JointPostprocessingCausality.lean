import QSB.CausalQueryAlgorithm

/-!
Classical causality of fresh-opening collision postprocessing after its raw
candidate pairs are fixed. The R route first queries H on each raw pair and
uses those replies as its R-query inputs. Agreement on the recorded H queries
therefore aligns the later R queries; agreement on both recorded stages then
preserves the cached collision scan and the query trace.

The candidate list is an explicit input. In the security game,
`JointFreshCandidates.openingPairs` depends on a world-indexed extractor and
setup secrets; this module does not show that list is available to a causal
algorithm or charge the extractor's own oracle calls. It proves no quantum
transition or collision-probability bound.
-/
namespace QSB.JointPostprocessingCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)
open JointFreshPostprocessing

/-- Eagerly evaluating a fixed pair list consults only the returned input
trace, even when the two coordinates or different pairs repeat an input. -/
theorem queryPairs_congr (oracle oracle' : Bytes → Bytes) :
    ∀ (pairs : List (Bytes × Bytes)),
      (∀ x ∈ (queryPairs oracle pairs).2, oracle' x = oracle x) →
      queryPairs oracle' pairs = queryPairs oracle pairs
  | [], _ => rfl
  | pair :: rest, agree => by
      have first : oracle' pair.1 = oracle pair.1 :=
        agree pair.1 (by simp [queryPairs])
      have second : oracle' pair.2 = oracle pair.2 :=
        agree pair.2 (by simp [queryPairs])
      have tailAgree : ∀ x ∈ (queryPairs oracle rest).2,
          oracle' x = oracle x := by
        intro x member
        exact agree x (by simp [queryPairs, member])
      have tail := queryPairs_congr oracle oracle' rest tailAgree
      simp [queryPairs, first, second, tail]

/-- The H stage with a candidate list supplied independently of the oracle. -/
def fixedHStage (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) :=
  queryPairs functions.H pairs

/-- The R stage uses the recorded H replies, not fresh or independently
sampled values, as its ordered R inputs. -/
def fixedRStages (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) :=
  let h := fixedHStage functions pairs
  (h, queryPairs functions.R (h.1.map Prod.snd))

theorem fixedHStage_congr (functions functions' : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes))
    (agreeH : ∀ x ∈ (fixedHStage functions pairs).2,
      functions'.H x = functions.H x) :
    fixedHStage functions' pairs = fixedHStage functions pairs :=
  queryPairs_congr functions.H functions'.H pairs agreeH

/-- H-query agreement makes the adaptive R-query input list identical;
agreement on those recorded R inputs then makes both response caches equal. -/
theorem fixedRStages_congr
    (functions functions' : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes))
    (agreeH : ∀ x ∈ (fixedHStage functions pairs).2,
      functions'.H x = functions.H x)
    (agreeR : ∀ x ∈ (fixedRStages functions pairs).2.2,
      functions'.R x = functions.R x) :
    fixedRStages functions' pairs = fixedRStages functions pairs := by
  have sameH := fixedHStage_congr functions functions' pairs agreeH
  have sameR : queryPairs functions'.R
      ((fixedHStage functions pairs).1.map Prod.snd) =
        queryPairs functions.R
          ((fixedHStage functions pairs).1.map Prod.snd) := by
    apply queryPairs_congr
    simpa [fixedRStages] using agreeR
  simp [fixedRStages, sameH, sameR]

/-- Cached H-collision scan and its H-query inputs for fixed candidates. -/
def fixedHPost (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) :=
  let h := fixedHStage functions pairs
  (JointFreshCandidates.firstPassing
      (fun entry => decide (entry.1.1 ≠ entry.1.2 ∧
        entry.2.1 = entry.2.2)) h.1,
    h.2)

/-- Cached R-collision scan, with the H and R input traces retained. -/
def fixedRPost (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) :=
  let stages := fixedRStages functions pairs
  (JointFreshCandidates.firstPassing
      (fun entry => decide (entry.1.1 ≠ entry.1.2 ∧
        entry.2.1 = entry.2.2)) stages.2.1,
    (stages.1.2, stages.2.2))

theorem fixedHPost_congr
    (functions functions' : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes))
    (agreeH : ∀ x ∈ (fixedHStage functions pairs).2,
      functions'.H x = functions.H x) :
    fixedHPost functions' pairs = fixedHPost functions pairs := by
  simp [fixedHPost, fixedHStage_congr functions functions' pairs agreeH]

theorem fixedRPost_congr
    (functions functions' : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes))
    (agreeH : ∀ x ∈ (fixedHStage functions pairs).2,
      functions'.H x = functions.H x)
    (agreeR : ∀ x ∈ (fixedRStages functions pairs).2.2,
      functions'.R x = functions.R x) :
    fixedRPost functions' pairs = fixedRPost functions pairs := by
  simp [fixedRPost, fixedRStages_congr functions functions' pairs agreeH agreeR]

/-- One shared, tagged input trace for the fixed-candidate R route. -/
def fixedRTaggedTrace (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) : List Query :=
  ((fixedRStages functions pairs).1.2.map Query.H) ++
    ((fixedRStages functions pairs).2.2.map Query.R)

/-- The one tagged trace charges two H calls and two R calls per raw pair,
including repeated inputs. -/
theorem fixedRTaggedTrace_length (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) :
    (fixedRTaggedTrace functions pairs).length = 4 * pairs.length := by
  have hCount : (fixedHStage functions pairs).1.length = pairs.length := by
    rw [fixedHStage, queryPairs_values]
    simp
  have hTrace := queryPairs_trace_length functions.H pairs
  have rTrace := queryPairs_trace_length functions.R
    ((fixedHStage functions pairs).1.map Prod.snd)
  simp only [fixedRTaggedTrace, List.length_append, List.length_map,
    fixedRStages]
  simp only [fixedHStage] at hCount hTrace rTrace ⊢
  rw [hTrace, rTrace]
  simp only [List.length_map]
  omega

/-- Agreement on the one tagged trace preserves the adaptive postprocessor's
cached result and both input traces. -/
theorem fixedRPost_congr_tagged
    (functions functions' : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes))
    (agree : ∀ q ∈ fixedRTaggedTrace functions pairs,
      answer functions' q = answer functions q) :
    fixedRPost functions' pairs = fixedRPost functions pairs := by
  have agreeH : ∀ x ∈ (fixedHStage functions pairs).2,
      functions'.H x = functions.H x := by
    intro x member
    exact agree (.H x) (by simp [fixedRTaggedTrace, fixedRStages, member])
  have agreeR : ∀ x ∈ (fixedRStages functions pairs).2.2,
      functions'.R x = functions.R x := by
    intro x member
    exact agree (.R x) (by simp [fixedRTaggedTrace, member])
  exact fixedRPost_congr functions functions' pairs agreeH agreeR

/-- The same agreement also preserves the ordered tagged query inputs;
the R inputs remain aligned because the H replies are aligned first. -/
theorem fixedRTaggedTrace_congr
    (functions functions' : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes))
    (agree : ∀ q ∈ fixedRTaggedTrace functions pairs,
      answer functions' q = answer functions q) :
    fixedRTaggedTrace functions' pairs =
      fixedRTaggedTrace functions pairs := by
  have agreeH : ∀ x ∈ (fixedHStage functions pairs).2,
      functions'.H x = functions.H x := by
    intro x member
    exact agree (.H x) (by simp [fixedRTaggedTrace, fixedRStages, member])
  have agreeR : ∀ x ∈ (fixedRStages functions pairs).2.2,
      functions'.R x = functions.R x := by
    intro x member
    exact agree (.R x) (by simp [fixedRTaggedTrace, member])
  simp [fixedRTaggedTrace,
    fixedRStages_congr functions functions' pairs agreeH agreeR]

/-- The existing world-indexed postprocessor specializes to the explicit
candidate-list form; this equality alone does not make candidate generation
causal. -/
theorem fixedHPost_eq_hPostTranscript
    {Ω Index SignedTx : Type*} [LinearOrder Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    fixedHPost (e.functions ω) (JointFreshCandidates.openingPairs e ω) =
      hPostTranscript e ω := rfl

theorem fixedRPost_eq_rPostTranscript
    {Ω Index SignedTx : Type*} [LinearOrder Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω : Ω) :
    fixedRPost (e.functions ω) (JointFreshCandidates.openingPairs e ω) =
      rPostTranscript e ω := rfl

/-- The H route's tagged post-output queries for an explicit candidate list. -/
def fixedHTaggedTrace (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) : List Query :=
  (fixedHStage functions pairs).2.map Query.H

theorem fixedHTaggedTrace_length (functions : JointSourceChecks.Functions)
    (pairs : List (Bytes × Bytes)) :
    (fixedHTaggedTrace functions pairs).length = 2 * pairs.length := by
  simpa [fixedHTaggedTrace, fixedHStage] using
    queryPairs_trace_length functions.H pairs

/-- The world-indexed H postprocessor is causal once the extracted raw pair
list is supplied unchanged across the two worlds. The premise does not follow
from oracle agreement: the extractor and setup secrets can be world-indexed. -/
theorem hPostTranscript_congr_of_candidates_eq
    {Ω Index SignedTx : Type*} [LinearOrder Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω ω' : Ω)
    (sameCandidates : JointFreshCandidates.openingPairs e ω' =
      JointFreshCandidates.openingPairs e ω)
    (agree : ∀ q ∈ fixedHTaggedTrace (e.functions ω)
        (JointFreshCandidates.openingPairs e ω),
      answer (e.functions ω') q = answer (e.functions ω) q) :
    hPostTranscript e ω' = hPostTranscript e ω := by
  change fixedHPost (e.functions ω')
      (JointFreshCandidates.openingPairs e ω') =
    fixedHPost (e.functions ω)
      (JointFreshCandidates.openingPairs e ω)
  rw [sameCandidates]
  apply fixedHPost_congr
  intro x member
  exact agree (.H x) (by simp [fixedHTaggedTrace, member])

/-- The R-route cached collision result and both ordered input traces are
unchanged when the explicit candidate list and the first world's recorded
tagged H/R replies are unchanged. The tagged trace itself then agrees too. -/
theorem rPostTranscript_congr_of_candidates_eq
    {Ω Index SignedTx : Type*} [LinearOrder Index]
    (e : JointOracleReduction.Experiment Ω Index SignedTx) (ω ω' : Ω)
    (sameCandidates : JointFreshCandidates.openingPairs e ω' =
      JointFreshCandidates.openingPairs e ω)
    (agree : ∀ q ∈ fixedRTaggedTrace (e.functions ω)
        (JointFreshCandidates.openingPairs e ω),
      answer (e.functions ω') q = answer (e.functions ω) q) :
    rPostTranscript e ω' = rPostTranscript e ω ∧
      fixedRTaggedTrace (e.functions ω')
          (JointFreshCandidates.openingPairs e ω') =
        fixedRTaggedTrace (e.functions ω)
          (JointFreshCandidates.openingPairs e ω) := by
  constructor
  · change fixedRPost (e.functions ω')
        (JointFreshCandidates.openingPairs e ω') =
      fixedRPost (e.functions ω)
        (JointFreshCandidates.openingPairs e ω)
    rw [sameCandidates]
    exact fixedRPost_congr_tagged (e.functions ω) (e.functions ω')
      (JointFreshCandidates.openingPairs e ω) agree
  · rw [sameCandidates]
    exact fixedRTaggedTrace_congr (e.functions ω) (e.functions ω')
      (JointFreshCandidates.openingPairs e ω) agree

end QSB.JointPostprocessingCausality
