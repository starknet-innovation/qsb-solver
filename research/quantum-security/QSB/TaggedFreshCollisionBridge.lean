import QSB.JointFreshPostprocessing
import QSB.TaggedOracle
import QSB.FixedWidthOracleEncoding

/-!
Connect a reached fresh-opening collision reported by the deterministic
postprocessor to a collision of the appropriate projection of a tagged,
product-valued oracle. The two tagged inputs are distinct, and the
postprocessor's verification calls remain explicitly charged.

The `realizesH` and `realizesR` premises are pointwise representation
contracts. This module does not construct a uniformly sampled finite tagged
oracle from the source byte functions, encode all byte inputs, simulate
coherent queries, or apply a compressed-oracle probability theorem.
-/
namespace QSB.TaggedFreshCollisionBridge
open ByteMachine

variable {Ω SignedTx : Type*}

/-- Embed the source H/R pair into the observed coordinates of a tagged bit
oracle using the proved exact-width encoders. Filler coordinates are explicit;
this deterministic construction is not a uniform tagged-oracle sample. -/
def sourceTagged (functions : JointSourceChecks.Functions)
    (leftFiller : Bytes → TaggedOracle.Bits 160)
    (rightFiller : Bytes → TaggedOracle.Bits 256) :
    Sum Bytes Bytes → TaggedOracle.Bits 256 × TaggedOracle.Bits 160
  | .inl x => (FixedWidthOracleEncoding.encodeHValue functions x,
      leftFiller x)
  | .inr x => (rightFiller x,
      FixedWidthOracleEncoding.encodeRValue functions x)

theorem observed_sourceTagged (functions : JointSourceChecks.Functions)
    (leftFiller : Bytes → TaggedOracle.Bits 160)
    (rightFiller : Bytes → TaggedOracle.Bits 256) :
    TaggedOracle.observed (sourceTagged functions leftFiller rightFiller) =
      (FixedWidthOracleEncoding.encodeHValue functions,
       FixedWidthOracleEncoding.encodeRValue functions) := by
  apply Prod.ext <;> funext x <;> rfl

/-- A reached H collision supplies distinct left-tag inputs with the same
first projected response. The encoded bit outputs are tied pointwise to the
source H responses; uniform sampling is a separate obligation. -/
theorem reached_h_tagged_collision
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω)
    (oracle : Sum Bytes Bytes →
      TaggedOracle.Bits 256 × TaggedOracle.Bits 160)
    (encodeH : Bytes → TaggedOracle.Bits 256)
    (realizesH : ∀ x : Bytes,
      (oracle (.inl x)).1 = encodeH ((e.functions ω).H x))
    (collision : JointFreshRoutes.reachedHCollision e ω) :
    ∃ entry count,
      (JointFreshPostprocessing.hPostTranscript e ω).1 =
        (some entry, count) ∧
      (Sum.inl entry.1.1 : Sum Bytes Bytes) ≠
        Sum.inl entry.1.2 ∧
      TaggedOracle.projectedH (.inl entry.1.1)
        (oracle (.inl entry.1.1)) =
        TaggedOracle.projectedH (.inl entry.1.2)
          (oracle (.inl entry.1.2)) ∧
      (JointFreshPostprocessing.hPostTranscript e ω).2.length ≤ 300 := by
  obtain ⟨entry, count, result, different, equalH, response, bound⟩ :=
    JointFreshPostprocessing.concrete_h_route_post_success e ω collision
  have sourceEqual : (e.functions ω).H entry.1.1 =
      (e.functions ω).H entry.1.2 := by
    have left := congrArg Prod.fst response
    have right := congrArg Prod.snd response
    exact left.symm.trans (equalH.trans right)
  refine ⟨entry, count, result, ?_, ?_, bound⟩
  · simpa using different
  · simp only [TaggedOracle.projectedH, realizesH]
    exact congrArg encodeH sourceEqual

/-- A reached R collision supplies distinct right-tag inputs with the same
second projected response. Forming the R inputs already costs H queries,
which remain in the postprocessor's combined 600-call allowance. -/
theorem reached_r_tagged_collision
    (e : JointOracleReduction.Experiment Ω (Fin 150) SignedTx) (ω : Ω)
    (oracle : Sum Bytes Bytes →
      TaggedOracle.Bits 256 × TaggedOracle.Bits 160)
    (encodeR : Bytes → TaggedOracle.Bits 160)
    (realizesR : ∀ x : Bytes,
      (oracle (.inr x)).2 = encodeR ((e.functions ω).R x))
    (collision : JointFreshRoutes.reachedRCollision e ω) :
    ∃ entry count,
      (JointFreshPostprocessing.rPostTranscript e ω).1 =
        (some entry, count) ∧
      (Sum.inr entry.1.1 : Sum Bytes Bytes) ≠
        Sum.inr entry.1.2 ∧
      TaggedOracle.projectedR (.inr entry.1.1)
        (oracle (.inr entry.1.1)) =
        TaggedOracle.projectedR (.inr entry.1.2)
          (oracle (.inr entry.1.2)) ∧
      (JointFreshPostprocessing.rPostTranscript e ω).2.1.length +
        (JointFreshPostprocessing.rPostTranscript e ω).2.2.length ≤
          600 := by
  obtain ⟨entry, count, result, different, equalR, response, bound⟩ :=
    JointFreshPostprocessing.concrete_r_route_post_success e ω collision
  have sourceEqual : (e.functions ω).R entry.1.1 =
      (e.functions ω).R entry.1.2 := by
    have left := congrArg Prod.fst response
    have right := congrArg Prod.snd response
    exact left.symm.trans (equalR.trans right)
  refine ⟨entry, count, result, ?_, ?_, bound⟩
  · simpa using different
  · simp only [TaggedOracle.projectedR, realizesR]
    exact congrArg encodeR sourceEqual

end QSB.TaggedFreshCollisionBridge
