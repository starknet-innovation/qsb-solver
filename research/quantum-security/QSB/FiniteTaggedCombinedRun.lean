import QSB.ActualCombinedQueryBitEncoding
import QSB.FixedWidthOracleEncoding
import QSB.TaggedOracle

/-!
Deterministic finite-domain factorization of one fixed combined classical
transcript/ledger-extractor run. Finite branching supplies one existential
byte cap for every query actually issued at the fixed fuel. On that bounded
domain, an H/R source-function pair becomes a product-valued tagged oracle
with separate H and R input tags and exact 256/160-bit observed responses.
Conversely, a tagged table is decoded into width-correct total byte functions,
using fixed zero defaults outside the bounded domain. Restricting and then
realizing a source-function pair leaves the entire combined run unchanged.

The cap can depend on the fixed first machine and initial state, including
oracle advice they contain. This is a deterministic classical-run theorem,
not a law for sampled finite or infinite oracles, an efficient reversible
implementation, a coherent-query/QROM charge, or a security bound. Setup and
callback work hidden outside the recorded machine remain uncharged.
-/
namespace QSB.FiniteTaggedCombinedRun
open ByteMachine
open CausalQueryAlgorithm (Machine run)
open TaggedOracle (Bits)

variable {S : Type*}

/-- The same nonnumeric cap is used in every world of this fixed combined
classical machine. -/
noncomputable def queryCap
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) : Nat :=
  (ActualCombinedQueryBitEncoding.fixedCombinedEncoding first q initial).bound

abbrev Input
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :=
  BoundedInputEncoding.BoundedBytes (queryCap first q initial)

/-- One finite product-valued oracle with disjoint H and R input tags. -/
abbrev TaggedTable
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :=
  Sum (Input first q initial) (Input first q initial) → Bits 256 × Bits 160

/-- The finite table domain and exact-width response registers make the set
of tagged tables finite, even though its size is not evaluated here. -/
noncomputable instance taggedTableFintype
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :
    Fintype (TaggedTable first q initial) := inferInstance

/-- Restrict both observed source functions to bounded bytes and fill the
unused product coordinate at each tag with zero bits. -/
noncomputable def restrict
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions : JointSourceChecks.Functions) :
    TaggedTable first q initial
  | .inl input =>
      (FixedWidthOracleEncoding.encodeHValue functions input.1,
        TaggedOracle.zeroBits 160)
  | .inr input =>
      (TaggedOracle.zeroBits 256,
        FixedWidthOracleEncoding.encodeRValue functions input.1)

/-- The tagged product oracle exposes exactly the bounded H and R tables. -/
theorem observed_restrict
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions : JointSourceChecks.Functions) :
    TaggedOracle.observed (restrict first q initial functions) =
      ((fun input : Input first q initial =>
          FixedWidthOracleEncoding.encodeHValue functions input.1),
       (fun input : Input first q initial =>
          FixedWidthOracleEncoding.encodeRValue functions input.1)) := by
  rfl

/-- Decode one H table entry, or use a fixed width-correct zero default
outside the bounded byte domain. -/
noncomputable def totalH
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (table : TaggedTable first q initial) (input : Bytes) :
    FixedWidthOracleEncoding.FixedBytes 32 :=
  if bounded : input.length ≤ queryCap first q initial then
    (FixedWidthOracleEncoding.encodingEquiv 32).symm
      ((TaggedOracle.observed table).1 ⟨input, bounded⟩)
  else ⟨List.replicate 32 0, by simp⟩

/-- Decode one R table entry, or use a fixed width-correct zero default
outside the bounded byte domain. -/
noncomputable def totalR
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (table : TaggedTable first q initial) (input : Bytes) :
    FixedWidthOracleEncoding.FixedBytes 20 :=
  if bounded : input.length ≤ queryCap first q initial then
    (FixedWidthOracleEncoding.encodingEquiv 20).symm
      ((TaggedOracle.observed table).2 ⟨input, bounded⟩)
  else ⟨List.replicate 20 0, by simp⟩

/-- Every finite tagged table yields a total source-model function pair with
the exact output widths required by the source interface. -/
noncomputable def realize
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (table : TaggedTable first q initial) :
    JointSourceChecks.Functions where
  H := fun input => (totalH first q initial table input).1
  R := fun input => (totalR first q initial table input).1
  H_width := fun input => (totalH first q initial table input).2
  R_width := fun input => (totalR first q initial table input).2

theorem realize_restrict_H
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions : JointSourceChecks.Functions)
    (input : Bytes) (bounded : input.length ≤ queryCap first q initial) :
    (realize first q initial (restrict first q initial functions)).H input =
      functions.H input := by
  change (totalH first q initial
    (restrict first q initial functions) input).1 = functions.H input
  simp only [totalH, dif_pos bounded]
  have decoded := FixedWidthOracleEncoding.decode_encode
    (⟨functions.H input, functions.H_width input⟩ :
      FixedWidthOracleEncoding.FixedBytes 32)
  simpa [restrict, TaggedOracle.observed,
    FixedWidthOracleEncoding.encodeHValue,
    FixedWidthOracleEncoding.encodeH] using congrArg Subtype.val decoded

theorem realize_restrict_R
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions : JointSourceChecks.Functions)
    (input : Bytes) (bounded : input.length ≤ queryCap first q initial) :
    (realize first q initial (restrict first q initial functions)).R input =
      functions.R input := by
  change (totalR first q initial
    (restrict first q initial functions) input).1 = functions.R input
  simp only [totalR, dif_pos bounded]
  have decoded := FixedWidthOracleEncoding.decode_encode
    (⟨functions.R input, functions.R_width input⟩ :
      FixedWidthOracleEncoding.FixedBytes 20)
  simpa [restrict, TaggedOracle.observed,
    FixedWidthOracleEncoding.encodeRValue,
    FixedWidthOracleEncoding.encodeR] using congrArg Subtype.val decoded

/-- The fixed combined run factors through the finite tagged H/R table:
restricting a source pair and realizing that table preserves the exact output
and ordered query-response log, including timeout or failure outcomes. -/
theorem run_restrict_realize_eq
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions : JointSourceChecks.Functions) :
    run (CausalLedgerExtractorSequence.machine first)
        (realize first q initial (restrict first q initial functions))
        (q + 1697) (.inl initial) =
      run (CausalLedgerExtractorSequence.machine first) functions
        (q + 1697) (.inl initial) := by
  apply ActualCombinedQueryBitEncoding.run_congr_on_bounded_inputs
  · intro input bounded
    exact realize_restrict_H first q initial functions input
      (by simpa [queryCap] using bounded)
  · intro input bounded
    exact realize_restrict_R first q initial functions input
      (by simpa [queryCap] using bounded)

end QSB.FiniteTaggedCombinedRun
