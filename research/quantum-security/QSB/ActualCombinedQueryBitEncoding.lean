import QSB.ActualQueryBitEncoding
import QSB.CausalLedgerExtractorSequence

/-!
For one fixed first-stage classical machine, initial state, and query budget,
the entire sequential first-stage/ledger-extractor run has a common finite
tagged input register across all H/R worlds. This applies to the requests
actually issued by the combined machine, including both phases and failure
outcomes. The register retains the H/R tag and exact queried bytes.

The existential byte bound can depend on the fixed first machine and initial
state, including any oracle advice embedded there. It is not numeric or
uniform over adversarially varying first machines or states. These results do
not construct a sampled finite-oracle game, an efficient reversible circuit,
a coherent-query charge, or a QROM security bound. Hidden setup and callback
work remains outside the explicit classical query log.
-/
namespace QSB.ActualCombinedQueryBitEncoding
open ByteMachine
open CausalQueryAlgorithm (Query Machine run answer)

variable {S : Type*}

/-- A single byte cap for every actual request in every world of one fixed
combined classical run. -/
structure FixedCombinedEncoding
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) where
  bound : Nat
  covers : ∀ functions : JointSourceChecks.Functions,
    ∀ entry ∈
      (run (CausalLedgerExtractorSequence.machine first) functions
        (q + 1697) (.inl initial)).2,
      entry.1.input.length ≤ bound

noncomputable def fixedCombinedEncoding
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :
    FixedCombinedEncoding first q initial :=
  { bound := Classical.choose
      (CausalLedgerExtractorSequence.fixed_combined_machine_input_bound
        first q initial)
    covers := Classical.choose_spec
      (CausalLedgerExtractorSequence.fixed_combined_machine_input_bound
        first q initial) }

/-- Encode one query from the actual combined run into the fixed register:
one H/R tag bit, one-hot byte length, and a padded byte payload. -/
noncomputable def encodeActual
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions : JointSourceChecks.Functions)
    (entry : Query × Bytes)
    (member : entry ∈
      (run (CausalLedgerExtractorSequence.machine first) functions
        (q + 1697) (.inl initial)).2) :
    TaggedOracle.Bits
      (1 + (((fixedCombinedEncoding first q initial).bound + 1) +
        (fixedCombinedEncoding first q initial).bound * 8)) :=
  ActualQueryBitEncoding.encode
    ⟨entry.1,
      (fixedCombinedEncoding first q initial).covers functions entry member⟩

/-- Across worlds of this one fixed combined machine, equal register values
identify precisely the same tagged H/R query; the response bytes may differ. -/
theorem encodeActual_eq_iff
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions functions' : JointSourceChecks.Functions)
    (entry entry' : Query × Bytes)
    (member : entry ∈
      (run (CausalLedgerExtractorSequence.machine first) functions
        (q + 1697) (.inl initial)).2)
    (member' : entry' ∈
      (run (CausalLedgerExtractorSequence.machine first) functions'
        (q + 1697) (.inl initial)).2) :
    encodeActual first q initial functions entry member =
      encodeActual first q initial functions' entry' member' ↔
        entry.1 = entry'.1 := by
  simp only [encodeActual, ActualQueryBitEncoding.encode_eq_iff]

/-- Agreement of both H and R on the finite bounded-byte domain determines
the entire combined classical run, including its output and ordered log. -/
theorem run_congr_on_bounded_inputs
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (functions functions' : JointSourceChecks.Functions)
    (agreeH : ∀ input : Bytes,
      input.length ≤ (fixedCombinedEncoding first q initial).bound →
        functions'.H input = functions.H input)
    (agreeR : ∀ input : Bytes,
      input.length ≤ (fixedCombinedEncoding first q initial).bound →
        functions'.R input = functions.R input) :
    run (CausalLedgerExtractorSequence.machine first) functions'
        (q + 1697) (.inl initial) =
      run (CausalLedgerExtractorSequence.machine first) functions
        (q + 1697) (.inl initial) := by
  apply CausalQueryAlgorithm.run_congr
  intro entry member
  cases query : entry.1 with
  | H input =>
      have bounded :=
        (fixedCombinedEncoding first q initial).covers functions entry member
      simpa [answer, query] using
        agreeH input (by simpa [Query.input, query] using bounded)
  | R input =>
      have bounded :=
        (fixedCombinedEncoding first q initial).covers functions entry member
      simpa [answer, query] using
        agreeR input (by simpa [Query.input, query] using bounded)

end QSB.ActualCombinedQueryBitEncoding
