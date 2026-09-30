import Mathlib.Data.Finset.Card

/-!
Hash-opening facts, independent of Bitcoin and quantum assumptions.
`opened` is an extracted set of DISTINCT commitment positions. Extracting such a
set of the required cardinality from arbitrary production script executions is
a separate obligation; it is deliberately not an axiom here.
-/
namespace QSB

variable {Index Secret Digest : Type*} [DecidableEq Index]

def OpeningsValid (hash : Secret → Digest) (commitments : Index → Digest)
    (opened : Finset Index)
    (values : (i : Index) → i ∈ opened → Secret) : Prop :=
  ∀ i (h : i ∈ opened), hash (values i h) = commitments i

/-- A concrete output (position, value) opening a target not previously disclosed.
This is not an existential over arbitrary secrets: values come from the witness. -/
def FreshOpening (hash : Secret → Digest) (commitments : Index → Digest)
    (disclosed opened : Finset Index)
    (values : (i : Index) → i ∈ opened → Secret) : Prop :=
  ∃ i, ∃ h : i ∈ opened, i ∉ disclosed ∧
    hash (values i h) = commitments i

theorem openings_fresh_or_covered
    {hash : Secret → Digest} {commitments : Index → Digest}
    {disclosed opened : Finset Index}
    {values : (i : Index) → i ∈ opened → Secret}
    (valid : OpeningsValid hash commitments opened values) :
    FreshOpening hash commitments disclosed opened values ∨ opened ⊆ disclosed := by
  classical
  by_cases covered : opened ⊆ disclosed
  · exact Or.inr covered
  · left
    have existsIndex : ∃ i ∈ opened, i ∉ disclosed := by
      by_contra h
      apply covered
      intro i hi
      by_contra hn
      exact h ⟨i, hi, hn⟩
    obtain ⟨i, hi, hn⟩ := existsIndex
    exact ⟨i, hi, hn, valid i hi⟩

/-- With a single prior disclosure of exactly t distinct positions, a new
t-position valid opening either opens a fresh target or uses exactly that set. -/
theorem one_disclosure_fresh_or_same
    {hash : Secret → Digest} {commitments : Index → Digest}
    {disclosed opened : Finset Index}
    {values : (i : Index) → i ∈ opened → Secret}
    (valid : OpeningsValid hash commitments opened values)
    (sameCard : opened.card = disclosed.card) :
    FreshOpening hash commitments disclosed opened values ∨ opened = disclosed := by
  rcases openings_fresh_or_covered valid with fresh | covered
  · exact Or.inl fresh
  · exact Or.inr (Finset.eq_of_subset_of_card_le covered (by omega))

theorem insufficient_disclosure_requires_fresh
    {hash : Secret → Digest} {commitments : Index → Digest}
    {disclosed opened : Finset Index}
    {values : (i : Index) → i ∈ opened → Secret}
    (valid : OpeningsValid hash commitments opened values)
    (more : disclosed.card < opened.card) :
    FreshOpening hash commitments disclosed opened values := by
  rcases openings_fresh_or_covered valid with fresh | covered
  · exact fresh
  · have := Finset.card_le_card covered
    omega

/-- Accumulated disclosures are a union, including cancelled/unmined authorizations. -/
theorem covered_after_more_disclosure {opened old new : Finset Index}
    (covered : opened ⊆ old) : opened ⊆ old ∪ new := by
  exact Finset.Subset.trans covered Finset.subset_union_left

end QSB
