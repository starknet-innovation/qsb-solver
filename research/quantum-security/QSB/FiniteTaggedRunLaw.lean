import QSB.FiniteTaggedCombinedRun

/-!
For one fixed classical combined machine, a uniformly chosen finite tagged
product table induces the same run law as a uniformly chosen pair of its
observable H and R tables. The unused response coordinates have constant
fibers, and the complete run depends only on the observable coordinates.

This is a finite counting statement at the existential input cap of the fixed
machine. It does not supply a law for a variable adversary, an infinite random
oracle, coherent queries, or a QROM security bound.
-/
namespace QSB.FiniteTaggedRunLaw
open ByteMachine
open TaggedOracle (Bits)
open CausalQueryAlgorithm (Machine run)

variable {S : Type*}

private theorem functions_ext (left right : JointSourceChecks.Functions)
    (sameH : left.H = right.H) (sameR : left.R = right.R) :
    left = right := by
  cases left with
  | mk leftH leftR leftWidthH leftWidthR =>
    cases right with
    | mk rightH rightR rightWidthH rightWidthR =>
      dsimp at sameH sameR
      cases sameH
      cases sameR
      rfl

abbrev Input
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :=
  FiniteTaggedCombinedRun.Input first q initial

abbrev Table
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :=
  FiniteTaggedCombinedRun.TaggedTable first q initial

abbrev Observed
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :=
  (Input first q initial → Bits 256) × (Input first q initial → Bits 160)

abbrev Filler
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :=
  (Input first q initial → Bits 160) × (Input first q initial → Bits 256)

/-- A canonical table fills unused coordinates with zero. -/
def canonicalTable
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (pair : Observed first q initial) : Table first q initial :=
  (TaggedOracle.splitEquiv).symm
    (pair, (fun _ => TaggedOracle.zeroBits 160,
            fun _ => TaggedOracle.zeroBits 256))

theorem observed_canonicalTable
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (pair : Observed first q initial) :
    TaggedOracle.observed (canonicalTable first q initial pair) = pair := by
  change ((TaggedOracle.splitEquiv).symm
    (pair, (fun _ : Input first q initial => TaggedOracle.zeroBits 160,
            fun _ : Input first q initial => TaggedOracle.zeroBits 256))
      |> TaggedOracle.splitEquiv).1 = pair
  simp

/-- Changing only unused table coordinates leaves the total realized source
functions unchanged, including their zero defaults outside the cap. -/
theorem realize_eq_of_observed_eq
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (left right : Table first q initial)
    (same : TaggedOracle.observed left = TaggedOracle.observed right) :
    FiniteTaggedCombinedRun.realize first q initial left =
      FiniteTaggedCombinedRun.realize first q initial right := by
  apply functions_ext
  · funext input
    simp [FiniteTaggedCombinedRun.realize,
      FiniteTaggedCombinedRun.totalH, same]
  · funext input
    simp [FiniteTaggedCombinedRun.realize,
      FiniteTaggedCombinedRun.totalR, same]

/-- The entire classical result and ordered query-response log factor through
the two observed finite tables, even when the run fails or times out. -/
theorem run_eq_canonical_observed
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (table : Table first q initial) :
    run (CausalLedgerExtractorSequence.machine first)
        (FiniteTaggedCombinedRun.realize first q initial table)
        (q + 1697) (.inl initial) =
      run (CausalLedgerExtractorSequence.machine first)
        (FiniteTaggedCombinedRun.realize first q initial
          (canonicalTable first q initial (TaggedOracle.observed table)))
        (q + 1697) (.inl initial) := by
  rw [realize_eq_of_observed_eq first q initial table
    (canonicalTable first q initial (TaggedOracle.observed table))]
  exact (observed_canonicalTable first q initial _).symm

/-- For any predicate on the observable H/R tables, the tables satisfying it
are in bijection with satisfying observable pairs and arbitrary filler. -/
def selectedEquiv
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (P : Observed first q initial → Prop) :
    {table : Table first q initial // P (TaggedOracle.observed table)} ≃
      {pair : Observed first q initial // P pair} ×
        Filler first q initial where
  toFun table :=
    (⟨(TaggedOracle.splitEquiv table.1).1,
      by simpa only [TaggedOracle.split_observed] using table.2⟩,
      (TaggedOracle.splitEquiv table.1).2)
  invFun pair :=
    ⟨TaggedOracle.splitEquiv.symm (pair.1.1, pair.2), by
      change P (TaggedOracle.splitEquiv
        (TaggedOracle.splitEquiv.symm (pair.1.1, pair.2))).1
      simpa using pair.1.2⟩
  left_inv table := by
    apply Subtype.ext
    exact TaggedOracle.splitEquiv.symm_apply_apply table.1
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · simp

/-- A uniformly sampled finite tagged table gives the same density for every
event on its H/R observations as uniform sampling of the observable pair.
The equation is in exact natural-number counts, avoiding any normalization or
measure assumptions. -/
theorem selected_count
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (P : Observed first q initial → Prop) :
    Nat.card {table : Table first q initial //
      P (TaggedOracle.observed table)} =
      Nat.card {pair : Observed first q initial // P pair} *
        Nat.card (Filler first q initial) := by
  rw [Nat.card_congr (selectedEquiv first q initial P), Nat.card_prod]

/-- The complete tagged-table sample space has the same constant-fiber
factorization. Together with `selected_count`, this identifies the exact
finite run law for every event that factors through the observed H/R pair. -/
theorem table_count
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S) :
    Nat.card (Table first q initial) =
      Nat.card (Observed first q initial) *
        Nat.card (Filler first q initial) := by
  rw [Nat.card_congr (TaggedOracle.splitEquiv :
    Table first q initial ≃
      Observed first q initial × Filler first q initial), Nat.card_prod]

/-- Every predicate on realized source functions has the same finite
constant-fiber count when sampled from product tables or observable pairs. -/
theorem realized_event_count
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (event : JointSourceChecks.Functions → Prop) :
    Nat.card {table : Table first q initial //
      event (FiniteTaggedCombinedRun.realize first q initial table)} =
      Nat.card {pair : Observed first q initial //
        event (FiniteTaggedCombinedRun.realize first q initial
          (canonicalTable first q initial pair))} *
        Nat.card (Filler first q initial) := by
  let P : Observed first q initial → Prop := fun pair =>
    event (FiniteTaggedCombinedRun.realize first q initial
      (canonicalTable first q initial pair))
  have agree (table : Table first q initial) :
      event (FiniteTaggedCombinedRun.realize first q initial table) ↔
        P (TaggedOracle.observed table) := by
    unfold P
    rw [realize_eq_of_observed_eq first q initial table
      (canonicalTable first q initial (TaggedOracle.observed table))
      (observed_canonicalTable first q initial _).symm]
  let eventEquiv :
      {table : Table first q initial //
        event (FiniteTaggedCombinedRun.realize first q initial table)} ≃
      {table : Table first q initial //
        P (TaggedOracle.observed table)} :=
    { toFun := fun table => ⟨table.1, (agree table.1).mp table.2⟩
      invFun := fun table => ⟨table.1, (agree table.1).mpr table.2⟩
      left_inv := by intro table; apply Subtype.ext; rfl
      right_inv := by intro table; apply Subtype.ext; rfl }
  calc
    _ = Nat.card {table : Table first q initial //
          P (TaggedOracle.observed table)} := Nat.card_congr eventEquiv
    _ = Nat.card {pair : Observed first q initial // P pair} *
          Nat.card (Filler first q initial) := selected_count first q initial P
    _ = _ := rfl

abbrev RunObservation :=
  Option (CausalLedgerExtractorSequence.FirstOutput ×
    Option (Bytes × RoundWitness (Fin 150) Bytes Bytes)) ×
      List (CausalQueryAlgorithm.Query × Bytes)

/-- Every event on the complete combined classical run, including its ordered
H/R query-response log and failure or timeout outcome, has the same finite
sampling density under a uniform product-valued tagged table as under a
uniform pair of observed H/R tables. This equation gives the numerator and
the common filler factor; `table_count` gives the denominator. -/
theorem run_event_count
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (event : RunObservation → Prop) :
    Nat.card {table : Table first q initial //
      event (run (CausalLedgerExtractorSequence.machine first)
        (FiniteTaggedCombinedRun.realize first q initial table)
        (q + 1697) (.inl initial))} =
      Nat.card {pair : Observed first q initial //
        event (run (CausalLedgerExtractorSequence.machine first)
          (FiniteTaggedCombinedRun.realize first q initial
            (canonicalTable first q initial pair))
          (q + 1697) (.inl initial))} *
        Nat.card (Filler first q initial) := by
  exact realized_event_count first q initial (fun functions =>
    event (run (CausalLedgerExtractorSequence.machine first) functions
      (q + 1697) (.inl initial)))

/-- Cross multiplication states equality of the two finite uniform run
probabilities without choosing a rational or real normalization. -/
theorem run_event_density_cross_mul
    (first : Machine S CausalLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (event : RunObservation → Prop) :
    Nat.card {table : Table first q initial //
      event (run (CausalLedgerExtractorSequence.machine first)
        (FiniteTaggedCombinedRun.realize first q initial table)
        (q + 1697) (.inl initial))} *
      Nat.card (Observed first q initial) =
    Nat.card {pair : Observed first q initial //
      event (run (CausalLedgerExtractorSequence.machine first)
        (FiniteTaggedCombinedRun.realize first q initial
          (canonicalTable first q initial pair))
        (q + 1697) (.inl initial))} *
      Nat.card (Table first q initial) := by
  rw [run_event_count first q initial event, table_count first q initial]
  ac_rfl

end QSB.FiniteTaggedRunLaw
