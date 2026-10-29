import QSB.FiniteBranchingInputBound
import QSB.FixedWidthOracleEncoding
import QSB.TaggedOracle
import QSB.CausalPushOnlyLedgerExtractorSequence

/-!
A finite random-table interface for any one fixed classical H/R query machine,
including the push-only transcript/ledger extractor at `q + 1295` fuel. The
input cap comes from the machine's finite response tree and may depend on its
fixed initial state or oracle advice. Restriction to the cap preserves the
entire actual run. A tagged product table and its observed H/R pair give the
same finite event density because unused coordinates are constant-size filler.

This is a law for a fixed classical machine, not for an oracle-dependent
choice of machine, an infinite random oracle, or coherent quantum queries.
-/
namespace QSB.FiniteClassicalRunLaw
open ByteMachine
open CausalQueryAlgorithm (Query Machine run answer)
open TaggedOracle (Bits)

variable {State Out : Type*}

noncomputable def queryCap (machine : Machine State Out)
    (fuel : Nat) (initial : State) : Nat :=
  Classical.choose
    (FiniteBranchingInputBound.exists_run_input_bound machine fuel initial)

theorem queryCap_covers (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (functions : JointSourceChecks.Functions)
    (entry : Query × Bytes)
    (member : entry ∈ (run machine functions fuel initial).2) :
    entry.1.input.length ≤ queryCap machine fuel initial :=
  (Classical.choose_spec
    (FiniteBranchingInputBound.exists_run_input_bound machine fuel initial))
      functions entry member

abbrev Input (machine : Machine State Out) (fuel : Nat)
    (initial : State) :=
  BoundedInputEncoding.BoundedBytes (queryCap machine fuel initial)

abbrev Table (machine : Machine State Out) (fuel : Nat)
    (initial : State) :=
  Sum (Input machine fuel initial) (Input machine fuel initial) →
    Bits 256 × Bits 160

abbrev Observed (machine : Machine State Out) (fuel : Nat)
    (initial : State) :=
  (Input machine fuel initial → Bits 256) ×
    (Input machine fuel initial → Bits 160)

abbrev Filler (machine : Machine State Out) (fuel : Nat)
    (initial : State) :=
  (Input machine fuel initial → Bits 160) ×
    (Input machine fuel initial → Bits 256)

/-- Project exact-width source replies into the observed H/R coordinates. -/
noncomputable def restrict (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (functions : JointSourceChecks.Functions) :
    Table machine fuel initial
  | .inl input =>
      (FixedWidthOracleEncoding.encodeHValue functions input.1,
        TaggedOracle.zeroBits 160)
  | .inr input =>
      (TaggedOracle.zeroBits 256,
        FixedWidthOracleEncoding.encodeRValue functions input.1)

noncomputable def totalH (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (table : Table machine fuel initial) (input : Bytes) :
    FixedWidthOracleEncoding.FixedBytes 32 :=
  if bounded : input.length ≤ queryCap machine fuel initial then
    (FixedWidthOracleEncoding.encodingEquiv 32).symm
      ((TaggedOracle.observed table).1 ⟨input, bounded⟩)
  else ⟨List.replicate 32 0, by simp⟩

noncomputable def totalR (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (table : Table machine fuel initial) (input : Bytes) :
    FixedWidthOracleEncoding.FixedBytes 20 :=
  if bounded : input.length ≤ queryCap machine fuel initial then
    (FixedWidthOracleEncoding.encodingEquiv 20).symm
      ((TaggedOracle.observed table).2 ⟨input, bounded⟩)
  else ⟨List.replicate 20 0, by simp⟩

/-- Every finite table yields total width-correct source-model functions. -/
noncomputable def realize (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (table : Table machine fuel initial) :
    JointSourceChecks.Functions where
  H := fun input => (totalH machine fuel initial table input).1
  R := fun input => (totalR machine fuel initial table input).1
  H_width := fun input => (totalH machine fuel initial table input).2
  R_width := fun input => (totalR machine fuel initial table input).2

theorem realize_restrict_H (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (functions : JointSourceChecks.Functions)
    (input : Bytes) (bounded : input.length ≤ queryCap machine fuel initial) :
    (realize machine fuel initial (restrict machine fuel initial functions)).H
      input = functions.H input := by
  change (totalH machine fuel initial
    (restrict machine fuel initial functions) input).1 = functions.H input
  simp only [totalH, dif_pos bounded]
  have decoded := FixedWidthOracleEncoding.decode_encode
    (⟨functions.H input, functions.H_width input⟩ :
      FixedWidthOracleEncoding.FixedBytes 32)
  simpa [restrict, TaggedOracle.observed,
    FixedWidthOracleEncoding.encodeHValue,
    FixedWidthOracleEncoding.encodeH] using congrArg Subtype.val decoded

theorem realize_restrict_R (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (functions : JointSourceChecks.Functions)
    (input : Bytes) (bounded : input.length ≤ queryCap machine fuel initial) :
    (realize machine fuel initial (restrict machine fuel initial functions)).R
      input = functions.R input := by
  change (totalR machine fuel initial
    (restrict machine fuel initial functions) input).1 = functions.R input
  simp only [totalR, dif_pos bounded]
  have decoded := FixedWidthOracleEncoding.decode_encode
    (⟨functions.R input, functions.R_width input⟩ :
      FixedWidthOracleEncoding.FixedBytes 20)
  simpa [restrict, TaggedOracle.observed,
    FixedWidthOracleEncoding.encodeRValue,
    FixedWidthOracleEncoding.encodeR] using congrArg Subtype.val decoded

/-- Restriction and realization preserve the exact output and ordered log of
one fixed classical run, including failure and timeout. -/
theorem run_restrict_realize_eq (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (functions : JointSourceChecks.Functions) :
    run machine
      (realize machine fuel initial
        (restrict machine fuel initial functions)) fuel initial =
      run machine functions fuel initial := by
  apply CausalQueryAlgorithm.run_congr
  intro entry member
  cases query : entry.1 with
  | H input =>
      have bounded := queryCap_covers machine fuel initial functions
        entry member
      simpa [answer, query] using realize_restrict_H machine fuel initial
        functions input (by simpa [Query.input, query] using bounded)
  | R input =>
      have bounded := queryCap_covers machine fuel initial functions
        entry member
      simpa [answer, query] using realize_restrict_R machine fuel initial
        functions input (by simpa [Query.input, query] using bounded)

/-- A canonical realization gives zero values to unused product coordinates. -/
def canonicalTable (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (pair : Observed machine fuel initial) :
    Table machine fuel initial :=
  TaggedOracle.splitEquiv.symm
    (pair, (fun _ => TaggedOracle.zeroBits 160,
            fun _ => TaggedOracle.zeroBits 256))

theorem observed_canonicalTable (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (pair : Observed machine fuel initial) :
    TaggedOracle.observed (canonicalTable machine fuel initial pair) = pair := by
  change (TaggedOracle.splitEquiv
    (TaggedOracle.splitEquiv.symm
      (pair, (fun _ : Input machine fuel initial => TaggedOracle.zeroBits 160,
              fun _ : Input machine fuel initial => TaggedOracle.zeroBits 256)))).1 = pair
  simp

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

theorem realize_eq_of_observed_eq (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (left right : Table machine fuel initial)
    (same : TaggedOracle.observed left = TaggedOracle.observed right) :
    realize machine fuel initial left = realize machine fuel initial right := by
  apply functions_ext
  · funext input
    simp [realize, totalH, same]
  · funext input
    simp [realize, totalR, same]

theorem run_eq_canonical_observed (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (table : Table machine fuel initial) :
    run machine (realize machine fuel initial table) fuel initial =
      run machine
        (realize machine fuel initial
          (canonicalTable machine fuel initial
            (TaggedOracle.observed table))) fuel initial := by
  rw [realize_eq_of_observed_eq machine fuel initial table
    (canonicalTable machine fuel initial (TaggedOracle.observed table))]
  exact (observed_canonicalTable machine fuel initial _).symm

def selectedEquiv (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (P : Observed machine fuel initial → Prop) :
    {table : Table machine fuel initial //
      P (TaggedOracle.observed table)} ≃
      {pair : Observed machine fuel initial // P pair} ×
        Filler machine fuel initial where
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

theorem selected_count (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (P : Observed machine fuel initial → Prop) :
    Nat.card {table : Table machine fuel initial //
      P (TaggedOracle.observed table)} =
      Nat.card {pair : Observed machine fuel initial // P pair} *
        Nat.card (Filler machine fuel initial) := by
  rw [Nat.card_congr (selectedEquiv machine fuel initial P), Nat.card_prod]

theorem table_count (machine : Machine State Out)
    (fuel : Nat) (initial : State) :
    Nat.card (Table machine fuel initial) =
      Nat.card (Observed machine fuel initial) *
        Nat.card (Filler machine fuel initial) := by
  rw [Nat.card_congr (TaggedOracle.splitEquiv :
    Table machine fuel initial ≃
      Observed machine fuel initial × Filler machine fuel initial),
      Nat.card_prod]

/-- Every event on the exact output and ordered query-response log has the
same finite count up to the constant unused-coordinate filler factor. -/
theorem run_event_count (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (event : Option Out × List (Query × Bytes) → Prop) :
    Nat.card {table : Table machine fuel initial //
      event (run machine (realize machine fuel initial table)
        fuel initial)} =
      Nat.card {pair : Observed machine fuel initial //
        event (run machine
          (realize machine fuel initial
            (canonicalTable machine fuel initial pair))
          fuel initial)} * Nat.card (Filler machine fuel initial) := by
  let P : Observed machine fuel initial → Prop := fun pair =>
    event (run machine
      (realize machine fuel initial
        (canonicalTable machine fuel initial pair)) fuel initial)
  have agree (table : Table machine fuel initial) :
      event (run machine (realize machine fuel initial table)
        fuel initial) ↔ P (TaggedOracle.observed table) := by
    unfold P
    rw [run_eq_canonical_observed machine fuel initial table]
  let eventEquiv :
      {table : Table machine fuel initial //
        event (run machine (realize machine fuel initial table)
          fuel initial)} ≃
      {table : Table machine fuel initial //
        P (TaggedOracle.observed table)} :=
    { toFun := fun table => ⟨table.1, (agree table.1).mp table.2⟩
      invFun := fun table => ⟨table.1, (agree table.1).mpr table.2⟩
      left_inv := by intro table; apply Subtype.ext; rfl
      right_inv := by intro table; apply Subtype.ext; rfl }
  calc
    _ = Nat.card {table : Table machine fuel initial //
          P (TaggedOracle.observed table)} := Nat.card_congr eventEquiv
    _ = Nat.card {pair : Observed machine fuel initial // P pair} *
          Nat.card (Filler machine fuel initial) :=
            selected_count machine fuel initial P
    _ = _ := rfl

/-- Equality of the two finite uniform run-event densities in exact integer
cross products. No probability normalization is needed. -/
theorem run_event_density_cross_mul (machine : Machine State Out)
    (fuel : Nat) (initial : State)
    (event : Option Out × List (Query × Bytes) → Prop) :
    Nat.card {table : Table machine fuel initial //
      event (run machine (realize machine fuel initial table)
        fuel initial)} * Nat.card (Observed machine fuel initial) =
      Nat.card {pair : Observed machine fuel initial //
        event (run machine
          (realize machine fuel initial
            (canonicalTable machine fuel initial pair))
          fuel initial)} * Nat.card (Table machine fuel initial) := by
  rw [run_event_count machine fuel initial event,
    table_count machine fuel initial]
  ac_rfl

section PushOnly

variable {S : Type*}

/-- The fixed push-only transcript/ledger cache at `q + 1295` requests is a
direct instance of the generic finite sampling law. The first-stage machine
and initial state are fixed before the table is sampled. -/
theorem pushOnly_run_event_density_cross_mul
    (first : Machine S CausalPushOnlyLedgerExtractorSequence.FirstOutput)
    (q : Nat) (initial : S)
    (event : Option (CausalPushOnlyLedgerExtractorSequence.FirstOutput ×
      Option (Bytes × RoundWitness (Fin 150) Bytes Bytes)) ×
      List (Query × Bytes) → Prop) :
    Nat.card {table : Table
      (CausalPushOnlyLedgerExtractorSequence.machine first)
      (q + 1295) (.inl initial) //
      event (run (CausalPushOnlyLedgerExtractorSequence.machine first)
        (realize (CausalPushOnlyLedgerExtractorSequence.machine first)
          (q + 1295) (.inl initial) table)
        (q + 1295) (.inl initial))} *
      Nat.card (Observed (CausalPushOnlyLedgerExtractorSequence.machine first)
        (q + 1295) (.inl initial)) =
    Nat.card {pair : Observed
      (CausalPushOnlyLedgerExtractorSequence.machine first)
      (q + 1295) (.inl initial) //
      event (run (CausalPushOnlyLedgerExtractorSequence.machine first)
        (realize (CausalPushOnlyLedgerExtractorSequence.machine first)
          (q + 1295) (.inl initial)
          (canonicalTable
            (CausalPushOnlyLedgerExtractorSequence.machine first)
            (q + 1295) (.inl initial) pair))
        (q + 1295) (.inl initial))} *
      Nat.card (Table (CausalPushOnlyLedgerExtractorSequence.machine first)
        (q + 1295) (.inl initial)) :=
  run_event_density_cross_mul
    (CausalPushOnlyLedgerExtractorSequence.machine first)
    (q + 1295) (.inl initial) event

end PushOnly

end QSB.FiniteClassicalRunLaw
