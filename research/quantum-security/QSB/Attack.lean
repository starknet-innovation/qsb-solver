import QSB.Extraction
import QSB.Selection

/-!
A deliberately *weaker* problem suited to the observed Config A control flow:
pinning and the FINAL digest round. The first-round multisignature result is
not a premise, because the emitted script leaves it unchecked. Its earlier
HASH160 comparisons and puzzle CHECKSIGVERIFY still need analysis, but after a
valid public disclosure their previously accepted values may be reused.

The statements here do not assert that arbitrary Bitcoin acceptance implies
`ExtractedPin`/`ExtractedRound`; that source-refinement theorem is open.
-/
namespace QSB

variable {Index Secret Digest Key Tx : Type*} [DecidableEq Index]

structure ExtractedPin
    (pinRelation : Tx → Key → Prop) (hashKey : Key → Digest)
    (target : Set Digest) (tx : Tx) (key : Key) : Prop where
  nonceBound : pinRelation tx key
  puzzle : hashKey key ∈ target

/-- Required shape of Config A's final round. This is not yet proved for an
arbitrary accepted Script witness; it is an explicit source-refinement goal. -/
def FinalRoundShape {Index Secret Key : Type*} [DecidableEq Index]
    (w : RoundWitness Index Secret Key) : Prop :=
  w.signed.card = 7 ∧ w.bonus.card = 2 ∧ Disjoint w.signed w.bonus

theorem final_round_shape_total
    {Index Secret Key : Type*} [DecidableEq Index]
    {w : RoundWitness Index Secret Key}
    (shape : FinalRoundShape w) : (w.signed ∪ w.bonus).card = 9 := by
  obtain ⟨h7, h2, disjoint⟩ := shape
  rw [Finset.card_union_of_disjoint disjoint, h7, h2]

/-- The shape supplied by the abstract without-replacement traversal. A real
Bitcoin witness still needs to be shown to induce that traversal. -/
def roundWitnessFromChosen {Index Secret Key : Type*} [DecidableEq Index]
    (chosen : List Index)
    (opening : (i : Index) → i ∈ (chosen.take 7).toFinset → Secret)
    (key : Key) :
    RoundWitness Index Secret Key :=
  { signed := (chosen.take 7).toFinset,
    bonus := (chosen.drop 7).toFinset,
    opening := opening, key := key }

theorem abstract_run_final_shape
    {Index Secret Key : Type*} [DecidableEq Index]
    {indices : List Nat} {pool chosen remaining : List Index}
    (distinct : pool.Nodup) (nine : indices.length = 9)
    (run : chooseMany indices pool = some (chosen, remaining))
    (opening : (i : Index) → i ∈ (chosen.take 7).toFinset → Secret)
    (key : Key) :
    FinalRoundShape (roundWitnessFromChosen chosen opening key) := by
  simpa [FinalRoundShape, roundWitnessFromChosen] using
    nine_selected_partition distinct nine run

/-- A computational target independent of Bitcoin acceptance. `forbidden`
specifies owner-disallowed messages before any Script or hash evaluation. The
adversary outputs such a novel transaction, a pin key, a covered final-round
subset/bonus choice and a final-round key satisfying two public hash-to-DER
puzzles. No success bound for this target has been proved. -/
def NovelTwoPuzzle
    (pinRelation : Tx → Key → Prop)
    (roundRelation : Tx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (forbidden : Tx → Prop) (released : Set Tx) (disclosed : Finset Index)
    (tx : Tx) (pinKey : Key) (w : RoundWitness Index Secret Key) : Prop :=
  forbidden tx ∧ tx ∉ released ∧ FinalRoundShape w ∧
  pinRelation tx pinKey ∧ hashKey pinKey ∈ target ∧
  w.signed ⊆ disclosed ∧
  roundRelation tx (w.signed ∪ w.bonus) w.key ∧ hashKey w.key ∈ target

/-- A direct two-distinct-input QROM search lemma can at most address this
branch. The equality branch remains a separate, potentially easier target. -/
def DistinctKeyPuzzle
    (pinRelation : Tx → Key → Prop)
    (roundRelation : Tx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (forbidden : Tx → Prop) (released : Set Tx) (disclosed : Finset Index)
    (tx : Tx) (pinKey : Key) (w : RoundWitness Index Secret Key) : Prop :=
  NovelTwoPuzzle pinRelation roundRelation hashKey target forbidden
    released disclosed tx pinKey w ∧ pinKey ≠ w.key

def SameKeyPuzzle
    (pinRelation : Tx → Key → Prop)
    (roundRelation : Tx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (forbidden : Tx → Prop) (released : Set Tx) (disclosed : Finset Index)
    (tx : Tx) (pinKey : Key) (w : RoundWitness Index Secret Key) : Prop :=
  NovelTwoPuzzle pinRelation roundRelation hashKey target forbidden
    released disclosed tx pinKey w ∧ pinKey = w.key

theorem novel_two_puzzle_key_cases
    {pinRelation : Tx → Key → Prop}
    {roundRelation : Tx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {forbidden : Tx → Prop} {released : Set Tx} {disclosed : Finset Index}
    {tx : Tx} {pinKey : Key} {w : RoundWitness Index Secret Key}
    (puzzle : NovelTwoPuzzle pinRelation roundRelation hashKey target forbidden
      released disclosed tx pinKey w) :
    DistinctKeyPuzzle pinRelation roundRelation hashKey target forbidden
      released disclosed tx pinKey w ∨
    SameKeyPuzzle pinRelation roundRelation hashKey target forbidden
      released disclosed tx pinKey w := by
  classical
  by_cases h : pinKey = w.key
  · exact Or.inr ⟨puzzle, h⟩
  · exact Or.inl ⟨puzzle, h⟩

theorem extracted_pin_final_fresh_or_two_puzzles
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {pinRelation : Tx → Key → Prop}
    {roundRelation : Tx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {forbidden : Tx → Prop} {released : Set Tx} {disclosed : Finset Index}
    {tx : Tx} {pinKey : Key} {w : RoundWitness Index Secret Key}
    (badMessage : forbidden tx) (novel : tx ∉ released)
    (shape : FinalRoundShape w)
    (pin : ExtractedPin pinRelation hashKey target tx pinKey)
    (finalRound : ExtractedRound hashSecret commitments roundRelation hashKey target tx w) :
    FreshOpening hashSecret commitments disclosed w.signed w.opening ∨
      NovelTwoPuzzle pinRelation roundRelation hashKey target forbidden
        released disclosed tx pinKey w := by
  rcases openings_fresh_or_covered finalRound.openings with fresh | covered
  · exact Or.inl fresh
  · exact Or.inr ⟨badMessage, novel, shape, pin.nonceBound, pin.puzzle, covered,
      finalRound.nonceBound, finalRound.puzzle⟩

end QSB
