import QSB.Attack
import QSB.Game
import QSB.Probability

/-!
The transaction-game reduction interface. `SourceExtraction` is the UNPROVED
arbitrary-witness Script-to-model obligation. The extractor is a function of
the adversary's output, so the target events do not existentially select a
secret witness from the challenger's private state. Its efficient computation
from raw transaction bytes is also part of the source-refinement obligation.

`ExtractionGap` is a real alternative outcome, not a negligible error term.
It cannot be dropped or bounded until source refinement is established.
-/
namespace QSB

variable {Index Secret Digest Key SignedTx : Type*} [DecidableEq Index]

abbrev Extractor (Index Secret Key SignedTx : Type*) :=
  SignedTx → Option (Key × RoundWitness Index Secret Key)

def ExtractionEvidence
    (extractor : Extractor Index Secret Key SignedTx)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (tx : SignedTx) : Prop :=
  ∃ pinKey w,
    extractor tx = some (pinKey, w) ∧
    FinalRoundShape w ∧
    ExtractedPin pinRelation hashKey target tx pinKey ∧
    ExtractedRound hashSecret commitments roundRelation hashKey target tx w

def SourceExtraction
    (accepted spendsTarget : SignedTx → Prop)
    (extractor : Extractor Index Secret Key SignedTx)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest) : Prop :=
  ∀ tx, accepted tx → spendsTarget tx →
    ExtractionEvidence extractor hashSecret commitments
      pinRelation roundRelation hashKey target tx

def AuthorizedPublication
    (projection : SignedTx → Game.Projection)
    (authorized : Set Game.Projection) (published : Set SignedTx) : Prop :=
  ∀ tx ∈ published, projection tx ∈ authorized

def FreshFailure
    (extractor : Extractor Index Secret Key SignedTx)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (disclosed : Finset Index) (tx : SignedTx) : Prop :=
  ∃ pinKey w,
    extractor tx = some (pinKey, w) ∧
    FreshOpening hashSecret commitments disclosed w.signed w.opening

def TwoPuzzleFailure
    (extractor : Extractor Index Secret Key SignedTx)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (published : Set SignedTx) (disclosed : Finset Index)
    (tx : SignedTx) : Prop :=
  ∃ pinKey w,
    extractor tx = some (pinKey, w) ∧
    NovelTwoPuzzle pinRelation roundRelation hashKey target
      published disclosed tx pinKey w

def ExtractionGap
    (accepted spendsTarget : SignedTx → Prop)
    (projection : SignedTx → Game.Projection)
    (authorized : Set Game.Projection)
    (extractor : Extractor Index Secret Key SignedTx)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (tx : SignedTx) : Prop :=
  Game.Unauthorized accepted spendsTarget projection authorized tx ∧
    ¬ ExtractionEvidence extractor hashSecret commitments
      pinRelation roundRelation hashKey target tx

/-- An unauthorized output cannot be an honestly published transaction, provided
published semantic projections are owner-authorized. -/
theorem unauthorized_not_published
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Game.Projection}
    {authorized : Set Game.Projection} {published : Set SignedTx}
    {tx : SignedTx}
    (honest : AuthorizedPublication projection authorized published)
    (bad : Game.Unauthorized accepted spendsTarget projection authorized tx) :
    tx ∉ published := by
  intro h
  exact bad.2.2 (honest tx h)

/-- This theorem has an explicit, currently unproved Script extraction premise. -/
theorem unauthorized_under_source_extraction
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Game.Projection}
    {authorized : Set Game.Projection} {published : Set SignedTx}
    {extractor : Extractor Index Secret Key SignedTx}
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {pinRelation : SignedTx → Key → Prop}
    {roundRelation : SignedTx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {disclosed : Finset Index} {tx : SignedTx}
    (honest : AuthorizedPublication projection authorized published)
    (extract : SourceExtraction accepted spendsTarget extractor hashSecret
      commitments pinRelation roundRelation hashKey target)
    (bad : Game.Unauthorized accepted spendsTarget projection authorized tx) :
    FreshFailure extractor hashSecret commitments disclosed tx ∨
      TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
        published disclosed tx := by
  obtain ⟨pinKey, w, fromOutput, shape, pin, finalRound⟩ := extract tx bad.1 bad.2.1
  rcases extracted_pin_final_fresh_or_two_puzzles
      (unauthorized_not_published honest bad) shape pin finalRound with fresh | puzzle
  · exact Or.inl ⟨pinKey, w, fromOutput, fresh⟩
  · exact Or.inr ⟨pinKey, w, fromOutput, puzzle⟩

/-- No unproved source premise: a real extraction failure remains a visible
third outcome. There is no bound on its probability in this project. -/
theorem unauthorized_with_explicit_gap
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Game.Projection}
    {authorized : Set Game.Projection} {published : Set SignedTx}
    {extractor : Extractor Index Secret Key SignedTx}
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {pinRelation : SignedTx → Key → Prop}
    {roundRelation : SignedTx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {disclosed : Finset Index} {tx : SignedTx}
    (honest : AuthorizedPublication projection authorized published)
    (bad : Game.Unauthorized accepted spendsTarget projection authorized tx) :
    FreshFailure extractor hashSecret commitments disclosed tx ∨
      TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
        published disclosed tx ∨
      ExtractionGap accepted spendsTarget projection authorized extractor
        hashSecret commitments pinRelation roundRelation hashKey target tx := by
  classical
  by_cases h : ExtractionEvidence extractor hashSecret commitments
      pinRelation roundRelation hashKey target tx
  · obtain ⟨pinKey, w, fromOutput, shape, pin, finalRound⟩ := h
    rcases extracted_pin_final_fresh_or_two_puzzles
        (unauthorized_not_published honest bad) shape pin finalRound with fresh | puzzle
    · exact Or.inl ⟨pinKey, w, fromOutput, fresh⟩
    · exact Or.inr (Or.inl ⟨pinKey, w, fromOutput, puzzle⟩)
  · exact Or.inr (Or.inr ⟨bad, h⟩)

/-- The measured security-game consequence, with every missing quantitative
obligation in its type. `εgap` has no established small value; setting it to
zero requires a source-extraction theorem, not an appeal to this union bound.
The terminal distribution may include adaptive transcript and disclosure
history through `published` and `disclosed`. -/
theorem unauthorized_measure_bound_with_gap
    {Ω : Type*} [MeasurableSpace Ω]
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Game.Projection}
    {authorized : Set Game.Projection}
    {extractor : Extractor Index Secret Key SignedTx}
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {pinRelation : SignedTx → Key → Prop}
    {roundRelation : SignedTx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    (μ : MeasureTheory.Measure Ω)
    (output : Ω → SignedTx) (published : Ω → Set SignedTx)
    (disclosed : Ω → Finset Index)
    (honest : ∀ ω, AuthorizedPublication projection authorized (published ω))
    (εfresh εpuzzle εgap : ENNReal)
    (freshBound : μ {ω | FreshFailure extractor hashSecret commitments
      (disclosed ω) (output ω)} ≤ εfresh)
    (puzzleBound : μ {ω | TwoPuzzleFailure extractor pinRelation roundRelation
      hashKey target (published ω) (disclosed ω) (output ω)} ≤ εpuzzle)
    (gapBound : μ {ω | ExtractionGap accepted spendsTarget projection authorized
      extractor hashSecret commitments pinRelation roundRelation hashKey target
      (output ω)} ≤ εgap) :
    μ {ω | Game.Unauthorized accepted spendsTarget projection authorized (output ω)} ≤
      (εfresh + εpuzzle) + εgap := by
  let badEvent : Set Ω :=
    {ω | Game.Unauthorized accepted spendsTarget projection authorized (output ω)}
  let freshEvent : Set Ω :=
    {ω | FreshFailure extractor hashSecret commitments (disclosed ω) (output ω)}
  let puzzleEvent : Set Ω :=
    {ω | TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
      (published ω) (disclosed ω) (output ω)}
  let gapEvent : Set Ω :=
    {ω | ExtractionGap accepted spendsTarget projection authorized extractor
      hashSecret commitments pinRelation roundRelation hashKey target (output ω)}
  have inclusion : badEvent ⊆ (freshEvent ∪ puzzleEvent) ∪ gapEvent := by
    intro ω bad
    simpa [freshEvent, puzzleEvent, gapEvent, or_assoc] using
      (unauthorized_with_explicit_gap
      (extractor := extractor) (hashSecret := hashSecret)
      (commitments := commitments) (pinRelation := pinRelation)
      (roundRelation := roundRelation) (hashKey := hashKey)
      (target := target) (disclosed := disclosed ω)
      (published := published ω) (honest ω) bad)
  exact event_bound_with_gap μ badEvent freshEvent puzzleEvent gapEvent
    inclusion εfresh εpuzzle εgap freshBound puzzleBound gapBound

end QSB
