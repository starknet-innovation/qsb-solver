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

/-- `released` contains owner-approved assembled transactions whose QSB
unlocking material was exposed to an external signer, caller, or publication,
including unmined and helper-unsigned ones. It excludes adversary submissions.
Cancellation does not remove a prior release. -/
def AuthorizedRelease
    (projection : SignedTx → Game.Projection)
    (authorized : Set Game.Projection) (released : Set SignedTx) : Prop :=
  ∀ tx ∈ released, projection tx ∈ authorized

/-- The owner-disallowed message class is fixed independently of Bitcoin
acceptance and of the hash-puzzle checks. -/
def ForbiddenMessage
    (projection : SignedTx → Game.Projection)
    (authorized : Set Game.Projection) (tx : SignedTx) : Prop :=
  projection tx ∉ authorized

def FreshFailure
    (extractor : Extractor Index Secret Key SignedTx)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (forbidden : SignedTx → Prop)
    (disclosed : Finset Index) (tx : SignedTx) : Prop :=
  forbidden tx ∧ ∃ pinKey w,
    extractor tx = some (pinKey, w) ∧
    FreshOpening hashSecret commitments disclosed w.signed w.opening

def TwoPuzzleFailure
    (extractor : Extractor Index Secret Key SignedTx)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (forbidden : SignedTx → Prop)
    (released : Set SignedTx) (disclosed : Finset Index)
    (tx : SignedTx) : Prop :=
  ∃ pinKey w,
    extractor tx = some (pinKey, w) ∧
    NovelTwoPuzzle pinRelation roundRelation hashKey target forbidden
      released disclosed tx pinKey w

def DistinctKeyFailure
    (extractor : Extractor Index Secret Key SignedTx)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (forbidden : SignedTx → Prop)
    (released : Set SignedTx) (disclosed : Finset Index)
    (tx : SignedTx) : Prop :=
  ∃ pinKey w,
    extractor tx = some (pinKey, w) ∧
    DistinctKeyPuzzle pinRelation roundRelation hashKey target forbidden
      released disclosed tx pinKey w

def SameKeyFailure
    (extractor : Extractor Index Secret Key SignedTx)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (forbidden : SignedTx → Prop)
    (released : Set SignedTx) (disclosed : Finset Index)
    (tx : SignedTx) : Prop :=
  ∃ pinKey w,
    extractor tx = some (pinKey, w) ∧
    SameKeyPuzzle pinRelation roundRelation hashKey target forbidden
      released disclosed tx pinKey w

theorem two_puzzle_failure_key_cases
    {extractor : Extractor Index Secret Key SignedTx}
    {pinRelation : SignedTx → Key → Prop}
    {roundRelation : SignedTx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {forbidden : SignedTx → Prop}
    {released : Set SignedTx} {disclosed : Finset Index}
    {tx : SignedTx} :
    TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
      forbidden released disclosed tx ↔
      DistinctKeyFailure extractor pinRelation roundRelation hashKey target
        forbidden released disclosed tx ∨
      SameKeyFailure extractor pinRelation roundRelation hashKey target
        forbidden released disclosed tx := by
  constructor
  · rintro ⟨pinKey, w, extracted, puzzle⟩
    rcases novel_two_puzzle_key_cases puzzle with distinct | same
    · exact Or.inl ⟨pinKey, w, extracted, distinct⟩
    · exact Or.inr ⟨pinKey, w, extracted, same⟩
  · rintro (⟨pinKey, w, extracted, distinct⟩ |
      ⟨pinKey, w, extracted, same⟩)
    · exact ⟨pinKey, w, extracted, distinct.1⟩
    · exact ⟨pinKey, w, extracted, same.1⟩

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

/-- A vacuous extractor does not make the security bound succeed: its gap event
is exactly the bad-spend event. This checks a useful boundary of the reduction. -/
theorem gap_with_no_extractor
    (accepted spendsTarget : SignedTx → Prop)
    (projection : SignedTx → Game.Projection)
    (authorized : Set Game.Projection)
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (pinRelation : SignedTx → Key → Prop)
    (roundRelation : SignedTx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (tx : SignedTx) :
    ExtractionGap accepted spendsTarget projection authorized
      (fun _ : SignedTx => (none : Option (Key × RoundWitness Index Secret Key)))
      hashSecret commitments pinRelation roundRelation hashKey target tx ↔
    Game.Unauthorized accepted spendsTarget projection authorized tx := by
  simp [ExtractionGap, ExtractionEvidence]

/-- An unauthorized output cannot be an honestly released transaction, provided
released semantic projections are owner-authorized. -/
theorem unauthorized_not_released
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Game.Projection}
    {authorized : Set Game.Projection} {released : Set SignedTx}
    {tx : SignedTx}
    (honest : AuthorizedRelease projection authorized released)
    (bad : Game.Unauthorized accepted spendsTarget projection authorized tx) :
    tx ∉ released := by
  intro h
  exact bad.2.2 (honest tx h)

/-- This theorem has an explicit, currently unproved Script extraction premise. -/
theorem unauthorized_under_source_extraction
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Game.Projection}
    {authorized : Set Game.Projection} {released : Set SignedTx}
    {extractor : Extractor Index Secret Key SignedTx}
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {pinRelation : SignedTx → Key → Prop}
    {roundRelation : SignedTx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {disclosed : Finset Index} {tx : SignedTx}
    (honest : AuthorizedRelease projection authorized released)
    (extract : SourceExtraction accepted spendsTarget extractor hashSecret
      commitments pinRelation roundRelation hashKey target)
    (bad : Game.Unauthorized accepted spendsTarget projection authorized tx) :
    FreshFailure extractor hashSecret commitments
      (ForbiddenMessage projection authorized) disclosed tx ∨
      TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
        (ForbiddenMessage projection authorized) released disclosed tx := by
  obtain ⟨pinKey, w, fromOutput, shape, pin, finalRound⟩ := extract tx bad.1 bad.2.1
  rcases extracted_pin_final_fresh_or_two_puzzles
      (forbidden := ForbiddenMessage projection authorized)
      bad.2.2 (unauthorized_not_released honest bad)
      shape pin finalRound with fresh | puzzle
  · exact Or.inl ⟨bad.2.2, pinKey, w, fromOutput, fresh⟩
  · exact Or.inr ⟨pinKey, w, fromOutput, puzzle⟩

/-- No unproved source premise: a real extraction failure remains a visible
third outcome. There is no bound on its probability in this project. -/
theorem unauthorized_with_explicit_gap
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Game.Projection}
    {authorized : Set Game.Projection} {released : Set SignedTx}
    {extractor : Extractor Index Secret Key SignedTx}
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {pinRelation : SignedTx → Key → Prop}
    {roundRelation : SignedTx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {disclosed : Finset Index} {tx : SignedTx}
    (honest : AuthorizedRelease projection authorized released)
    (bad : Game.Unauthorized accepted spendsTarget projection authorized tx) :
    FreshFailure extractor hashSecret commitments
      (ForbiddenMessage projection authorized) disclosed tx ∨
      TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
        (ForbiddenMessage projection authorized) released disclosed tx ∨
      ExtractionGap accepted spendsTarget projection authorized extractor
        hashSecret commitments pinRelation roundRelation hashKey target tx := by
  classical
  by_cases h : ExtractionEvidence extractor hashSecret commitments
      pinRelation roundRelation hashKey target tx
  · obtain ⟨pinKey, w, fromOutput, shape, pin, finalRound⟩ := h
    rcases extracted_pin_final_fresh_or_two_puzzles
        (forbidden := ForbiddenMessage projection authorized)
        bad.2.2 (unauthorized_not_released honest bad)
        shape pin finalRound with fresh | puzzle
    · exact Or.inl ⟨bad.2.2, pinKey, w, fromOutput, fresh⟩
    · exact Or.inr (Or.inl ⟨pinKey, w, fromOutput, puzzle⟩)
  · exact Or.inr (Or.inr ⟨bad, h⟩)

/-- The measured security-game consequence, with every missing quantitative
obligation in its type. `εgap` has no established small value; setting it to
zero requires a source-extraction theorem, not an appeal to this union bound.
The terminal distribution may include adaptive transcript and disclosure
history through `released` and `disclosed`. -/
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
    (output : Ω → SignedTx) (released : Ω → Set SignedTx)
    (disclosed : Ω → Finset Index)
    (honest : ∀ ω, AuthorizedRelease projection authorized (released ω))
    (εfresh εpuzzle εgap : ENNReal)
    (freshBound : μ {ω | FreshFailure extractor hashSecret commitments
      (ForbiddenMessage projection authorized)
      (disclosed ω) (output ω)} ≤ εfresh)
    (puzzleBound : μ {ω | TwoPuzzleFailure extractor pinRelation roundRelation
      hashKey target (ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)} ≤ εpuzzle)
    (gapBound : μ {ω | ExtractionGap accepted spendsTarget projection authorized
      extractor hashSecret commitments pinRelation roundRelation hashKey target
      (output ω)} ≤ εgap) :
    μ {ω | Game.Unauthorized accepted spendsTarget projection authorized (output ω)} ≤
      (εfresh + εpuzzle) + εgap := by
  let badEvent : Set Ω :=
    {ω | Game.Unauthorized accepted spendsTarget projection authorized (output ω)}
  let freshEvent : Set Ω :=
    {ω | FreshFailure extractor hashSecret commitments
      (ForbiddenMessage projection authorized) (disclosed ω) (output ω)}
  let puzzleEvent : Set Ω :=
    {ω | TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
      (ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)}
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
      (released := released ω) (honest ω) bad)
  exact event_bound_with_gap μ badEvent freshEvent puzzleEvent gapEvent
    inclusion εfresh εpuzzle εgap freshBound puzzleBound gapBound

/-- The same conditional security-game bound with the two-puzzle target
separated by whether the extracted pinning and final-round key bytes coincide.
The distinct branch is the only possible target for a distinct-input QROM
search theorem; neither branch has a proved QSB query bound here. -/
theorem unauthorized_measure_bound_with_key_cases
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
    (output : Ω → SignedTx) (released : Ω → Set SignedTx)
    (disclosed : Ω → Finset Index)
    (honest : ∀ ω, AuthorizedRelease projection authorized (released ω))
    (εfresh εdistinct εsame εgap : ENNReal)
    (freshBound : μ {ω | FreshFailure extractor hashSecret commitments
      (ForbiddenMessage projection authorized)
      (disclosed ω) (output ω)} ≤ εfresh)
    (distinctBound : μ {ω | DistinctKeyFailure extractor pinRelation
      roundRelation hashKey target (ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)} ≤ εdistinct)
    (sameBound : μ {ω | SameKeyFailure extractor pinRelation
      roundRelation hashKey target (ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)} ≤ εsame)
    (gapBound : μ {ω | ExtractionGap accepted spendsTarget projection authorized
      extractor hashSecret commitments pinRelation roundRelation hashKey target
      (output ω)} ≤ εgap) :
    μ {ω | Game.Unauthorized accepted spendsTarget projection authorized
      (output ω)} ≤
      (εfresh + (εdistinct + εsame)) + εgap := by
  let distinctEvent : Set Ω :=
    {ω | DistinctKeyFailure extractor pinRelation roundRelation hashKey target
      (ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)}
  let sameEvent : Set Ω :=
    {ω | SameKeyFailure extractor pinRelation roundRelation hashKey target
      (ForbiddenMessage projection authorized)
      (released ω) (disclosed ω) (output ω)}
  have cover :
      {ω | TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
        (ForbiddenMessage projection authorized)
        (released ω) (disclosed ω) (output ω)} ⊆
        distinctEvent ∪ sameEvent := by
    intro ω puzzle
    simpa [distinctEvent, sameEvent] using
      (two_puzzle_failure_key_cases.mp puzzle)
  have puzzleBound :
      μ {ω | TwoPuzzleFailure extractor pinRelation roundRelation hashKey target
        (ForbiddenMessage projection authorized)
        (released ω) (disclosed ω) (output ω)} ≤
        εdistinct + εsame := by
    exact (MeasureTheory.measure_mono cover).trans
      ((MeasureTheory.measure_union_le distinctEvent sameEvent).trans
        (add_le_add distinctBound sameBound))
  exact unauthorized_measure_bound_with_gap μ output released disclosed
    honest εfresh (εdistinct + εsame) εgap freshBound puzzleBound gapBound

end QSB
