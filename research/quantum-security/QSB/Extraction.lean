import QSB.Disclosure

/-!
Algebraic extraction interface for ONE enforced digest round.
This interface is NOT a definition of Bitcoin acceptance. In particular, the
production first-round CHECKMULTISIG has not been shown to imply `nonceBound`.
No theorem in this module claims that arbitrary Script witnesses satisfy it.
-/
namespace QSB

structure RoundWitness (Index Secret Key : Type*) where
  signed : Finset Index
  bonus : Finset Index
  opening : Index → Secret
  key : Key

variable {Index Secret Digest Key Tx : Type*} [DecidableEq Index]

structure ExtractedRound
    (hashSecret : Secret → Digest) (commitments : Index → Digest)
    (nonceRelation : Tx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (tx : Tx) (w : RoundWitness Index Secret Key) : Prop where
  openings : OpeningsValid hashSecret commitments w.signed w.opening
  nonceBound : nonceRelation tx (w.signed ∪ w.bonus) w.key
  puzzle : hashKey w.key ∈ target

/-- Independently specified search output: a transaction, covered signed subset,
bonus subset, and nonce-relation key whose hash lies in the target set.
This deliberately has no owner-authorization or Bitcoin-acceptance predicate.
Its quantum query complexity is NOT assumed or proved in this project. -/
def CoveredPuzzle
    (nonceRelation : Tx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (disclosed : Finset Index) (tx : Tx) (w : RoundWitness Index Secret Key) : Prop :=
  w.signed ⊆ disclosed ∧
  nonceRelation tx (w.signed ∪ w.bonus) w.key ∧ hashKey w.key ∈ target

theorem extracted_round_fresh_or_puzzle
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {nonceRelation : Tx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {disclosed : Finset Index} {tx : Tx} {w : RoundWitness Index Secret Key}
    (extracted : ExtractedRound hashSecret commitments nonceRelation hashKey target tx w) :
    FreshOpening hashSecret commitments disclosed w.signed w.opening ∨
      CoveredPuzzle nonceRelation hashKey target disclosed tx w := by
  rcases openings_fresh_or_covered extracted.openings with fresh | covered
  · exact Or.inl fresh
  · exact Or.inr ⟨covered, extracted.nonceBound, extracted.puzzle⟩

/-- Fresh-message target search relative to published transcript messages.
Excluding old messages is essential: a published solution can otherwise be
replayed with probability one. This is still NOT standard HORS hash-to-subset. -/
def NovelCoveredPuzzle
    (nonceRelation : Tx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (published : Set Tx) (disclosed : Finset Index)
    (tx : Tx) (w : RoundWitness Index Secret Key) : Prop :=
  tx ∉ published ∧ CoveredPuzzle nonceRelation hashKey target disclosed tx w

theorem extracted_novel_round_fresh_or_puzzle
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {nonceRelation : Tx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {published : Set Tx} {disclosed : Finset Index}
    {tx : Tx} {w : RoundWitness Index Secret Key}
    (novel : tx ∉ published)
    (extracted : ExtractedRound hashSecret commitments nonceRelation hashKey target tx w) :
    FreshOpening hashSecret commitments disclosed w.signed w.opening ∨
      NovelCoveredPuzzle nonceRelation hashKey target published disclosed tx w := by
  rcases extracted_round_fresh_or_puzzle extracted with fresh | covered
  · exact Or.inl fresh
  · exact Or.inr ⟨novel, covered⟩

end QSB
