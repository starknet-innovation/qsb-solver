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
  opening : (i : Index) → i ∈ signed → Secret
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

/-- Search on an owner-forbidden message relative to prior QSB releases.
Restricting to forbidden messages prevents ordinary authorized releases from
making the target event certain. This is still NOT standard HORS hash-to-subset. -/
def NovelCoveredPuzzle
    (nonceRelation : Tx → Finset Index → Key → Prop)
    (hashKey : Key → Digest) (target : Set Digest)
    (forbidden : Tx → Prop) (released : Set Tx) (disclosed : Finset Index)
    (tx : Tx) (w : RoundWitness Index Secret Key) : Prop :=
  forbidden tx ∧ tx ∉ released ∧
    CoveredPuzzle nonceRelation hashKey target disclosed tx w

theorem extracted_novel_round_fresh_or_puzzle
    {hashSecret : Secret → Digest} {commitments : Index → Digest}
    {nonceRelation : Tx → Finset Index → Key → Prop}
    {hashKey : Key → Digest} {target : Set Digest}
    {forbidden : Tx → Prop} {released : Set Tx} {disclosed : Finset Index}
    {tx : Tx} {w : RoundWitness Index Secret Key}
    (badMessage : forbidden tx) (novel : tx ∉ released)
    (extracted : ExtractedRound hashSecret commitments nonceRelation hashKey target tx w) :
    FreshOpening hashSecret commitments disclosed w.signed w.opening ∨
      NovelCoveredPuzzle nonceRelation hashKey target forbidden
        released disclosed tx w := by
  rcases extracted_round_fresh_or_puzzle extracted with fresh | covered
  · exact Or.inl fresh
  · exact Or.inr ⟨badMessage, novel, covered⟩

end QSB
