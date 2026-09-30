import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
Transaction-level authorization and disclosure bookkeeping.

The projection omits scriptSig/witness malleations but includes ordered
outpoints, sequence numbers, outputs, and the authenticated previous outputs
used for fee calculation. `accepted` and `spendsTarget` are external predicates:
they are not silently equated with app API admission. Full consensus and chain
refinement are open. Auth is an owner-chosen set of exact projections, not a
service decision. This is a mathematical game skeleton, not a QROM algorithm.
-/
namespace QSB.Game

abbrev Bytes := List UInt8

structure Outpoint where
  txid : Bytes
  index : Nat
  deriving DecidableEq, Repr

structure Output where
  value : Nat
  script : Bytes
  deriving DecidableEq, Repr

structure Projection where
  version : Nat
  inputs : List Outpoint
  sequences : List Nat
  locktime : Nat
  outputs : List Output
  previousOutputs : List Output
  deriving DecidableEq, Repr

def FeeOf (p : Projection) : Int :=
  (p.previousOutputs.map (fun o => o.value)).sum -
    (p.outputs.map (fun o => o.value)).sum

def Unauthorized {SignedTx : Type*}
    (accepted spendsTarget : SignedTx → Prop)
    (projection : SignedTx → Projection)
    (authorized : Set Projection) (tx : SignedTx) : Prop :=
  accepted tx ∧ spendsTarget tx ∧ projection tx ∉ authorized

/-- Source-independent authorization check: a different ordered output list
is unauthorized if all owner-approved projections carry `want`. -/
theorem changed_outputs_unauthorized {SignedTx : Type*}
    {accepted spendsTarget : SignedTx → Prop}
    {projection : SignedTx → Projection}
    {authorized : Set Projection} {tx : SignedTx} {want : List Output}
    (ownerBound : ∀ p ∈ authorized, p.outputs = want)
    (acceptedTx : accepted tx) (spends : spendsTarget tx)
    (changed : (projection tx).outputs ≠ want) :
    Unauthorized accepted spendsTarget projection authorized tx := by
  refine ⟨acceptedTx, spends, ?_⟩
  intro h
  exact changed (ownerBound (projection tx) h)

/-- A concrete disclosure is recorded when it leaves the signer. `mined` is
metadata only; it never erases known indexed preimages. -/
structure Disclosure (Index Secret : Type*) where
  vault : Nat
  round : Fin 2
  opened : Finset Index
  values : (i : Index) → i ∈ opened → Secret
  mined : Bool

def disclosedAt {Index Secret : Type*} [DecidableEq Index]
    (history : List (Disclosure Index Secret)) (vault : Nat) (round : Fin 2) :
    Finset Index :=
  history.foldl (fun acc d =>
    if d.vault == vault && d.round == round then acc ∪ d.opened else acc) ∅

theorem disclosedAt_append
    {Index Secret : Type*} [DecidableEq Index]
    (history more : List (Disclosure Index Secret)) (vault : Nat) (round : Fin 2) :
    disclosedAt history vault round ⊆ disclosedAt (history ++ more) vault round := by
  unfold disclosedAt
  rw [List.foldl_append]
  generalize history.foldl
    (fun (acc : Finset Index) (d : Disclosure Index Secret) =>
      if d.vault == vault && d.round == round then acc ∪ d.opened else acc)
    (∅ : Finset Index) = old
  induction more generalizing old with
  | nil => simp
  | cons d rest ih =>
      simp only [List.foldl_cons]
      by_cases h : d.vault == vault && d.round == round
      · simp only [if_pos h]
        exact Finset.Subset.trans Finset.subset_union_left (ih (old ∪ d.opened))
      · simp only [if_neg h]
        exact ih old

/-- A conservative cap on disclosed positions after `r` signing records: if
each record opens at most `t` positions, the union has at most `t*r` positions.
The history may include records for other vaults/rounds, so this bound can be
loose. It counts releases whether or not they were mined. -/
theorem disclosedAt_card_le_history
    {Index Secret : Type*} [DecidableEq Index]
    (history : List (Disclosure Index Secret))
    (vault : Nat) (round : Fin 2) (t : Nat)
    (each : ∀ d ∈ history, d.opened.card ≤ t) :
    (disclosedAt history vault round).card ≤ t * history.length := by
  let step : Finset Index → Disclosure Index Secret → Finset Index :=
    fun acc d => if d.vault == vault && d.round == round then acc ∪ d.opened else acc
  have foldBound : ∀ (more : List (Disclosure Index Secret)) (acc : Finset Index),
      (∀ d ∈ more, d.opened.card ≤ t) →
      (more.foldl step acc).card ≤ acc.card + t * more.length := by
    intro more
    induction more with
    | nil =>
        intro acc _
        simp
    | cons d rest ih =>
        intro acc bounded
        have hd : d.opened.card ≤ t := bounded d (by simp)
        have hrest : ∀ x ∈ rest, x.opened.card ≤ t := by
          intro x hx
          exact bounded x (by simp [hx])
        simp only [List.foldl_cons, List.length_cons]
        by_cases h : d.vault == vault && d.round == round
        · have hu := Finset.card_union_le acc d.opened
          have hr := ih (acc ∪ d.opened) hrest
          simpa only [step, if_pos h] using
            (show (rest.foldl step (acc ∪ d.opened)).card ≤
              acc.card + t * (rest.length + 1) by
                rw [Nat.mul_add, Nat.mul_one]
                omega)
        · have hr := ih acc hrest
          simpa only [step, if_neg h] using
            (show (rest.foldl step acc).card ≤
              acc.card + t * (rest.length + 1) by
                rw [Nat.mul_add, Nat.mul_one]
                omega)
  have h := foldBound history ∅ each
  simpa [disclosedAt, step] using h

theorem disclosedAt_card_le_min
    {Index Secret : Type*} [Fintype Index] [DecidableEq Index]
    (history : List (Disclosure Index Secret))
    (vault : Nat) (round : Fin 2) (t : Nat)
    (each : ∀ d ∈ history, d.opened.card ≤ t) :
    (disclosedAt history vault round).card ≤
      min (Fintype.card Index) (t * history.length) := by
  apply Nat.le_min.mpr
  constructor
  · simpa using Finset.card_le_card
      (Finset.subset_univ (disclosedAt history vault round))
  · exact disclosedAt_card_le_history history vault round t each

end QSB.Game
