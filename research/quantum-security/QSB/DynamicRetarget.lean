import QSB.DynamicDisclosureEvent

/-!
An approved disclosure of one fixed-signature/key verification makes a
particular SHA256d digest an oracle-dependent member of that key's ECDSA
target set. An unauthorized verification with the same signature and key
must then either collide with that approved digest on a distinct ALL
preimage, or hit one of the other at most seven wire digest targets. This
does not bound the coherent-query probability of either event.
-/
namespace QSB.DynamicRetarget
open ByteMachine

structure ReleasedAllCall
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection) where
  sig : Bytes
  key : Bytes
  tx : SighashAllWire.TxFields
  selected : Nat
  scriptCode : Bytes
  valid : SighashAllWire.valid tx
  scriptCodeValid : scriptCode.length < 256 ^ 8
  approved : SighashAllWire.projectionWithLedger ledger tx ∈ authorized
  checked : ecdsa sig key
    (functions.H (functions.H
      (SighashAllWire.sourceAllPreimage tx selected scriptCode))) = true

/-- Search only the records for this exact signature byte string and public
key encoding. A key disclosed for another role does not silently count as a
matching approved verification for this signature. -/
def findRelease
    {functions : JointSourceChecks.Functions}
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    {ledger : Game.Outpoint → Game.Output}
    {authorized : Set Game.Projection} :
    List (ReleasedAllCall functions ecdsa ledger authorized) →
      Bytes → Bytes →
      Option (ReleasedAllCall functions ecdsa ledger authorized)
  | [], _, _ => none
  | release :: rest, sig, key =>
      if release.sig = sig ∧ release.key = key then some release
      else findRelease rest sig key

theorem findRelease_sound
    {functions : JointSourceChecks.Functions}
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    {ledger : Game.Outpoint → Game.Output}
    {authorized : Set Game.Projection}
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (sig key : Bytes)
    (release : ReleasedAllCall functions ecdsa ledger authorized)
    (found : findRelease history sig key = some release) :
    release.sig = sig ∧ release.key = key := by
  induction history with
  | nil => simp [findRelease] at found
  | cons head rest ih =>
      by_cases matchPair : head.sig = sig ∧ head.key = key
      · simp [findRelease, matchPair] at found
        subst release
        exact matchPair
      · simp [findRelease, matchPair] at found
        exact ih found

/-- A collision of `H ∘ H` on distinct inputs yields a collision of that
same H, either on the original inputs or on their distinct first outputs. -/
theorem double_hash_collision_yields_hash_collision
    (H : Bytes → Bytes) (left right : Bytes)
    (different : left ≠ right)
    (doubleEqual : H (H left) = H (H right)) :
    ∃ a b : Bytes, a ≠ b ∧ H a = H b := by
  by_cases firstEqual : H left = H right
  · exact ⟨left, right, different, firstEqual⟩
  · exact ⟨H left, H right, firstEqual, doubleEqual⟩

/-- Reusing a publicly disclosed fixed-signature/key pair on an unauthorized
projection yields either an equal SHA256d digest on distinct ALL preimages or
an alternative digest in a target set of size at most seven. The target-set
soundness/cardinality contract and source-shaped ALL encoding are explicit. -/
theorem reused_fixed_call_collision_or_alternative
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (released : ReleasedAllCall functions ecdsa ledger authorized)
    (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes)
    (attemptedValid : SighashAllWire.valid attempted)
    (scriptCodeValid : scriptCode.length < 256 ^ 8)
    (forbidden : SighashAllWire.projectionWithLedger ledger attempted ∉
      authorized)
    (checked : ecdsa released.sig released.key
      (functions.H (functions.H
        (SighashAllWire.sourceAllPreimage attempted selected
          scriptCode))) = true) :
    let oldPreimage := SighashAllWire.sourceAllPreimage
      released.tx released.selected released.scriptCode
    let newPreimage := SighashAllWire.sourceAllPreimage
      attempted selected scriptCode
    let oldDigest := functions.H (functions.H oldPreimage)
    let newDigest := functions.H (functions.H newPreimage)
    newPreimage ≠ oldPreimage ∧
      (newDigest = oldDigest ∨
        (newDigest ∈
          (contract.targets released.sig released.key).erase oldDigest ∧
        ((contract.targets released.sig released.key).erase
          oldDigest).card ≤ 7)) := by
  dsimp
  have preimagesDistinct :=
    SighashAllWire.unauthorized_sourceAll_distinct_preimage
      ledger authorized released.selected selected
      released.scriptCode scriptCode released.valid attemptedValid
      released.scriptCodeValid scriptCodeValid
      released.approved forbidden
  have oldTarget := contract.sound released.sig released.key _
    released.checked
  have newTarget := contract.sound released.sig released.key _ checked
  constructor
  · exact preimagesDistinct
  · by_cases sameDigest :
        functions.H (functions.H
          (SighashAllWire.sourceAllPreimage attempted selected scriptCode)) =
        functions.H (functions.H
          (SighashAllWire.sourceAllPreimage released.tx released.selected
            released.scriptCode))
    · exact Or.inl sameDigest
    · right
      constructor
      · exact Finset.mem_erase.mpr ⟨sameDigest, newTarget⟩
      · have erased := Finset.card_erase_of_mem oldTarget
        have bound := contract.card_le_eight released.sig released.key
        omega

/-- The equal-digest branch above is an ordinary collision in the *same*
SHA-256 oracle. The other branch remains a finite, oracle-dependent target
search problem. No independent-oracle replacement is used. -/
theorem reused_fixed_call_hash_collision_or_alternative
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (released : ReleasedAllCall functions ecdsa ledger authorized)
    (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes)
    (attemptedValid : SighashAllWire.valid attempted)
    (scriptCodeValid : scriptCode.length < 256 ^ 8)
    (forbidden : SighashAllWire.projectionWithLedger ledger attempted ∉
      authorized)
    (checked : ecdsa released.sig released.key
      (functions.H (functions.H
        (SighashAllWire.sourceAllPreimage attempted selected
          scriptCode))) = true) :
    let oldPreimage := SighashAllWire.sourceAllPreimage
      released.tx released.selected released.scriptCode
    let newPreimage := SighashAllWire.sourceAllPreimage
      attempted selected scriptCode
    newPreimage ≠ oldPreimage ∧
      ((∃ a b : Bytes, a ≠ b ∧ functions.H a = functions.H b) ∨
        (functions.H (functions.H newPreimage) ∈
          (contract.targets released.sig released.key).erase
            (functions.H (functions.H oldPreimage)) ∧
        ((contract.targets released.sig released.key).erase
          (functions.H (functions.H oldPreimage))).card ≤ 7)) := by
  have prior := reused_fixed_call_collision_or_alternative
    functions ecdsa contract ledger authorized released attempted selected
    scriptCode attemptedValid scriptCodeValid forbidden checked
  dsimp at prior ⊢
  refine ⟨prior.1, ?_⟩
  rcases prior.2 with equalDigest | alternative
  · exact Or.inl (double_hash_collision_yields_hash_collision
      functions.H _ _ prior.1 equalDigest)
  · exact Or.inr alternative

end QSB.DynamicRetarget
