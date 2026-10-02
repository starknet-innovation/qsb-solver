import QSB.DynamicDisclosureEvent
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.EquivFin

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

theorem findRelease_mem
    {functions : JointSourceChecks.Functions}
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    {ledger : Game.Outpoint → Game.Output}
    {authorized : Set Game.Projection}
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (sig key : Bytes)
    (release : ReleasedAllCall functions ecdsa ledger authorized)
    (found : findRelease history sig key = some release) :
    release ∈ history := by
  induction history with
  | nil => simp [findRelease] at found
  | cons head rest ih =>
      by_cases matchPair : head.sig = sig ∧ head.key = key
      · simp [findRelease, matchPair] at found
        subst release
        exact List.mem_cons_self
      · simp [findRelease, matchPair] at found
        exact List.mem_cons_of_mem _ (ih found)

theorem findRelease_none_no_match
    {functions : JointSourceChecks.Functions}
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    {ledger : Game.Outpoint → Game.Output}
    {authorized : Set Game.Projection}
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (sig key : Bytes) :
    findRelease history sig key = none →
      ∀ release ∈ history, ¬(release.sig = sig ∧ release.key = key) := by
  induction history with
  | nil => simp
  | cons head rest ih =>
      intro missing release member pair
      by_cases headMatch : head.sig = sig ∧ head.key = key
      · simp [findRelease, headMatch] at missing
      · have tailMissing : findRelease rest sig key = none := by
          simpa [findRelease, headMatch] using missing
        rcases List.mem_cons.mp member with equal | tailMember
        · subst release
          exact headMatch pair
        · exact ih tailMissing release tailMember pair

/-- A key may have been disclosed in an approved call under a different
signature even when no exact signature/key record matches. -/
def KeyInHistory
    {functions : JointSourceChecks.Functions}
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    {ledger : Game.Outpoint → Game.Output}
    {authorized : Set Game.Projection}
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (key : Bytes) : Prop :=
  ∃ release ∈ history, release.key = key

theorem unmatched_known_key_has_other_signature
    {functions : JointSourceChecks.Functions}
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    {ledger : Game.Outpoint → Game.Output}
    {authorized : Set Game.Projection}
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (sig key : Bytes)
    (missing : findRelease history sig key = none)
    (known : KeyInHistory history key) :
    ∃ release ∈ history,
      release.key = key ∧ release.sig ≠ sig := by
  obtain ⟨release, member, sameKey⟩ := known
  refine ⟨release, member, sameKey, ?_⟩
  intro sameSig
  exact (findRelease_none_no_match history sig key missing
    release member) ⟨sameSig, sameKey⟩

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

/-- The collision is witnessed at one of two specific input pairs determined
by the approved and attempted ALL preimages. Unlike an unrestricted
existential collision, this event names the reached calls' actual inputs. -/
def WitnessedHashCollision {X : Type*} (H : X → X)
    (oldInput newInput : X) : Prop :=
  H oldInput = H newInput ∨
    (H oldInput ≠ H newInput ∧
      H (H oldInput) = H (H newInput))

theorem double_hash_collision_witnessed {X : Type*}
    (H : X → X) (oldInput newInput : X)
    (equal : H (H oldInput) = H (H newInput)) :
    WitnessedHashCollision H oldInput newInput := by
  by_cases firstEqual : H oldInput = H newInput
  · exact Or.inl firstEqual
  · exact Or.inr ⟨firstEqual, equal⟩

/-- The reached-pair event is exactly equality of the two double-hash
digests, with the first-round versus second-round collision made explicit. -/
theorem witnessed_collision_iff_double_equal {X : Type*}
    (H : X → X) (oldInput newInput : X) :
    WitnessedHashCollision H oldInput newInput ↔
      H (H oldInput) = H (H newInput) := by
  constructor
  · intro witnessed
    rcases witnessed with firstEqual | ⟨_, secondEqual⟩
    · exact congrArg H firstEqual
    · exact secondEqual
  · exact double_hash_collision_witnessed H oldInput newInput

theorem witnessed_collision_has_reached_pair {X : Type*}
    (H : X → X) (oldInput newInput : X)
    (different : oldInput ≠ newInput)
    (witnessed : WitnessedHashCollision H oldInput newInput) :
    ∃ a b : X,
      ((a = oldInput ∧ b = newInput) ∨
        (a = H oldInput ∧ b = H newInput)) ∧
      a ≠ b ∧ H a = H b := by
  rcases witnessed with firstEqual | ⟨firstDifferent, secondEqual⟩
  · exact ⟨oldInput, newInput, Or.inl ⟨rfl, rfl⟩,
      different, firstEqual⟩
  · exact ⟨H oldInput, H newInput, Or.inr ⟨rfl, rfl⟩,
      firstDifferent, secondEqual⟩

/-- A collision somewhere else in the function is not the reached-call
collision. The finite example has a collision at inputs 2 and 3, but its
outputs at approved input 0 and attempted input 1 remain distinct through
both hash rounds. -/
theorem unrelated_global_collision_counterexample :
    let H : Fin 4 → Fin 4 := fun x => if x = 3 then 2 else x
    (∃ a b : Fin 4, a ≠ b ∧ H a = H b) ∧
      ¬WitnessedHashCollision H 0 1 := by
  dsimp
  constructor
  · refine ⟨2, 3, ?_, ?_⟩ <;> decide
  · simp [WitnessedHashCollision]

/-- For a total fixed-width SHA-256-shaped function on all byte strings, the
unrestricted global collision event is true even before an adversary runs.
It therefore cannot itself receive a nontrivial query-success bound. -/
theorem fixed_width_global_collision (H : Bytes → Bytes)
    (width : ∀ input, (H input).length = 32) :
    ∃ a b : Bytes, a ≠ b ∧ H a = H b := by
  classical
  by_contra noCollision
  have injective : Function.Injective H := by
    intro a b equal
    by_contra different
    exact noCollision ⟨a, b, different, equal⟩
  let vectorized : Bytes → List.Vector UInt8 32 :=
    fun input => ⟨H input, width input⟩
  have vectorizedInjective : Function.Injective vectorized := by
    intro a b equal
    exact injective (congrArg Subtype.val equal)
  haveI : Finite Bytes := Finite.of_injective vectorized vectorizedInjective
  exact (inferInstance : Infinite Bytes).false

theorem joint_functions_global_collision
    (functions : JointSourceChecks.Functions) :
    ∃ a b : Bytes, a ≠ b ∧ functions.H a = functions.H b :=
  fixed_width_global_collision functions.H functions.H_width

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

/-- The equal-digest branch implies an ordinary collision in the *same*
SHA-256 oracle. This unrestricted existential consequence must not be used
as the quantum failure event: it is always true for a total fixed-width H.
The reached-pair event below is the one retained by history classification. -/
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

/-- Retain the collision's actual reached input pair. An unrestricted
`∃ a b, H a = H b` would be too broad to serve as a QROM failure event. -/
theorem reused_fixed_call_witnessed_collision_or_alternative
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
      (WitnessedHashCollision functions.H oldPreimage newPreimage ∨
        (newDigest ∈
          (contract.targets released.sig released.key).erase oldDigest ∧
        ((contract.targets released.sig released.key).erase
          oldDigest).card ≤ 7)) := by
  have prior := reused_fixed_call_collision_or_alternative
    functions ecdsa contract ledger authorized released attempted selected
    scriptCode attemptedValid scriptCodeValid forbidden checked
  dsimp at prior ⊢
  refine ⟨prior.1, ?_⟩
  rcases prior.2 with equalDigest | alternative
  · exact Or.inl (double_hash_collision_witnessed
      functions.H _ _ equalDigest.symm)
  · exact Or.inr alternative

/-- The deterministic event for a fixed signature/key pair previously checked
on an approved source-shaped ALL transaction. Its collision branch names the
specific reached preimages or their first H outputs; an arbitrary collision
elsewhere does not satisfy it. -/
def RetargetEvent
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (released : ReleasedAllCall functions ecdsa ledger authorized)
    (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) : Prop :=
  let oldPreimage := SighashAllWire.sourceAllPreimage
    released.tx released.selected released.scriptCode
  let newPreimage := SighashAllWire.sourceAllPreimage
    attempted selected scriptCode
  newPreimage ≠ oldPreimage ∧
    (WitnessedHashCollision functions.H oldPreimage newPreimage ∨
      (functions.H (functions.H newPreimage) ∈
        (contract.targets released.sig released.key).erase
          (functions.H (functions.H oldPreimage)) ∧
      ((contract.targets released.sig released.key).erase
        (functions.H (functions.H oldPreimage))).card ≤ 7))

/-- Classify a checked forbidden call by both exact-pair and key-only
release history. An unmatched pair with a previously released key is charged
to an at-most-eight digest target event, not a fresh DER-key event. A matching
pair uses the reached collision or at-most-seven alternative-target split. -/
def HistoryCallEvent
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (sig key : Bytes)
  (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) : Prop :=
  (findRelease history sig key = none ∧
    ¬KeyInHistory history key ∧
    SighashAllWire.sourceAllPreimage attempted selected scriptCode ∉
      DynamicDisclosureEvent.approvedAllPreimages ledger authorized ∧
    DERSyntax.valid (functions.H key) = true ∧
    ecdsa sig key (functions.H (functions.H
      (SighashAllWire.sourceAllPreimage attempted selected scriptCode))) = true) ∨
  (∃ released, findRelease history sig key = some released ∧
    RetargetEvent functions ecdsa contract ledger authorized released
      attempted selected scriptCode) ∨
  (findRelease history sig key = none ∧
    (∃ released ∈ history,
      released.key = key ∧ released.sig ≠ sig) ∧
    SighashAllWire.sourceAllPreimage attempted selected scriptCode ∉
      DynamicDisclosureEvent.approvedAllPreimages ledger authorized ∧
    DERSyntax.valid (functions.H key) = true ∧
    functions.H (functions.H
      (SighashAllWire.sourceAllPreimage attempted selected scriptCode)) ∈
        contract.targets sig key ∧
    (contract.targets sig key).card ≤ 8)

theorem classify_checked_call
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (sig key : Bytes)
    (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes)
    (attemptedValid : SighashAllWire.valid attempted)
    (scriptCodeValid : scriptCode.length < 256 ^ 8)
    (forbidden : SighashAllWire.projectionWithLedger ledger attempted ∉
      authorized)
    (der : DERSyntax.valid (functions.H key) = true)
    (checked : ecdsa sig key
      (functions.H (functions.H
        (SighashAllWire.sourceAllPreimage attempted selected scriptCode))) = true) :
    HistoryCallEvent functions ecdsa contract ledger authorized history
      sig key attempted selected scriptCode := by
  unfold HistoryCallEvent
  cases lookup : findRelease history sig key with
  | none =>
      have fresh := DynamicDisclosureEvent.forbidden_all_preimage_fresh
        ledger authorized attempted selected scriptCode
        attemptedValid scriptCodeValid forbidden
      by_cases known : KeyInHistory history key
      · exact Or.inr (Or.inr ⟨rfl,
          unmatched_known_key_has_other_signature history sig key
            lookup known,
          fresh, der, contract.sound sig key _ checked,
          contract.card_le_eight sig key⟩)
      · exact Or.inl ⟨rfl, known, fresh, der, checked⟩
  | some released =>
      have pair := findRelease_sound history sig key released lookup
      have releasedChecked : ecdsa released.sig released.key
          (functions.H (functions.H
            (SighashAllWire.sourceAllPreimage attempted selected
              scriptCode))) = true := by
        simpa [pair.1, pair.2] using checked
      refine Or.inr (Or.inl ⟨released, rfl, ?_⟩)
      exact reused_fixed_call_witnessed_collision_or_alternative
        functions ecdsa contract ledger authorized released attempted
        selected scriptCode attemptedValid scriptCodeValid forbidden
        releasedChecked

/-- A supplied set of publicly disclosed keys, which may contain more than
the keys in the approved-call list. Completeness is an external premise. -/
def PublicKnownKey
    {functions : JointSourceChecks.Functions}
    {ecdsa : Bytes → Bytes → Bytes → Bool}
    {ledger : Game.Outpoint → Game.Output}
    {authorized : Set Game.Projection}
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (publicKeys : Set Bytes) (key : Bytes) : Prop :=
  key ∈ publicKeys ∨ KeyInHistory history key

/-- A call with no exact approved signature/key record has a new DER-key
branch only relative to the supplied public-key set. If the key is
already public, its checked digest is instead charged to at most eight ECDSA
wire targets. Exact-pair reuse retains the reached collision/seven-target
split. This deterministic event makes no oracle-query or independence claim. -/
def PublicHistoryCallEvent
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (publicKeys : Set Bytes)
    (sig key : Bytes)
    (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) : Prop :=
  (findRelease history sig key = none ∧
    ¬PublicKnownKey history publicKeys key ∧
    SighashAllWire.sourceAllPreimage attempted selected scriptCode ∉
      DynamicDisclosureEvent.approvedAllPreimages ledger authorized ∧
    DERSyntax.valid (functions.H key) = true ∧
    ecdsa sig key (functions.H (functions.H
      (SighashAllWire.sourceAllPreimage attempted selected scriptCode))) = true) ∨
  (findRelease history sig key = none ∧
    PublicKnownKey history publicKeys key ∧
    SighashAllWire.sourceAllPreimage attempted selected scriptCode ∉
      DynamicDisclosureEvent.approvedAllPreimages ledger authorized ∧
    DERSyntax.valid (functions.H key) = true ∧
    functions.H (functions.H
      (SighashAllWire.sourceAllPreimage attempted selected scriptCode)) ∈
        contract.targets sig key ∧
    (contract.targets sig key).card ≤ 8) ∨
  (∃ released, findRelease history sig key = some released ∧
    RetargetEvent functions ecdsa contract ledger authorized released
      attempted selected scriptCode)

theorem history_event_public_case
    (functions : JointSourceChecks.Functions)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (publicKeys : Set Bytes)
    (sig key : Bytes)
    (attempted : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes)
    (event : HistoryCallEvent functions ecdsa contract ledger authorized
      history sig key attempted selected scriptCode) :
    PublicHistoryCallEvent functions ecdsa contract ledger authorized
      history publicKeys sig key attempted selected scriptCode := by
  unfold HistoryCallEvent at event
  unfold PublicHistoryCallEvent
  rcases event with ⟨missing, noHistory, fresh, der, checked⟩ |
      ⟨released, found, retarget⟩ |
      ⟨missing, otherSignature, fresh, der, targetHit, targetCount⟩
  · by_cases isPublished : key ∈ publicKeys
    · exact Or.inr (Or.inl ⟨missing, Or.inl isPublished, fresh, der,
        contract.sound sig key _ checked, contract.card_le_eight sig key⟩)
    · have unknown : ¬PublicKnownKey history publicKeys key := by
        intro known
        rcases known with published | recorded
        · exact isPublished published
        · exact noHistory recorded
      exact Or.inl ⟨missing, unknown, fresh, der, checked⟩
  · exact Or.inr (Or.inr ⟨released, found, retarget⟩)
  · obtain ⟨released, member, sameKey, _otherSig⟩ := otherSignature
    exact Or.inr (Or.inl ⟨missing,
      Or.inr ⟨released, member, sameKey⟩,
      fresh, der, targetHit, targetCount⟩)

/-- Apply the transcript classification to the two actual modeled source
checks, preserving their reached signature/key roles and scriptCode bytes.
This is a deterministic source-search implication; a Core acceptance bridge
and the shared-query QROM probability bound are separate obligations. -/
theorem search_pin_final_history_cases
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final))
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (txValid : SighashAllWire.valid tx)
    (forbidden : SighashAllWire.projectionWithLedger ledger tx ∉
      authorized) :
    ∃ (pinKey finalKey : Bytes)
      (beforePin beforeCheck : CoreOpcodeStep.State),
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 2)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforePin ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      DynamicJointTransaction.reachedPinSignature beforePin = lock.pin ∧
      DynamicJointTransaction.reachedPinKey beforePin = pinKey ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some finalKey ∧
      HistoryCallEvent functions ecdsa contract ledger authorized history
        lock.pin.dropLast pinKey tx selected
        (DynamicJointTransaction.reachedPinScriptCode lock beforePin) ∧
      HistoryCallEvent functions ecdsa contract ledger authorized history
        lock.nonce1.dropLast finalKey tx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          beforeCheck.stack.reverse 10 10) := by
  obtain ⟨pinKey, finalKey, beforePin, beforeCheck,
    pinReached, checkReached, pinSig, pinKeyAt, nonceSig,
    finalKeyAt, pinDER, finalDER, _input, pinVerified, finalVerified⟩ :=
    DynamicJointTransaction.search_two_key_joint_hit functions tx selected
      lock secondWidth stack validKey ecdsa firstRound final found
      pinAll nonceAll
  have wireBound : (DynamicCheckedCertificate.wire lock).length <
      256 ^ 8 := by
    have h := (DynamicScriptLimits.full_wire_below_core_limit
      lock.pin lock.nonce0 lock.nonce1
      lock.firstCommitment lock.secondCommitment
      firstWidth secondWidth pinShort nonce0Short nonce1Short).2
    change (DynamicCheckedCertificate.wire lock).length < 10000 at h
    exact lt_trans h (by decide)
  have pinCodeBound :
      (DynamicJointTransaction.reachedPinScriptCode lock beforePin).length <
        256 ^ 8 := by
    apply lt_of_le_of_lt _ wireBound
    simpa [DynamicJointTransaction.reachedPinScriptCode] using
      CoreFindAndDelete.run_length_le 880
        (DynamicCheckedCertificate.wire lock)
        (CorePushSerialize.pushPattern
          (DynamicJointTransaction.reachedPinSignature beforePin))
  have finalCodeBound :
      (CoreMultisigSourceScan.deletedScript
        (DynamicCheckedCertificate.wire lock)
        beforeCheck.stack.reverse 10 10).length < 256 ^ 8 := by
    apply lt_of_le_of_lt _ wireBound
    simpa [CoreMultisigSourceScan.deletedScript] using
      CoreFindAndDelete.runMany_length_le 880
        (DynamicCheckedCertificate.wire lock)
        ((CoreMultisigSourceScan.reachedSignatures
          beforeCheck.stack.reverse 10 10).map
          CorePushSerialize.pushPattern)
  refine ⟨pinKey, finalKey, beforePin, beforeCheck,
    pinReached, checkReached, pinSig, pinKeyAt,
    nonceSig, finalKeyAt, ?_, ?_⟩
  · exact classify_checked_call functions ecdsa contract ledger authorized
      history lock.pin.dropLast pinKey tx selected
      (DynamicJointTransaction.reachedPinScriptCode lock beforePin)
      txValid pinCodeBound forbidden pinDER pinVerified
  · exact classify_checked_call functions ecdsa contract ledger authorized
      history lock.nonce1.dropLast finalKey tx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicCheckedCertificate.wire lock)
        beforeCheck.stack.reverse 10 10)
      txValid finalCodeBound forbidden finalDER finalVerified

/-- The seven reached HASH160 openings and both classified ALL calls belong
to one modeled source certificate and use the same H and R functions. This
is a deterministic necessary event to charge in a later adaptive QROM game; no
query-success estimate or compiled-Core acceptance implication is asserted. -/
theorem search_good_setup_joint_history_event
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final))
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (txValid : SighashAllWire.valid tx)
    (forbidden : SighashAllWire.projectionWithLedger ledger tx ∉
      authorized) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (pinKey finalKey : Bytes)
      (beforePin beforeCheck : CoreOpcodeStep.State),
      DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions)
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment)
        ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace,
        functions.R (functions.H p.2) = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 2)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforePin ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      DynamicJointTransaction.reachedPinSignature beforePin = lock.pin ∧
      DynamicJointTransaction.reachedPinKey beforePin = pinKey ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some finalKey ∧
      HistoryCallEvent functions ecdsa contract ledger authorized history
        lock.pin.dropLast pinKey tx selected
        (DynamicJointTransaction.reachedPinScriptCode lock beforePin) ∧
      HistoryCallEvent functions ecdsa contract ledger authorized history
        lock.nonce1.dropLast finalKey tx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          beforeCheck.stack.reverse 10 10) := by
  obtain ⟨trace, a, b, extracted, seven, hits, distinct, count⟩ :=
    DynamicCheckedCertificate.search_good_setup_nine_positions
      (JointSourceChecks.hashes functions) lock firstWidth secondWidth
      pinShort nonce0Short nonce1Short stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa)
      firstRound final found noCommitmentDER
  obtain ⟨pinKey, finalKey, beforePin, beforeCheck,
    pinReached, checkReached, pinSig, pinKeyAt, nonceSig,
    finalKeyAt, pinCase, finalCase⟩ :=
    search_pin_final_history_cases functions tx selected lock firstWidth
      secondWidth pinShort nonce0Short nonce1Short stack validKey ecdsa
      contract firstRound final found pinAll nonceAll ledger authorized
      history txValid forbidden
  exact ⟨trace, a, b, pinKey, finalKey, beforePin, beforeCheck,
    extracted, seven, by simpa [JointSourceChecks.hashes] using hits,
    distinct, count, pinReached, checkReached, pinSig, pinKeyAt,
    nonceSig, finalKeyAt, pinCase, finalCase⟩

/-- The same good-setup source certificate classifies both reached ALL calls
relative to one supplied terminal public-key set. A disclosed key with no
approved-call record takes the finite digest-target branch. This does not
prove that an undisclosed key is fresh to a quantum oracle transcript. -/
theorem search_good_setup_joint_public_history_event
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock)
    (firstWidth : ∀ i, (lock.firstCommitment i).length = 20)
    (secondWidth : ∀ i, (lock.secondCommitment i).length = 20)
    (pinShort : lock.pin.length < 76)
    (nonce0Short : lock.nonce0.length < 76)
    (nonce1Short : lock.nonce1.length < 76)
    (stack : List Bytes) (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (contract : DynamicDisclosureEvent.ECDSATargets ecdsa)
    (firstRound : Bool) (final : CoreOpcodeStep.State)
    (found : DynamicCheckedCertificate.search
      (JointSourceChecks.hashes functions) lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) =
        some (firstRound, final))
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (lock.secondCommitment id) = false)
    (pinAll : lock.pin.getLast? = some 0x01)
    (nonceAll : lock.nonce1.getLast? = some 0x01)
    (ledger : Game.Outpoint → Game.Output)
    (authorized : Set Game.Projection)
    (history : List (ReleasedAllCall functions ecdsa ledger authorized))
    (publicKeys : Set Bytes)
    (txValid : SighashAllWire.valid tx)
    (forbidden : SighashAllWire.projectionWithLedger ledger tx ∉
      authorized) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
      (pinKey finalKey : Bytes)
      (beforePin beforeCheck : CoreOpcodeStep.State),
      DynamicWholeSource.extractTrace (JointSourceChecks.hashes functions)
        (DynamicFullSerialized.priorOps lock.pin lock.nonce0
          lock.firstCommitment)
        ⟨stack, CoreCheckedCertificate.outcomes firstRound, 0⟩ =
          some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace,
        functions.R (functions.H p.2) = lock.secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        ((DynamicCheckedCertificate.program lock).take 2)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforePin ∧
      CoreStructuralRun.run (JointSourceChecks.hashes functions)
        (DynamicCheckedCertificate.beforeFinalProgram lock)
        (DynamicCheckedCertificate.initial stack firstRound) =
          some beforeCheck ∧
      DynamicJointTransaction.reachedPinSignature beforePin = lock.pin ∧
      DynamicJointTransaction.reachedPinKey beforePin = pinKey ∧
      CoreMultisigStack.signatureAt beforeCheck.stack 10 9 =
        some lock.nonce1 ∧
      CoreMultisigStack.keyAt beforeCheck.stack 9 = some finalKey ∧
      PublicHistoryCallEvent functions ecdsa contract ledger authorized
        history publicKeys lock.pin.dropLast pinKey tx selected
        (DynamicJointTransaction.reachedPinScriptCode lock beforePin) ∧
      PublicHistoryCallEvent functions ecdsa contract ledger authorized
        history publicKeys lock.nonce1.dropLast finalKey tx selected
        (CoreMultisigSourceScan.deletedScript
          (DynamicCheckedCertificate.wire lock)
          beforeCheck.stack.reverse 10 10) := by
  obtain ⟨trace, a, b, pinKey, finalKey, beforePin, beforeCheck,
    extracted, seven, hits, distinct, count, pinReached, checkReached,
    pinSig, pinKeyAt, nonceSig, finalKeyAt, pinCase, finalCase⟩ :=
      search_good_setup_joint_history_event functions tx selected lock
        firstWidth secondWidth pinShort nonce0Short nonce1Short stack
        validKey ecdsa contract firstRound final found noCommitmentDER
        pinAll nonceAll ledger authorized history txValid forbidden
  exact ⟨trace, a, b, pinKey, finalKey, beforePin, beforeCheck,
    extracted, seven, hits, distinct, count, pinReached, checkReached,
    pinSig, pinKeyAt, nonceSig, finalKeyAt,
    history_event_public_case functions ecdsa contract ledger authorized
      history publicKeys lock.pin.dropLast pinKey tx selected
      (DynamicJointTransaction.reachedPinScriptCode lock beforePin) pinCase,
    history_event_public_case functions ecdsa contract ledger authorized
      history publicKeys lock.nonce1.dropLast finalKey tx selected
      (CoreMultisigSourceScan.deletedScript
        (DynamicCheckedCertificate.wire lock)
        beforeCheck.stack.reverse 10 10) finalCase⟩

end QSB.DynamicRetarget
