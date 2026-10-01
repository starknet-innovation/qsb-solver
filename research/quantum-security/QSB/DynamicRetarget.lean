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

/-- The deterministic event for a fixed signature/key pair previously checked
on an approved source-shaped ALL transaction. It contains an actual collision
in the shared H, or a hit in the other at most seven ECDSA wire targets. -/
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
    ((∃ a b : Bytes, a ≠ b ∧ functions.H a = functions.H b) ∨
      (functions.H (functions.H newPreimage) ∈
        (contract.targets released.sig released.key).erase
          (functions.H (functions.H oldPreimage)) ∧
      ((contract.targets released.sig released.key).erase
        (functions.H (functions.H oldPreimage))).card ≤ 7))

/-- A call without a matching approved signature/key record remains an
unmatched DER-shaped checked call. Matching on the key alone would be unsound:
an approved signature for a different role need not be the attempted one. -/
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
    SighashAllWire.sourceAllPreimage attempted selected scriptCode ∉
      DynamicDisclosureEvent.approvedAllPreimages ledger authorized ∧
    DERSyntax.valid (functions.H key) = true ∧
    ecdsa sig key (functions.H (functions.H
      (SighashAllWire.sourceAllPreimage attempted selected scriptCode))) = true) ∨
  ∃ released, findRelease history sig key = some released ∧
    RetargetEvent functions ecdsa contract ledger authorized released
      attempted selected scriptCode

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
      exact Or.inl ⟨rfl,
        DynamicDisclosureEvent.forbidden_all_preimage_fresh
          ledger authorized attempted selected scriptCode
          attemptedValid scriptCodeValid forbidden,
        der, checked⟩
  | some released =>
      have pair := findRelease_sound history sig key released lookup
      have releasedChecked : ecdsa released.sig released.key
          (functions.H (functions.H
            (SighashAllWire.sourceAllPreimage attempted selected
              scriptCode))) = true := by
        simpa [pair.1, pair.2] using checked
      refine Or.inr ⟨released, rfl, ?_⟩
      exact reused_fixed_call_hash_collision_or_alternative
        functions ecdsa contract ledger authorized released attempted
        selected scriptCode attemptedValid scriptCodeValid forbidden
        releasedChecked

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

end QSB.DynamicRetarget
