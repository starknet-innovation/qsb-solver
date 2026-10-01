import QSB.Game
import QSB.Nonce
import QSB.OutputCodec
import QSB.WireOutputs
import QSB.SighashAllWire
import QSB.RecoveryCandidates

/-!
The authorization-to-sighash bridge for a legacy SIGHASH_ALL check. In the
fixed-context theorem, the only varying wire segment is the serialized
ordered output list. The arbitrary-context theorem ranges over signed
transactions, including their possibly different scriptCodes, and assumes a
decoder can recover ordered outputs from every relevant preimage. These wire
premises do not claim that Core's C++ serializer has been refined to Lean.
`hash` and `RecoveryEquation` also require a separate Bitcoin/ECDSA
refinement. A different preimage alone does NOT imply that a fixed
signature/key fails: any admissible recovery point yields a message target,
and multiple preimages may hash to one of those targets.
-/
namespace QSB.SighashBinding

abbrev Bytes := List UInt8

/-- Legacy ALL preimage shape when every non-output field, including the
selected scriptCode and four-byte sighash type, is fixed. -/
def allPreimage (contextBefore suffix : Bytes)
    (encodeOutputs : List Game.Output → Bytes)
    (outputs : List Game.Output) : Bytes :=
  contextBefore ++ encodeOutputs outputs ++ suffix

/-- Different ordered outputs have different preimages if their full wire
encoding is injective. The shape alone does not prove that Core computes this
encoding, nor any hash collision bound. -/
theorem changed_outputs_distinct_preimages
    (contextBefore suffix : Bytes)
    (encodeOutputs : List Game.Output → Bytes)
    (wireInjective : Function.Injective encodeOutputs)
    {released attempted : List Game.Output}
    (changed : attempted ≠ released) :
    allPreimage contextBefore suffix encodeOutputs attempted ≠
      allPreimage contextBefore suffix encodeOutputs released := by
  intro equal
  unfold allPreimage at equal
  have encoded : encodeOutputs attempted = encodeOutputs released := by
    exact List.append_cancel_left (List.append_cancel_right equal)
  exact changed (wireInjective encoded)

/-- A stronger fixed-context boundary for the source-shaped output layout.
Prefix-codec laws for the count and amount fields, restricted to valid Core
values, suffice for ordered-output injectivity; script length framing and
list composition are proved in `OutputCodec`. -/
theorem changed_outputs_distinct_preimages_of_codecs
    (contextBefore suffix : Bytes)
    (count amount : OutputCodec.PrefixCodec Nat)
    {released attempted : List Game.Output}
    (releasedCount : count.valid released.length)
    (attemptedCount : count.valid attempted.length)
    (releasedValues : ∀ out ∈ released,
      amount.valid out.value ∧ count.valid out.script.length)
    (attemptedValues : ∀ out ∈ attempted,
      amount.valid out.value ∧ count.valid out.script.length)
    (changed : attempted ≠ released) :
    allPreimage contextBefore suffix
        (OutputCodec.sourceShapedOutputs count amount) attempted ≠
      allPreimage contextBefore suffix
        (OutputCodec.sourceShapedOutputs count amount) released := by
  intro equal
  unfold allPreimage at equal
  have encoded := List.append_cancel_left (List.append_cancel_right equal)
  exact changed (OutputCodec.sourceShapedOutputs_injective_on count amount
    attemptedCount releasedCount attemptedValues releasedValues encoded)

/-- All output-field byte encodings are now concrete. The only serializer
premise left outside this theorem is that Core's actual legacy ALL preimage
contains this output segment with unchanged surrounding bytes. -/
theorem changed_outputs_distinct_preimages_of_wire_bytes
    (contextBefore suffix : Bytes)
    {released attempted : List Game.Output}
    (releasedValid : WireOutputs.validOutputs released)
    (attemptedValid : WireOutputs.validOutputs attempted)
    (changed : attempted ≠ released) :
    allPreimage contextBefore suffix WireOutputs.encode attempted ≠
      allPreimage contextBefore suffix WireOutputs.encode released := by
  intro equal
  unfold allPreimage at equal
  have encoded := List.append_cancel_left (List.append_cancel_right equal)
  exact changed (WireOutputs.encode_injective_on attemptedValid releasedValid encoded)

/-- The parser contract needed when other transaction fields or selected
scriptCode vary. If the ordered output projection can be decoded from every
relevant ALL preimage, different output projections cannot share a preimage.
The actual Core serializer/parser round trip is NOT established here. -/
theorem changed_outputs_any_context_distinct_preimages
    {SignedTx : Type*}
    (serialize : SignedTx → Bytes)
    (outputs : SignedTx → List Game.Output)
    (parseOutputs : Bytes → Option (List Game.Output))
    (roundtrip : ∀ tx, parseOutputs (serialize tx) = some (outputs tx))
    {released attempted : SignedTx}
    (changed : outputs attempted ≠ outputs released) :
    serialize attempted ≠ serialize released := by
  intro equal
  have same : some (outputs attempted) = some (outputs released) := by
    calc
      some (outputs attempted) = parseOutputs (serialize attempted) :=
        (roundtrip attempted).symm
      _ = parseOutputs (serialize released) := congrArg parseOutputs equal
      _ = some (outputs released) := roundtrip released
  exact changed (Option.some.inj same)

/-- A changed-output verification by the same fixed signature and public key
implies a hit on the key's finite message-target set, not necessarily a
SHA256d collision with the released transaction. This is conditional on the
actual verified ECDSA recovery point belonging to `points` and on the hash
and group-element conversion represented by `hash`. -/
theorem changed_outputs_same_key_requires_target
    {F G : Type*} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (contextBefore suffix : Bytes)
    (encodeOutputs : List Game.Output → Bytes)
    (wireInjective : Function.Injective encodeOutputs)
    (hash : Bytes → G) (r s : F) (key : G) (points : Finset G)
    {released attempted : List Game.Output}
    (changed : attempted ≠ released)
    (verified : ∃ R ∈ points,
      RecoveryEquation r s R
        (hash (allPreimage contextBefore suffix encodeOutputs attempted)) key) :
    allPreimage contextBefore suffix encodeOutputs attempted ≠
        allPreimage contextBefore suffix encodeOutputs released ∧
      hash (allPreimage contextBefore suffix encodeOutputs attempted) ∈
        messageTargets r s key points := by
  refine ⟨changed_outputs_distinct_preimages contextBefore suffix encodeOutputs
    wireInjective changed, ?_⟩
  obtain ⟨R, present, equation⟩ := verified
  exact recovery_in_messageTargets r s key _ R points present equation

/-- The same target-set conclusion for varying non-output fields, under a
round-trip parser premise for the complete preimage. It preserves the
distinction between a different preimage and a different hash value. -/
theorem changed_outputs_any_context_same_key_target
    {F G SignedTx : Type*} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (serialize : SignedTx → Bytes)
    (outputs : SignedTx → List Game.Output)
    (parseOutputs : Bytes → Option (List Game.Output))
    (roundtrip : ∀ tx, parseOutputs (serialize tx) = some (outputs tx))
    (hash : Bytes → G) (r s : F) (key : G) (points : Finset G)
    {released attempted : SignedTx}
    (changed : outputs attempted ≠ outputs released)
    (verified : ∃ R ∈ points,
      RecoveryEquation r s R (hash (serialize attempted)) key) :
    serialize attempted ≠ serialize released ∧
      hash (serialize attempted) ∈ messageTargets r s key points := by
  refine ⟨changed_outputs_any_context_distinct_preimages
    serialize outputs parseOutputs roundtrip changed, ?_⟩
  obtain ⟨R, present, equation⟩ := verified
  exact recovery_in_messageTargets r s key _ R points present equation

/-- For the complete source-shaped ALL preimage, the parser premise above is
proved for valid wire transactions, even when their prepared input scripts,
version, input count, and locktime differ. The Core C++ serializer and actual
ECDSA verification remain external to this theorem. -/
theorem source_shaped_all_changed_outputs_same_key_target
    {F G : Type*} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (hash : Bytes → G) (r s : F) (key : G) (points : Finset G)
    {released attempted : { tx : SighashAllWire.TxFields // SighashAllWire.valid tx }}
    (changed : attempted.val.outputs ≠ released.val.outputs)
    (verified : ∃ R ∈ points,
      RecoveryEquation r s R (hash (SighashAllWire.encode attempted.val)) key) :
    SighashAllWire.encode attempted.val ≠ SighashAllWire.encode released.val ∧
      hash (SighashAllWire.encode attempted.val) ∈ messageTargets r s key points := by
  exact changed_outputs_any_context_same_key_target
    (fun tx : { tx : SighashAllWire.TxFields // SighashAllWire.valid tx } =>
      SighashAllWire.encode tx.val)
    (fun tx => tx.val.outputs) SighashAllWire.decodeOutputs
    (fun tx => SighashAllWire.decodeOutputs_encode tx.val tx.property)
    hash r s key points changed verified

/-- A source-shaped changed-output same-key verification has a distinct
preimage and an unsigned digest in a set of at most eight values. The actual
Core verifier, point admissibility, digest-to-scalar reduction, and joint
SHA256d quantum target-hit bound are explicit external obligations. -/
theorem source_all_changed_outputs_wire_digest_target
    {F G : Type*} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (hash : Bytes → G) (digest : Bytes → Nat) (residueOf : G → Nat)
    (r s : F) (key : G) (points : Finset G)
    (xCoord : G → Nat) (rNat : Nat)
    (admissible : ∀ R ∈ points,
      xCoord R < RecoveryCandidates.secpFieldPrime ∧
        xCoord R % RecoveryCandidates.secpGroupOrder = rNat)
    (fiber : ∀ x, (points.filter (fun R => xCoord R = x)).card ≤ 2)
    {released attempted : SighashAllWire.TxFields}
    (releasedSelected attemptedSelected : Nat)
    (releasedScript attemptedScript : Bytes)
    (releasedValid : SighashAllWire.valid released)
    (attemptedValid : SighashAllWire.valid attempted)
    (releasedScriptValid : releasedScript.length < 256 ^ 8)
    (attemptedScriptValid : attemptedScript.length < 256 ^ 8)
    (changed : attempted.outputs ≠ released.outputs)
    (verified : ∃ R ∈ points,
      RecoveryEquation r s R
        (hash (SighashAllWire.sourceAllPreimage attempted attemptedSelected
          attemptedScript)) key)
    (wire : digest (SighashAllWire.sourceAllPreimage attempted attemptedSelected
      attemptedScript) < 2 ^ 256)
    (reduction : digest (SighashAllWire.sourceAllPreimage attempted
      attemptedSelected attemptedScript) % RecoveryCandidates.secpGroupOrder =
      residueOf (hash (SighashAllWire.sourceAllPreimage attempted
        attemptedSelected attemptedScript))) :
    SighashAllWire.sourceAllPreimage attempted attemptedSelected attemptedScript ≠
      SighashAllWire.sourceAllPreimage released releasedSelected releasedScript ∧
    digest (SighashAllWire.sourceAllPreimage attempted attemptedSelected
      attemptedScript) ∈
      RecoveryCandidates.digestTargets RecoveryCandidates.secpGroupOrder
        (2 ^ 256) ((messageTargets r s key points).image residueOf) ∧
    (RecoveryCandidates.digestTargets RecoveryCandidates.secpGroupOrder
      (2 ^ 256) ((messageTargets r s key points).image residueOf)).card ≤ 8 := by
  let attemptedPreimage := SighashAllWire.sourceAllPreimage attempted
    attemptedSelected attemptedScript
  obtain ⟨R, present, equation⟩ := verified
  have target : hash attemptedPreimage ∈ messageTargets r s key points :=
    recovery_in_messageTargets r s key _ R points present equation
  exact ⟨SighashAllWire.changed_outputs_sourceAll_distinct_preimages
      releasedSelected attemptedSelected releasedScript attemptedScript
      releasedValid attemptedValid releasedScriptValid attemptedScriptValid changed,
    RecoveryCandidates.secp_digest_in_targetSet r s key points residueOf
      (digest attemptedPreimage) (hash attemptedPreimage) wire target reduction,
    RecoveryCandidates.secp_digestTargets_card_le_eight r s key points
      xCoord rNat residueOf admissible fiber⟩

end QSB.SighashBinding
