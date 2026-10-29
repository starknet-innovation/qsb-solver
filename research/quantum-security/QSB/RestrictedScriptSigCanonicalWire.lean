import QSB.CorePushSerialize
import QSB.RestrictedScriptSigHash160

/-!
Canonical byte encoding for the restricted direct-push `scriptSig` fragment.
This connects the fragment's parser to the existing source-shaped Core push
serializer, only for payloads shorter than 76 bytes. It does not establish
equivalence with compiled Bitcoin Core, its general script parser, or its
execution trace.
-/
namespace QSB.RestrictedScriptSigCanonicalWire
open ByteMachine
open RestrictedScriptSigHash160

/-- The restricted parser consumes exactly one Core-shaped short push and
leaves the following bytes untouched. -/
theorem directPush_pushPattern (data tail : Bytes)
    (short : data.length < 76) :
    directPush (CorePushSerialize.pushPattern data ++ tail) =
      some (data, tail) := by
  have width : (UInt8.ofNat data.length).toNat = data.length :=
    UInt8.toNat_ofNat_of_lt (by change data.length < 256; omega)
  have small : data.length ≤ 75 := by omega
  simp [directPush, CorePushSerialize.pushPattern, short, width,
    small]

/-- One canonical direct-push fragment: opening, HASH160, expected digest,
EQUALVERIFY, and one payload cell. -/
def canonical (opening expected payload : Bytes) : Bytes :=
  CorePushSerialize.pushPattern opening ++ [0xa9] ++
    CorePushSerialize.pushPattern expected ++ [0x88] ++
    CorePushSerialize.pushPattern payload

theorem hashPrefix_canonical (opening expected payload : Bytes)
    (openingShort : opening.length < 76) :
    hashPrefix (canonical opening expected payload) =
      some (opening,
        CorePushSerialize.pushPattern expected ++ [0x88] ++
          CorePushSerialize.pushPattern payload) := by
  simp [canonical, hashPrefix, directPush_pushPattern,
    openingShort, List.append_assoc]

theorem suffix_canonical (expected payload digest : Bytes)
    (expectedShort : expected.length < 76)
    (payloadShort : payload.length < 76) :
    suffix (CorePushSerialize.pushPattern expected ++ [0x88] ++
      CorePushSerialize.pushPattern payload) digest =
      if digest = expected then some [payload] else none := by
  have pushed := directPush_pushPattern expected
    ([0x88] ++ CorePushSerialize.pushPattern payload) expectedShort
  have finalPush := directPush_pushPattern payload [] payloadShort
  have pushed' :
      directPush (CorePushSerialize.pushPattern expected ++ [0x88] ++
        CorePushSerialize.pushPattern payload) =
        some (expected, [0x88] ++ CorePushSerialize.pushPattern payload) := by
    simpa only [List.append_assoc] using pushed
  have finalPush' : directPush (CorePushSerialize.pushPattern payload) =
      some (payload, []) := by simpa using finalPush
  by_cases hit : digest = expected
  · unfold suffix
    rw [pushed']
    simp [finalPush', hit]
  · unfold suffix
    rw [pushed']
    simp [hit]

/-- The evaluator's result on exactly the canonical bytes is determined by
the one HASH160 comparison; transaction fields are unused by this fragment. -/
theorem eval_canonical
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (opening expected payload : Bytes)
    (openingShort : opening.length < 76)
    (expectedShort : expected.length < 76)
    (payloadShort : payload.length < 76) :
    eval functions tx selected (canonical opening expected payload) =
      if functions.R (functions.H opening) = expected then
        some [payload] else none := by
  unfold eval
  rw [hashPrefix_canonical opening expected payload openingShort]
  exact suffix_canonical expected payload
    (functions.R (functions.H opening)) expectedShort payloadShort

end QSB.RestrictedScriptSigCanonicalWire
