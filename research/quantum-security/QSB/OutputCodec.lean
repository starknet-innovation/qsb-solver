import QSB.Game

/-!
Compositional prefix-decoding obligation for Bitcoin's ordered outputs.
The full legacy ALL serializer writes a CompactSize output count followed by
each output's value and length-prefixed script. This module proves that if
the count, value, and script field codecs each decode their own encoding at
the front of arbitrary trailing bytes, the composed output list does too.
Concrete equality with Core's CompactSize, signed 64-bit amount, and script
serialization remains to be established.
-/
namespace QSB.OutputCodec

abbrev Bytes := List UInt8

structure PrefixCodec (α : Type*) where
  valid : α → Prop
  encode : α → Bytes
  decode : Bytes → Option (α × Bytes)
  roundtrip : ∀ value, valid value → ∀ tail,
    decode (encode value ++ tail) = some (value, tail)

/-- Bitcoin script byte vectors use a CompactSize length followed by exactly
that many bytes. This construction only assumes a correct count codec; it
proves the framing and payload round trip for arbitrary script bytes. -/
def lengthPrefixedBytesCodec (count : PrefixCodec Nat) : PrefixCodec Bytes where
  valid := fun payload => count.valid payload.length
  encode := fun payload => count.encode payload.length ++ payload
  decode := fun bytes => do
    let (n, rest) ← count.decode bytes
    if n ≤ rest.length then
      return (rest.take n, rest.drop n)
    else
      none
  roundtrip := by
    intro payload valid tail
    simp only [List.append_assoc]
    change (do
      let (n, rest) ← count.decode
        (count.encode payload.length ++ (payload ++ tail))
      if n ≤ rest.length then
        some (rest.take n, rest.drop n)
      else
        none) = some (payload, tail)
    rw [count.roundtrip _ valid]
    simp

def outputCodec (amount : PrefixCodec Nat) (script : PrefixCodec Bytes) :
    PrefixCodec Game.Output where
  valid := fun out => amount.valid out.value ∧ script.valid out.script
  encode := fun out => amount.encode out.value ++ script.encode out.script
  decode := fun bytes => do
    let (value, rest) ← amount.decode bytes
    let (scriptBytes, tail) ← script.decode rest
    return ({ value := value, script := scriptBytes }, tail)
  roundtrip := by
    intro out valid tail
    simp only [List.append_assoc]
    change (do
      let (value, rest) ← amount.decode
        (amount.encode out.value ++ (script.encode out.script ++ tail))
      let (scriptBytes, finalTail) ← script.decode rest
      return ({ value := value, script := scriptBytes }, finalTail)) =
      some (out, tail)
    simp [amount.roundtrip _ valid.1, script.roundtrip _ valid.2]

def encodeItems {α : Type*} (item : PrefixCodec α) : List α → Bytes
  | [] => []
  | value :: rest => item.encode value ++ encodeItems item rest

def decodeItems {α : Type*} (item : PrefixCodec α) : Nat → Bytes →
    Option (List α × Bytes)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let (value, rest) ← item.decode bytes
      let (items, tail) ← decodeItems item n rest
      return (value :: items, tail)

theorem decodeItems_encodeItems {α : Type*} (item : PrefixCodec α)
    (items : List α) (tail : Bytes) :
    (∀ value ∈ items, item.valid value) →
    decodeItems item items.length (encodeItems item items ++ tail) =
      some (items, tail) := by
  induction items with
  | nil => intro _; rfl
  | cons value rest ih =>
      intro valid
      have head : item.valid value := valid value (by simp)
      have tailValid : ∀ x ∈ rest, item.valid x := by
        intro x hx
        exact valid x (by simp [hx])
      simp [encodeItems, decodeItems, List.append_assoc,
        item.roundtrip _ head, ih tailValid]

def encodeOutputs (count : PrefixCodec Nat) (item : PrefixCodec Game.Output)
    (outputs : List Game.Output) : Bytes :=
  count.encode outputs.length ++ encodeItems item outputs

def decodeOutputs (count : PrefixCodec Nat) (item : PrefixCodec Game.Output)
    (bytes : Bytes) : Option (List Game.Output × Bytes) := do
  let (n, rest) ← count.decode bytes
  decodeItems item n rest

theorem decodeOutputs_encodeOutputs (count : PrefixCodec Nat)
    (item : PrefixCodec Game.Output) (outputs : List Game.Output)
    (tail : Bytes)
    (validCount : count.valid outputs.length)
    (validItems : ∀ out ∈ outputs, item.valid out) :
    decodeOutputs count item (encodeOutputs count item outputs ++ tail) =
      some (outputs, tail) := by
  simp [decodeOutputs, encodeOutputs, List.append_assoc,
    count.roundtrip _ validCount, decodeItems_encodeItems _ _ _ validItems]

theorem encodeOutputs_injective_on (count : PrefixCodec Nat)
    (item : PrefixCodec Game.Output)
    {left right : List Game.Output}
    (leftCount : count.valid left.length)
    (rightCount : count.valid right.length)
    (leftItems : ∀ out ∈ left, item.valid out)
    (rightItems : ∀ out ∈ right, item.valid out)
    (equal : encodeOutputs count item left = encodeOutputs count item right) :
    left = right := by
  have h := congrArg (decodeOutputs count item) equal
  have leftRoundtrip := decodeOutputs_encodeOutputs count item left [] leftCount leftItems
  have rightRoundtrip := decodeOutputs_encodeOutputs count item right [] rightCount rightItems
  simp only [List.append_nil] at leftRoundtrip rightRoundtrip
  rw [leftRoundtrip, rightRoundtrip] at h
  exact congrArg Prod.fst (Option.some.inj h)

/-- Count, then for each output an amount and a count-prefixed script. The
remaining byte-level premises are concrete valid-domain CompactSize counts
and 64-bit amounts, plus equality with Core's field serialization. -/
def sourceShapedOutputs (count amount : PrefixCodec Nat)
    (outputs : List Game.Output) : Bytes :=
  encodeOutputs count (outputCodec amount (lengthPrefixedBytesCodec count)) outputs

theorem sourceShapedOutputs_injective_on (count amount : PrefixCodec Nat)
    {left right : List Game.Output}
    (leftCount : count.valid left.length)
    (rightCount : count.valid right.length)
    (leftValues : ∀ out ∈ left,
      amount.valid out.value ∧ count.valid out.script.length)
    (rightValues : ∀ out ∈ right,
      amount.valid out.value ∧ count.valid out.script.length)
    (equal : sourceShapedOutputs count amount left =
      sourceShapedOutputs count amount right) : left = right := by
  exact encodeOutputs_injective_on count
    (outputCodec amount (lengthPrefixedBytesCodec count))
    leftCount rightCount leftValues rightValues equal

end QSB.OutputCodec
