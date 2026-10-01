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

/-- The converse of a valid-domain round trip: every successful parse uses
exactly the codec's canonical bytes for its returned value. -/
def DecodeSound {α : Type*} (codec : PrefixCodec α) : Prop :=
  ∀ raw value tail, codec.decode raw = some (value, tail) →
    raw = codec.encode value ++ tail

/-- Fixed-length raw bytes, used for an input's 32-byte previous txid. -/
def fixedBytesCodec (width : Nat) : PrefixCodec Bytes where
  valid := fun payload => payload.length = width
  encode := id
  decode := fun bytes =>
    if width ≤ bytes.length then
      some (bytes.take width, bytes.drop width)
    else
      none
  roundtrip := by
    intro payload valid tail
    simp [valid]

theorem fixedBytesCodec_decodeSound (width : Nat) :
    DecodeSound (fixedBytesCodec width) := by
  intro raw value tail parsed
  have enough : width ≤ raw.length := by
    by_contra short
    simp [fixedBytesCodec, short] at parsed
  have pair : (raw.take width, raw.drop width) = (value, tail) := by
    exact Option.some.inj (by simpa [fixedBytesCodec, enough] using parsed)
  have hValue : raw.take width = value := by
    simpa using congrArg Prod.fst pair
  have hTail : raw.drop width = tail := by
    simpa using congrArg Prod.snd pair
  change raw = value ++ tail
  calc
    raw = raw.take width ++ raw.drop width :=
      (List.take_append_drop width raw).symm
    _ = value ++ tail := by rw [hValue, hTail]

/-- Consecutive self-delimiting fields remain self-delimiting. -/
def productCodec {α β : Type} (first : PrefixCodec α)
    (second : PrefixCodec β) : PrefixCodec (α × β) where
  valid := fun pair => first.valid pair.1 ∧ second.valid pair.2
  encode := fun pair => first.encode pair.1 ++ second.encode pair.2
  decode := fun bytes => do
    let (a, rest) ← first.decode bytes
    let (b, tail) ← second.decode rest
    return ((a, b), tail)
  roundtrip := by
    intro pair valid tail
    cases pair with
    | mk a b =>
      simp [List.append_assoc, first.roundtrip _ valid.1,
        second.roundtrip _ valid.2]

theorem productCodec_decodeSound {α β : Type}
    (first : PrefixCodec α) (second : PrefixCodec β)
    (firstSound : DecodeSound first) (secondSound : DecodeSound second) :
    DecodeSound (productCodec first second) := by
  intro raw value tail parsed
  cases firstEq : first.decode raw with
  | none => simp [productCodec, firstEq] at parsed
  | some firstPair =>
    rcases firstPair with ⟨a, rest⟩
    cases secondEq : second.decode rest with
    | none => simp [productCodec, firstEq, secondEq] at parsed
    | some secondPair =>
      rcases secondPair with ⟨b, after⟩
      have result : ((a, b), after) = (value, tail) := by
        exact Option.some.inj (by
          simpa [productCodec, firstEq, secondEq] using parsed)
      have hValue : (a, b) = value := by
        simpa using congrArg Prod.fst result
      have hTail : after = tail := by
        simpa using congrArg Prod.snd result
      have left := firstSound raw a rest firstEq
      have right := secondSound rest b after secondEq
      rw [← hValue, ← hTail]
      change raw = first.encode a ++ second.encode b ++ after
      rw [left, right, List.append_assoc]

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

theorem lengthPrefixedBytesCodec_decodeSound (count : PrefixCodec Nat)
    (countSound : DecodeSound count) :
    DecodeSound (lengthPrefixedBytesCodec count) := by
  intro raw value tail parsed
  cases countEq : count.decode raw with
  | none => simp [lengthPrefixedBytesCodec, countEq] at parsed
  | some countPair =>
    rcases countPair with ⟨n, rest⟩
    have enough : n ≤ rest.length := by
      by_contra short
      simp [lengthPrefixedBytesCodec, countEq, short] at parsed
    have result : (rest.take n, rest.drop n) = (value, tail) := by
      exact Option.some.inj (by
        simpa [lengthPrefixedBytesCodec, countEq, enough] using parsed)
    have hValue : rest.take n = value := by
      simpa using congrArg Prod.fst result
    have hTail : rest.drop n = tail := by
      simpa using congrArg Prod.snd result
    have hCount : value.length = n := by
      rw [← hValue, List.length_take_of_le enough]
    have hRaw := countSound raw n rest countEq
    change raw = count.encode value.length ++ value ++ tail
    calc
      raw = count.encode n ++ rest := hRaw
      _ = count.encode value.length ++ value ++ tail := by
        rw [hCount, ← hValue, ← hTail,
          List.append_assoc, List.take_append_drop n rest]

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

theorem outputCodec_decodeSound (amount : PrefixCodec Nat)
    (script : PrefixCodec Bytes)
    (amountSound : DecodeSound amount) (scriptSound : DecodeSound script) :
    DecodeSound (outputCodec amount script) := by
  intro raw value tail parsed
  cases amountEq : amount.decode raw with
  | none => simp [outputCodec, amountEq] at parsed
  | some amountPair =>
    rcases amountPair with ⟨n, rest⟩
    cases scriptEq : script.decode rest with
    | none => simp [outputCodec, amountEq, scriptEq] at parsed
    | some scriptPair =>
      rcases scriptPair with ⟨bytes, after⟩
      have result : ({ value := n, script := bytes }, after) =
          (value, tail) := by
        exact Option.some.inj (by
          simpa [outputCodec, amountEq, scriptEq] using parsed)
      have hValue : ({ value := n, script := bytes } : Game.Output) = value := by
        simpa using congrArg Prod.fst result
      have hTail : after = tail := by
        simpa using congrArg Prod.snd result
      have left := amountSound raw n rest amountEq
      have right := scriptSound rest bytes after scriptEq
      rw [← hValue, ← hTail]
      change raw = amount.encode n ++ script.encode bytes ++ after
      rw [left, right, List.append_assoc]

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

theorem decodeItems_sound {α : Type*} (item : PrefixCodec α)
    (itemSound : DecodeSound item) (count : Nat) (raw : Bytes)
    (items : List α) (tail : Bytes)
    (parsed : decodeItems item count raw = some (items, tail)) :
    items.length = count ∧ raw = encodeItems item items ++ tail := by
  induction count generalizing raw items tail with
  | zero =>
      have result : ([], raw) = (items, tail) := by
        exact Option.some.inj (by simpa [decodeItems] using parsed)
      have hItems : ([] : List α) = items := by
        simpa using congrArg Prod.fst result
      have hTail : raw = tail := by
        simpa using congrArg Prod.snd result
      subst items
      simp [encodeItems, hTail]
  | succ n ih =>
      cases itemEq : item.decode raw with
      | none => simp [decodeItems, itemEq] at parsed
      | some firstPair =>
        rcases firstPair with ⟨head, rest⟩
        cases restEq : decodeItems item n rest with
        | none => simp [decodeItems, itemEq, restEq] at parsed
        | some restPair =>
          rcases restPair with ⟨remaining, after⟩
          have result : (head :: remaining, after) = (items, tail) := by
            exact Option.some.inj (by
              simpa [decodeItems, itemEq, restEq] using parsed)
          have hItems : head :: remaining = items := by
            simpa using congrArg Prod.fst result
          have hTail : after = tail := by
            simpa using congrArg Prod.snd result
          obtain ⟨hLength, hRest⟩ := ih rest remaining after restEq
          have hHead := itemSound raw head rest itemEq
          rw [← hItems, ← hTail]
          constructor
          · simp [hLength]
          · simp [encodeItems, hHead, hRest, List.append_assoc]

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

theorem decodeOutputs_sound (count : PrefixCodec Nat)
    (item : PrefixCodec Game.Output)
    (countSound : DecodeSound count) (itemSound : DecodeSound item)
    (raw : Bytes) (outputs : List Game.Output) (tail : Bytes)
    (parsed : decodeOutputs count item raw = some (outputs, tail)) :
    raw = encodeOutputs count item outputs ++ tail := by
  cases countEq : count.decode raw with
  | none => simp [decodeOutputs, countEq] at parsed
  | some countPair =>
    rcases countPair with ⟨n, rest⟩
    have itemsEq : decodeItems item n rest = some (outputs, tail) := by
      simpa [decodeOutputs, countEq] using parsed
    obtain ⟨hLength, hItems⟩ :=
      decodeItems_sound item itemSound n rest outputs tail itemsEq
    have hCount := countSound raw n rest countEq
    unfold encodeOutputs
    calc
      raw = count.encode n ++ rest := hCount
      _ = count.encode outputs.length ++ encodeItems item outputs ++ tail := by
        rw [hLength, hItems, List.append_assoc]

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
