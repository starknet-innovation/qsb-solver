import QSB.FixedWidthOracleEncoding

/-!
An explicit finite register for byte strings whose length is bounded in
advance. A unary length field and a zero-padded payload retain the exact
source bytes. The bound is part of the input type; this construction does not
encode the unbounded `Bytes` domain used by the source oracle interfaces.
-/
namespace QSB.BoundedInputEncoding
open QSB.ByteMachine
open QSB.TaggedOracle

/-- Byte strings of length at most `bound`. -/
abbrev BoundedBytes (bound : Nat) := {bytes : Bytes // bytes.length ≤ bound}

/-- The original length is represented in a finite register. -/
def lengthIndex {bound : Nat} (bytes : BoundedBytes bound) : Fin (bound + 1) :=
  ⟨bytes.1.length, by omega⟩

/-- Pad to exactly `bound` bytes, retaining the original prefix. -/
def pad {bound : Nat} (bytes : BoundedBytes bound) :
    FixedWidthOracleEncoding.FixedBytes bound :=
  ⟨bytes.1 ++ List.replicate (bound - bytes.1.length) 0, by
    simp only [List.length_append, List.length_replicate]
    omega⟩

theorem take_pad {bound : Nat} (bytes : BoundedBytes bound) :
    (pad bytes).1.take bytes.1.length = bytes.1 := by
  simp [pad]

/-- Equal lengths and equal padded payloads imply equal original bytes. -/
theorem equal_of_length_pad {bound : Nat} (left right : BoundedBytes bound)
    (lengthEq : left.1.length = right.1.length)
    (padEq : pad left = pad right) : left = right := by
  apply Subtype.ext
  have same := congrArg (fun bytes : FixedWidthOracleEncoding.FixedBytes bound =>
    bytes.1.take left.1.length) padEq
  change (pad left).1.take left.1.length =
    (pad right).1.take left.1.length at same
  rw [take_pad] at same
  rw [lengthEq, take_pad] at same
  exact same

/-- A one-hot length register. This uses `bound + 1` bits, prioritizing a
simple injectivity proof over a compact binary representation. -/
def lengthBits {bound : Nat} (index : Fin (bound + 1)) :
    Bits (bound + 1) :=
  fun i => decide (i = index)

theorem lengthBits_injective {bound : Nat} :
    Function.Injective (lengthBits (bound := bound)) := by
  intro left right same
  have bit := congrFun same left
  simpa [lengthBits] using bit

/-- The length field and padded payload form a pair of finite bit registers. -/
def encodePair {bound : Nat} (bytes : BoundedBytes bound) :
    Bits (bound + 1) × Bits (bound * 8) :=
  (lengthBits (lengthIndex bytes), FixedWidthOracleEncoding.encode (pad bytes))

theorem encodePair_injective {bound : Nat} :
    Function.Injective (encodePair (bound := bound)) := by
  intro left right same
  have lengthEq : left.1.length = right.1.length := by
    have h := lengthBits_injective (congrArg Prod.fst same)
    exact congrArg Fin.val h
  have padEq : pad left = pad right :=
    FixedWidthOracleEncoding.encode_injective (congrArg Prod.snd same)
  exact equal_of_length_pad left right lengthEq padEq

/-- Concatenate two bit registers using the standard finite sum indexing. -/
def joinBits {leftWidth rightWidth : Nat}
    (left : Bits leftWidth) (right : Bits rightWidth) :
    Bits (leftWidth + rightWidth) :=
  fun i => match (finSumFinEquiv :
      Fin leftWidth ⊕ Fin rightWidth ≃ Fin (leftWidth + rightWidth)).symm i with
    | .inl j => left j
    | .inr j => right j

theorem joinBits_injective {leftWidth rightWidth : Nat} :
    Function.Injective (fun pair : Bits leftWidth × Bits rightWidth =>
      joinBits pair.1 pair.2) := by
  intro left right same
  apply Prod.ext
  · funext i
    have bit := congrFun same
      ((finSumFinEquiv : Fin leftWidth ⊕ Fin rightWidth ≃
        Fin (leftWidth + rightWidth)) (.inl i))
    simpa [joinBits] using bit
  · funext i
    have bit := congrFun same
      ((finSumFinEquiv : Fin leftWidth ⊕ Fin rightWidth ≃
        Fin (leftWidth + rightWidth)) (.inr i))
    simpa [joinBits] using bit

theorem joinBits_pair_eq {leftWidth rightWidth : Nat}
    {leftA leftB : Bits leftWidth} {rightA rightB : Bits rightWidth}
    (same : joinBits leftA rightA = joinBits leftB rightB) :
    (leftA, rightA) = (leftB, rightB) := by
  apply joinBits_injective
  exact same

/-- A single finite bit register: one-hot length followed by padded bytes. -/
def encode {bound : Nat} (bytes : BoundedBytes bound) :
    Bits ((bound + 1) + bound * 8) :=
  joinBits (encodePair bytes).1 (encodePair bytes).2

theorem encode_injective {bound : Nat} :
    Function.Injective (encode (bound := bound)) := by
  intro left right same
  apply encodePair_injective
  apply joinBits_injective
  exact same

/-- A fixed length cap makes the source input domain finite. This instance is
obtained from the proved injection into the explicit bit register. -/
noncomputable instance boundedBytesFintype (bound : Nat) :
    Fintype (BoundedBytes bound) :=
  Fintype.ofInjective (encode (bound := bound))
    (encode_injective (bound := bound))

theorem boundedBytes_card_le (bound : Nat) :
    Nat.card (BoundedBytes bound) ≤
      2 ^ ((bound + 1) + bound * 8) := by
  classical
  calc
    Nat.card (BoundedBytes bound) = Fintype.card (BoundedBytes bound) :=
      Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Bits ((bound + 1) + bound * 8)) :=
      Fintype.card_le_of_injective (encode (bound := bound))
        (encode_injective (bound := bound))
    _ = 2 ^ ((bound + 1) + bound * 8) := by
      simpa only [Nat.card_eq_fintype_card] using
        (TaggedOracle.bits_card ((bound + 1) + bound * 8))

/-- Add one explicit tag bit to the bounded byte-input register. The left tag
stands for an H input and the right tag for an R input. -/
def taggedEncode {bound : Nat}
    (input : Sum (BoundedBytes bound) (BoundedBytes bound)) :
    Bits (1 + ((bound + 1) + bound * 8)) :=
  match input with
  | .inl bytes => joinBits (fun _ : Fin 1 => false) (encode bytes)
  | .inr bytes => joinBits (fun _ : Fin 1 => true) (encode bytes)

theorem taggedEncode_injective {bound : Nat} :
    Function.Injective (taggedEncode (bound := bound)) := by
  intro left right same
  cases left with
  | inl leftBytes =>
      cases right with
      | inl rightBytes =>
          simp only [taggedEncode] at same
          have parts := joinBits_pair_eq same
          have payload := congrArg Prod.snd parts
          exact congrArg Sum.inl (encode_injective payload)
      | inr rightBytes =>
          simp only [taggedEncode] at same
          have parts := joinBits_pair_eq same
          have tags := congrArg Prod.fst parts
          have impossible := congrFun tags (⟨0, by decide⟩ : Fin 1)
          cases impossible
  | inr leftBytes =>
      cases right with
      | inl rightBytes =>
          simp only [taggedEncode] at same
          have parts := joinBits_pair_eq same
          have tags := congrArg Prod.fst parts
          have impossible := congrFun tags (⟨0, by decide⟩ : Fin 1)
          cases impossible
      | inr rightBytes =>
          simp only [taggedEncode] at same
          have parts := joinBits_pair_eq same
          have payload := congrArg Prod.snd parts
          exact congrArg Sum.inr (encode_injective payload)

end QSB.BoundedInputEncoding
