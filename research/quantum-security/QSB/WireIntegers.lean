import QSB.OutputCodec
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.NormNum

/-!
Fixed-width little-endian natural-number bytes. Bitcoin writes a nonnegative
output amount as eight little-endian bytes. The codec below proves a
valid-domain prefix round trip; equivalence with Core's signed CAmount writer
and the exact consensus monetary bound remain separate source obligations.
-/
namespace QSB.WireIntegers

open QSB.OutputCodec

def leBytes (width value : Nat) : Bytes :=
  (Nat.digitsAppend 256 width value).map UInt8.ofNat

def readLE (bytes : Bytes) : Nat :=
  Nat.ofDigits 256 (bytes.map UInt8.toNat)

theorem leBytes_length (width value : Nat) (valid : value < 256 ^ width) :
    (leBytes width value).length = width := by
  simpa [leBytes] using Nat.length_digitsAppend (by norm_num : 1 < 256) width valid

theorem readLE_leBytes (width value : Nat) :
    readLE (leBytes width value) = value := by
  have mapped : ((Nat.digitsAppend 256 width value).map UInt8.ofNat).map
      UInt8.toNat = Nat.digitsAppend 256 width value := by
    simp only [List.map_map]
    simpa only [List.map_id] using
      (List.map_congr_left (l := Nat.digitsAppend 256 width value)
        (f := UInt8.toNat ∘ UInt8.ofNat) (g := id) (by
          intro digit member
          exact UInt8.toNat_ofNat_of_lt (by
            simpa [UInt8.size] using
              (Nat.lt_of_mem_digitsAppend (by norm_num : 1 < 256)
                width digit member))))
  change Nat.ofDigits 256
    (((Nat.digitsAppend 256 width value).map UInt8.ofNat).map UInt8.toNat) = value
  rw [mapped]
  rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero]
  exact Nat.ofDigits_digits 256 value

/-- A fixed-width byte string is recovered from its little-endian value.
Together with `readLE_leBytes`, this avoids silently dropping leading zero
bytes when converting 32-byte ECDSA digests to integers and back. -/
theorem leBytes_readLE (bytes : Bytes) (width : Nat)
    (length : bytes.length = width) :
    leBytes width (readLE bytes) = bytes := by
  have digitsValid : (bytes.map UInt8.toNat).length = width ∧
      ∀ digit ∈ bytes.map UInt8.toNat, digit < 256 := by
    constructor
    · simpa using length
    · intro digit member
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
      exact byte.toNat_lt
  have digitsRoundtrip :=
    (Nat.setInvOn_digitsAppend_ofDigits
      (by norm_num : 1 < 256) width).1 digitsValid
  unfold leBytes readLE
  rw [digitsRoundtrip]
  have byteRoundtrip (byte : UInt8) : UInt8.ofNat byte.toNat = byte := by
    apply UInt8.ext
    exact UInt8.toNat_ofNat_of_lt byte.toNat_lt
  simp [Function.comp_def, byteRoundtrip]

theorem readLE_lt (bytes : Bytes) : readLE bytes < 256 ^ bytes.length := by
  unfold readLE
  simpa using Nat.ofDigits_lt_base_pow_length
    (by norm_num : 1 < 256)
    (l := bytes.map UInt8.toNat) (by
      intro digit member
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
      exact byte.toNat_lt)

def beBytes (width value : Nat) : Bytes := (leBytes width value).reverse

def readBE (bytes : Bytes) : Nat := readLE bytes.reverse

theorem readBE_beBytes (width value : Nat) :
    readBE (beBytes width value) = value := by
  simp [readBE, beBytes, readLE_leBytes]

theorem beBytes_readBE (bytes : Bytes) (width : Nat)
    (length : bytes.length = width) :
    beBytes width (readBE bytes) = bytes := by
  simp [beBytes, readBE, leBytes_readLE bytes.reverse width
    (by simpa using length)]

theorem readBE_lt (bytes : Bytes) : readBE bytes < 256 ^ bytes.length := by
  simpa [readBE] using readLE_lt bytes.reverse

/-- Core's out-of-range legacy SINGLE result is `uint256::ONE`: its raw
buffer is 01 followed by 31 zero bytes. Interpreted by the ECDSA scalar
parser as big-endian bytes, that buffer denotes 2^248, not 1. -/
theorem coreSingleBug_rawDigest_readBE :
    readBE ((1 : UInt8) :: List.replicate 31 (0 : UInt8)) = 2 ^ 248 := by
  decide

def fixedLECodec (width : Nat) : PrefixCodec Nat where
  valid := fun value => value < 256 ^ width
  encode := leBytes width
  decode := fun bytes =>
    if width ≤ bytes.length then
      some (readLE (bytes.take width), bytes.drop width)
    else
      none
  roundtrip := by
    intro value valid tail
    have len := leBytes_length width value valid
    simp [leBytes_length width value valid, readLE_leBytes width value]

/-- Every successful fixed-width parse recovers exactly the consumed bytes;
this is the converse direction needed for raw-byte canonicality. -/
theorem fixedLE_decode_sound (width : Nat) (raw : Bytes)
    (value : Nat) (tail : Bytes)
    (parsed : (fixedLECodec width).decode raw = some (value, tail)) :
    value < 256 ^ width ∧ raw = leBytes width value ++ tail := by
  have enough : width ≤ raw.length := by
    by_contra short
    simp [fixedLECodec, short] at parsed
  have pair : (readLE (raw.take width), raw.drop width) =
      (value, tail) := by
    exact Option.some.inj (by simpa [fixedLECodec, enough] using parsed)
  have hValue : readLE (raw.take width) = value := by
    simpa using congrArg Prod.fst pair
  have hTail : raw.drop width = tail := by
    simpa using congrArg Prod.snd pair
  constructor
  · rw [← hValue]
    simpa [List.length_take_of_le enough] using readLE_lt (raw.take width)
  · calc
      raw = raw.take width ++ raw.drop width :=
        (List.take_append_drop width raw).symm
      _ = leBytes width value ++ tail := by
        rw [← hValue, leBytes_readLE (raw.take width) width
          (List.length_take_of_le enough), hTail]

theorem fixedLECodec_decodeSound (width : Nat) :
    DecodeSound (fixedLECodec width) := by
  intro raw value tail parsed
  exact (fixedLE_decode_sound width raw value tail parsed).2

/-- The entire nonnegative signed-64 range has a distinct eight-byte encoding.
Consensus imposes a tighter monetary range; this theorem does not model it. -/
def nonnegativeAmountCodec : PrefixCodec Nat where
  valid := fun value => value < 2 ^ 63
  encode := (fixedLECodec 8).encode
  decode := (fixedLECodec 8).decode
  roundtrip := by
    intro value valid tail
    exact (fixedLECodec 8).roundtrip value (by
      change value < 256 ^ 8
      norm_num at valid ⊢
      omega) tail

theorem nonnegativeAmountCodec_decodeSound :
    DecodeSound nonnegativeAmountCodec := by
  exact fixedLECodec_decodeSound 8

/-- The four canonical CompactSize encoder branches. The valid domain is the
uint64 range; decoding rejects an overlong representation as Core does. -/
def compactSizeEncode (value : Nat) : Bytes :=
  if value < 253 then
    [UInt8.ofNat value]
  else if value < 256 ^ 2 then
    UInt8.ofNat 253 :: leBytes 2 value
  else if value < 256 ^ 4 then
    UInt8.ofNat 254 :: leBytes 4 value
  else
    UInt8.ofNat 255 :: leBytes 8 value

def compactSizeDecode : Bytes → Option (Nat × Bytes)
  | [] => none
  | tag :: rest =>
      if tag.toNat < 253 then
        some (tag.toNat, rest)
      else if tag.toNat = 253 then
        do
          let (value, tail) ← (fixedLECodec 2).decode rest
          if value < 253 then none else some (value, tail)
      else if tag.toNat = 254 then
        do
          let (value, tail) ← (fixedLECodec 4).decode rest
          if value < 256 ^ 2 then none else some (value, tail)
      else
        do
          let (value, tail) ← (fixedLECodec 8).decode rest
          if value < 256 ^ 4 then none else some (value, tail)

theorem compactSize_roundtrip (value : Nat) (valid : value < 256 ^ 8)
    (tail : Bytes) :
    compactSizeDecode (compactSizeEncode value ++ tail) =
      some (value, tail) := by
  by_cases small : value < 253
  · have byte : (UInt8.ofNat value).toNat = value := by
      apply UInt8.toNat_ofNat_of_lt
      change value < 256
      omega
    simp [compactSizeEncode, compactSizeDecode, small, byte]
  · by_cases medium : value < 256 ^ 2
    · simp only [compactSizeEncode, if_neg small, if_pos medium]
      simp [compactSizeDecode]
      have h : (fixedLECodec 2).decode (leBytes 2 value ++ tail) =
          some (value, tail) := (fixedLECodec 2).roundtrip value medium tail
      rw [h]
      simp [small]
    · by_cases large : value < 256 ^ 4
      · simp only [compactSizeEncode, if_neg small, if_neg medium, if_pos large]
        simp [compactSizeDecode]
        have h : (fixedLECodec 4).decode (leBytes 4 value ++ tail) =
            some (value, tail) := (fixedLECodec 4).roundtrip value large tail
        rw [h]
        norm_num at medium
        simp [medium]
      · simp only [compactSizeEncode, if_neg small, if_neg medium, if_neg large]
        simp [compactSizeDecode]
        have h : (fixedLECodec 8).decode (leBytes 8 value ++ tail) =
            some (value, tail) := (fixedLECodec 8).roundtrip value valid tail
        rw [h]
        norm_num at large
        simp [large]

/-- A successful CompactSize parse consumes the unique shortest encoding of
its value. This excludes noncanonical length prefixes in every transaction
field that uses this codec, not just the three boundary examples below. -/
theorem compactSizeDecode_sound (raw : Bytes) (value : Nat) (tail : Bytes)
    (parsed : compactSizeDecode raw = some (value, tail)) :
    value < 256 ^ 8 ∧ raw = compactSizeEncode value ++ tail := by
  cases raw with
  | nil => simp [compactSizeDecode] at parsed
  | cons tag rest =>
    by_cases small : tag.toNat < 253
    · have pair : (tag.toNat, rest) = (value, tail) := by
        exact Option.some.inj (by simpa [compactSizeDecode, small] using parsed)
      have hValue : tag.toNat = value := by
        simpa using congrArg Prod.fst pair
      have hTail : rest = tail := by
        simpa using congrArg Prod.snd pair
      have valueSmall : value < 253 := by omega
      constructor
      · have := tag.toNat_lt
        omega
      · rw [← hValue, hTail]
        simp [compactSizeEncode, small]
    · by_cases tag16 : tag.toNat = 253
      · cases hDecode : (fixedLECodec 2).decode rest with
        | none => simp [compactSizeDecode, tag16, hDecode] at parsed
        | some result =>
          rcases result with ⟨n, after⟩
          by_cases overlong : n < 253
          · simp [compactSizeDecode, tag16, hDecode, overlong] at parsed
          · have pair : (n, after) = (value, tail) := by
              exact Option.some.inj (by
                simpa [compactSizeDecode, small, tag16, hDecode, overlong]
                  using parsed)
            have hValue : n = value := by
              simpa using congrArg Prod.fst pair
            have hTail : after = tail := by
              simpa using congrArg Prod.snd pair
            obtain ⟨upper, consumed⟩ :=
              fixedLE_decode_sound 2 rest n after hDecode
            have tagEq : tag = (253 : UInt8) := by
              apply UInt8.ext
              simpa using tag16
            have valueLower : ¬value < 253 := by omega
            constructor
            · omega
            · rw [tagEq, consumed, ← hValue, ← hTail]
              norm_num at upper
              simp [compactSizeEncode, overlong, upper]
      · by_cases tag32 : tag.toNat = 254
        · cases hDecode : (fixedLECodec 4).decode rest with
          | none => simp [compactSizeDecode, tag32, hDecode] at parsed
          | some result =>
            rcases result with ⟨n, after⟩
            by_cases overlong : n < 256 ^ 2
            · simp [compactSizeDecode, tag32, hDecode] at parsed
              norm_num at overlong
              omega
            · have parsedParts : 65536 ≤ n ∧ n = value ∧ after = tail := by
                simpa [compactSizeDecode, small, tag16, tag32, hDecode]
                  using parsed
              have pair : (n, after) = (value, tail) :=
                Prod.ext parsedParts.2.1 parsedParts.2.2
              have hValue : n = value := by
                simpa using congrArg Prod.fst pair
              have hTail : after = tail := by
                simpa using congrArg Prod.snd pair
              obtain ⟨upper, consumed⟩ :=
                fixedLE_decode_sound 4 rest n after hDecode
              have tagEq : tag = (254 : UInt8) := by
                apply UInt8.ext
                simpa using tag32
              have notSmall : ¬value < 253 := by omega
              have notMedium : ¬value < 256 ^ 2 := by omega
              constructor
              · omega
              · rw [tagEq, consumed, ← hValue, ← hTail]
                norm_num at overlong upper
                have notSmallN : ¬n < 253 := by omega
                have notMediumN : ¬n < 65536 := by omega
                simp [compactSizeEncode, notSmallN, notMediumN, upper]
        · cases hDecode : (fixedLECodec 8).decode rest with
          | none => simp [compactSizeDecode, small, tag16, tag32, hDecode] at parsed
          | some result =>
            rcases result with ⟨n, after⟩
            by_cases overlong : n < 256 ^ 4
            · simp [compactSizeDecode, small, tag16, tag32, hDecode] at parsed
              norm_num at overlong
              omega
            · have parsedParts : 4294967296 ≤ n ∧ n = value ∧ after = tail := by
                simpa [compactSizeDecode, small, tag16, tag32, hDecode]
                  using parsed
              have pair : (n, after) = (value, tail) :=
                Prod.ext parsedParts.2.1 parsedParts.2.2
              have hValue : n = value := by
                simpa using congrArg Prod.fst pair
              have hTail : after = tail := by
                simpa using congrArg Prod.snd pair
              obtain ⟨upper, consumed⟩ :=
                fixedLE_decode_sound 8 rest n after hDecode
              have tagEq : tag = (255 : UInt8) := by
                have tagBound := tag.toNat_lt
                have tagNat : tag.toNat = 255 := by omega
                apply UInt8.ext
                simpa using tagNat
              have notSmall : ¬value < 253 := by omega
              have notMedium : ¬value < 256 ^ 2 := by omega
              have notLarge : ¬value < 256 ^ 4 := by omega
              constructor
              · simpa [← hValue] using upper
              · rw [tagEq, consumed, ← hValue, ← hTail]
                norm_num at overlong
                have notSmallN : ¬n < 253 := by omega
                have notMediumN : ¬n < 65536 := by omega
                have notLargeN : ¬n < 4294967296 := by omega
                simp [compactSizeEncode, notSmallN, notMediumN, notLargeN]

theorem compact_noncanonical_16_rejected (tail : Bytes) :
    compactSizeDecode ([253, 1, 0] ++ tail) = none := by rfl

theorem compact_noncanonical_32_rejected (tail : Bytes) :
    compactSizeDecode ([254, 253, 0, 0, 0] ++ tail) = none := by rfl

def compactSizeCodec : PrefixCodec Nat where
  valid := fun value => value < 256 ^ 8
  encode := compactSizeEncode
  decode := compactSizeDecode
  roundtrip := compactSize_roundtrip

theorem compactSizeCodec_decodeSound : DecodeSound compactSizeCodec := by
  intro raw value tail parsed
  exact (compactSizeDecode_sound raw value tail parsed).2

theorem compact_252 : compactSizeEncode 252 = [252] := by decide
theorem compact_253 : compactSizeEncode 253 = [253, 253, 0] := by decide
theorem compact_65535 : compactSizeEncode 65535 = [253, 255, 255] := by decide
theorem compact_65536 : compactSizeEncode 65536 = [254, 0, 0, 1, 0] := by decide
theorem compact_2pow32 : compactSizeEncode (2 ^ 32) =
    [255, 0, 0, 0, 0, 1, 0, 0, 0] := by decide
theorem amount_90000 : leBytes 8 90000 = [144, 95, 1, 0, 0, 0, 0, 0] := by decide

end QSB.WireIntegers
