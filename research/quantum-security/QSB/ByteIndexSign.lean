import QSB.FirstNegativeRange

namespace QSB.ByteIndexSign
open ByteMachine

theorem negative_encoding_has_sign_bit (value : Int) (bytes : Bytes)
    (negative : value < 0)
    (encoded : ByteIndex.encodeScriptNum value = some bytes) :
    128 ≤ (bytes.getLast?.getD 0).toNat := by
  unfold ByteIndex.encodeScriptNum at encoded
  have nonzero : value ≠ 0 := by omega
  simp [negative, nonzero] at encoded
  split_ifs at encoded with hhigh
  · rcases encoded with ⟨_, h⟩
    injection h with h
    subst bytes
    simp
  · rcases encoded with ⟨_, h⟩
    injection h with h
    subst bytes
    simp
    omega

theorem parse_sign_bit_nonpositive (bytes : Bytes) (value : Int)
    (short : bytes.length ≤ 4)
    (sign : 128 ≤ (bytes.getLast?.getD 0).toNat)
    (parsed : ByteIndex.parseScriptNum bytes = some value) :
    value ≤ 0 := by
  unfold ByteIndex.parseScriptNum at parsed
  have within : ¬ bytes.length > 4 := by omega
  simp [within, sign] at parsed
  subst value
  omega

theorem parsed_bytes_are_short (bytes : Bytes) (value : Int)
    (parsed : ByteIndex.parseScriptNum bytes = some value) :
    bytes.length ≤ 4 := by
  unfold ByteIndex.parseScriptNum at parsed
  by_contra tooLong
  have exceeded : bytes.length > 4 := by omega
  simp [exceeded] at parsed

theorem negative_encoding_never_parses_positive (value : Int) (bytes : Bytes)
    (negative : value < 0)
    (encoded : ByteIndex.encodeScriptNum value = some bytes)
    (parsedValue : Int)
    (parsed : ByteIndex.parseScriptNum bytes = some parsedValue) :
    parsedValue ≤ 0 := by
  have short : bytes.length ≤ 4 := by
    exact parsed_bytes_are_short bytes parsedValue parsed
  exact parse_sign_bit_nonpositive bytes parsedValue short
    (negative_encoding_has_sign_bit value bytes negative encoded) parsed

theorem encoded_below_152_parses_below_152
    (source parsedValue : Int) (bytes : Bytes)
    (bounded : source ≤ 151)
    (encoded : ByteIndex.encodeScriptNum source = some bytes)
    (parsed : ByteIndex.parseScriptNum bytes = some parsedValue) :
    parsedValue ≤ 151 := by
  by_cases negative : source < 0
  · have nonpositive := negative_encoding_never_parses_positive
      source bytes negative encoded parsedValue parsed
    omega
  · let n : Fin 152 := ⟨source.toNat, by omega⟩
    have value_eq : source = Int.ofNat n.val := by
      dsimp [n]
      omega
    have roundtrip := FirstNumericRange.canonical_index_roundtrip n
    rw [← value_eq, encoded] at roundtrip
    simp [parsed] at roundtrip
    omega

end QSB.ByteIndexSign
