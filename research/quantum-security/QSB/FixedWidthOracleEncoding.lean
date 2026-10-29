import QSB.TaggedOracle
import QSB.ByteMachine
import QSB.JointSourceChecks

/-!
An explicit, bijective bit-register encoding for fixed-width source-model hash
responses. Each byte contributes eight low-to-high bits, and bytes retain their
original list order. The width premises are part of the input types: arbitrary
byte strings are not silently truncated or padded.

This bridges only idealized response values of width 32 (H) and 20 (R) to the
bit registers used in `TaggedOracle`. The source-model `Functions` interface
supplies these output-width proofs. Arbitrary byte-string query inputs still
need a finite-register encoding, and no coherent quantum oracle is built here.
-/
namespace QSB.FixedWidthOracleEncoding
open QSB.ByteMachine
open QSB.TaggedOracle

/-- A byte string with an exact, checked length. -/
abbrev FixedBytes (n : Nat) := {bytes : Bytes // bytes.length = n}

/-- Bit `i` of one source-model byte, with bit zero least significant. -/
def byteBits (byte : UInt8) : Bits 8 :=
  fun i => byte.toBitVec.getLsb i

theorem byteBits_injective : Function.Injective byteBits := by
  intro left right same
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bit := congrFun same (⟨i, hi⟩ : Fin 8)
  simpa [byteBits, BitVec.getLsb, BitVec.getLsbD] using bit

theorem byteBits_bijective : Function.Bijective byteBits := by
  apply (Fintype.bijective_iff_injective_and_card byteBits).2
  refine ⟨byteBits_injective, ?_⟩
  calc
    Fintype.card UInt8 = FinEnum.card UInt8 :=
      FinEnum.card_eq_fintypeCard.symm
    _ = 2 ^ 8 := FinEnum.card_UInt8
    _ = Fintype.card (Bits 8) := by simp [Bits]

/-- One byte is equivalent to its eight low-to-high bits. -/
noncomputable def byteBitsEquiv : UInt8 ≃ Bits 8 :=
  Equiv.ofBijective byteBits byteBits_bijective

/-- The byte at a position in a fixed-width byte string. -/
def byteAt {n : Nat} (bytes : FixedBytes n) (i : Fin n) : UInt8 :=
  bytes.1.get (Fin.cast bytes.2.symm i)

theorem byteAt_injective {n : Nat} : Function.Injective (byteAt (n := n)) := by
  intro left right same
  apply Subtype.ext
  apply List.ext_get (by rw [left.2, right.2])
  intro i hiLeft hiRight
  let j : Fin n := ⟨i, by simpa [left.2] using hiLeft⟩
  have equalByte := congrFun same j
  simpa [byteAt, j] using equalByte

/-- Exact-length byte lists are tuples of that length. -/
def fixedBytesEquivPi (n : Nat) : FixedBytes n ≃ (Fin n → UInt8) where
  toFun := byteAt
  invFun f := ⟨List.ofFn f, by simp⟩
  left_inv bytes := by
    apply byteAt_injective
    funext i
    simp [byteAt]
  right_inv f := by
    funext i
    simp [byteAt]

/-- The standard product indexing flattens one bit function per byte into
one bit register. -/
def flattenEquiv (n : Nat) : (Fin n → Bits 8) ≃ Bits (n * 8) where
  toFun f i :=
    let pair := (finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n * 8)).symm i
    f pair.1 pair.2
  invFun b i j := b ((finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n * 8)) (i, j))
  left_inv f := by
    funext i j
    simp
  right_inv b := by
    funext i
    change b ((finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n * 8))
      ((finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n * 8)).symm i)) = b i
    rw [Equiv.apply_symm_apply]

/-- Flatten byte positions and low-to-high bit positions into a single bit
register. `finProdFinEquiv` uses index `8 * byteIndex + bitIndex`. -/
def encode {n : Nat} (bytes : FixedBytes n) : Bits (n * 8) :=
  fun i =>
    let pair := (finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n * 8)).symm i
    byteBits (byteAt bytes pair.1) pair.2

theorem encode_injective {n : Nat} : Function.Injective (encode (n := n)) := by
  intro left right same
  apply byteAt_injective
  funext byteIndex
  apply byteBits_injective
  funext bitIndex
  have bit := congrFun same
    ((finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n * 8))
      (byteIndex, bitIndex))
  simpa [encode] using bit

/-- Exact-width byte strings and their flattened bit registers have the
same values, without padding or truncation. The inverse is selected from the
proved byte bijection and is noncomputable; the forward encoding remains the
concrete `encode`. This equivalence supports finite counting, but does not
provide an efficient reversible coherent implementation. -/
noncomputable def encodingEquiv (n : Nat) :
    FixedBytes n ≃ Bits (n * 8) :=
  (fixedBytesEquivPi n).trans
    ((Equiv.piCongrRight fun _ : Fin n => byteBitsEquiv).trans
      (flattenEquiv n))

theorem encodingEquiv_apply {n : Nat} (bytes : FixedBytes n) :
    encodingEquiv n bytes = encode bytes := by
  rfl

theorem encode_bijective {n : Nat} :
    Function.Bijective (encode (n := n)) := by
  simpa only [encodingEquiv_apply] using (encodingEquiv n).bijective

theorem encode_decode {n : Nat} (bits : Bits (n * 8)) :
    encode ((encodingEquiv n).symm bits) = bits := by
  rw [← encodingEquiv_apply]
  exact (encodingEquiv n).apply_symm_apply bits

theorem decode_encode {n : Nat} (bytes : FixedBytes n) :
    (encodingEquiv n).symm (encode bytes) = bytes := by
  rw [← encodingEquiv_apply]
  exact (encodingEquiv n).symm_apply_apply bytes

/-- Exactly 32 bytes encode to the existing H output register. -/
def encodeH (bytes : FixedBytes 32) : Bits 256 := encode bytes

/-- Exactly 20 bytes encode to the existing R output register. -/
def encodeR (bytes : FixedBytes 20) : Bits 160 := encode bytes

theorem encodeH_injective : Function.Injective encodeH :=
  encode_injective (n := 32)

theorem encodeR_injective : Function.Injective encodeR :=
  encode_injective (n := 20)

theorem encodeH_bijective : Function.Bijective encodeH :=
  encode_bijective (n := 32)

theorem encodeR_bijective : Function.Bijective encodeR :=
  encode_bijective (n := 20)

theorem hOutput_card : Nat.card (FixedBytes 32) = 2 ^ 256 := by
  calc
    Nat.card (FixedBytes 32) = Nat.card (Bits 256) :=
      Nat.card_congr (encodingEquiv 32)
    _ = 2 ^ 256 := bits_card 256

theorem rOutput_card : Nat.card (FixedBytes 20) = 2 ^ 160 := by
  calc
    Nat.card (FixedBytes 20) = Nat.card (Bits 160) :=
      Nat.card_congr (encodingEquiv 20)
    _ = 2 ^ 160 := bits_card 160

/-- Encode the actual source-model H output using its declared width. -/
def encodeHValue (functions : JointSourceChecks.Functions) (x : Bytes) :
    Bits 256 :=
  encodeH ⟨functions.H x, functions.H_width x⟩

/-- Encode the actual source-model R output using its declared width. -/
def encodeRValue (functions : JointSourceChecks.Functions) (x : Bytes) :
    Bits 160 :=
  encodeR ⟨functions.R x, functions.R_width x⟩

theorem encodeHValue_eq_iff (functions : JointSourceChecks.Functions)
    (x y : Bytes) :
    encodeHValue functions x = encodeHValue functions y ↔
      functions.H x = functions.H y := by
  constructor
  · intro same
    exact congrArg Subtype.val (encodeH_injective same)
  · intro same
    apply congrArg encodeH
    exact Subtype.ext same

theorem encodeRValue_eq_iff (functions : JointSourceChecks.Functions)
    (x y : Bytes) :
    encodeRValue functions x = encodeRValue functions y ↔
      functions.R x = functions.R y := by
  constructor
  · intro same
    exact congrArg Subtype.val (encodeR_injective same)
  · intro same
    apply congrArg encodeR
    exact Subtype.ext same

end QSB.FixedWidthOracleEncoding
