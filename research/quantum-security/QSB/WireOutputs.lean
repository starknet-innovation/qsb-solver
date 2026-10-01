import QSB.OutputCodec
import QSB.WireIntegers

/-!
Concrete little-endian and CompactSize byte encoders for the ordered output
segment of a legacy ALL preimage. Lean proves the encoder is injective over
the stated finite wire domain. A separate refinement must identify these
definitions with Core's C++ transaction serialization and establish that
every relevant consensus output is in the domain.
-/
namespace QSB.WireOutputs

open QSB.OutputCodec

def validOutputs (outputs : List Game.Output) : Prop :=
  outputs.length < 256 ^ 8 ∧
    ∀ out ∈ outputs, out.value < 2 ^ 63 ∧ out.script.length < 256 ^ 8

def encode (outputs : List Game.Output) : Bytes :=
  sourceShapedOutputs WireIntegers.compactSizeCodec
    WireIntegers.nonnegativeAmountCodec outputs

def decode (bytes : Bytes) : Option (List Game.Output × Bytes) :=
  decodeOutputs WireIntegers.compactSizeCodec
    (outputCodec WireIntegers.nonnegativeAmountCodec
      (lengthPrefixedBytesCodec WireIntegers.compactSizeCodec)) bytes

theorem decode_encode (outputs : List Game.Output) (tail : Bytes)
    (valid : validOutputs outputs) :
    decode (encode outputs ++ tail) = some (outputs, tail) := by
  exact decodeOutputs_encodeOutputs WireIntegers.compactSizeCodec
    (outputCodec WireIntegers.nonnegativeAmountCodec
      (lengthPrefixedBytesCodec WireIntegers.compactSizeCodec))
    outputs tail valid.1 valid.2

theorem encode_injective_on {left right : List Game.Output}
    (leftValid : validOutputs left) (rightValid : validOutputs right)
    (equal : encode left = encode right) : left = right := by
  exact sourceShapedOutputs_injective_on WireIntegers.compactSizeCodec
    WireIntegers.nonnegativeAmountCodec leftValid.1 rightValid.1
    leftValid.2 rightValid.2 equal

end QSB.WireOutputs
