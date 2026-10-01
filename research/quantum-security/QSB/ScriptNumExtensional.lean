import QSB.CoreNumericOps
import QSB.CoreRoll

/-!
ScriptNum operand *bytes* need not be canonical in a bare legacy script. These
lemmas identify the numeric transitions that depend only on the parsed value,
not on the operand encoding. They quantify over arbitrary stacks and parsed
values; the full generated run still needs the separate source-extraction
argument showing where each witness operand is consumed.
-/
namespace QSB.ScriptNumExtensional
open ByteMachine

/-- The deliberately nonminimal four-byte encoding used by the complete-lock
native differential. Its top byte is zero, so the sign bit is clear. -/
def fourBytePositive (n : Nat) : Bytes :=
  [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256), 0]

theorem four_byte_positive_parses (n : Nat) (small : n < 2 ^ 24) :
    ByteIndex.parseScriptNum (fourBytePositive n) = some (Int.ofNat n) := by
  have value : n % 256 + 256 * ((n / 256) % 256 +
      256 * ((n / 65536) % 256)) = n := by omega
  simp [fourBytePositive, ByteIndex.parseScriptNum,
    ByteIndex.unsignedLE, value]

def fiveBytePositive (n : Nat) : Bytes :=
  fourBytePositive n ++ [0]

theorem five_byte_positive_rejected (n : Nat) :
    ByteIndex.parseScriptNum (fiveBytePositive n) = none := by
  simp [fiveBytePositive, fourBytePositive, ByteIndex.parseScriptNum]

/-- Any two raw roll operands with the same ScriptNum parse have exactly the
same byte-model transition, including both failure and success. -/
theorem roll_step_parse_extensional (hashes : Hashes)
    (raw other : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (same : ByteIndex.parseScriptNum raw =
      ByteIndex.parseScriptNum other) :
    ByteMachine.step hashes .roll ⟨raw :: tail, outcomes, cost⟩ =
      ByteMachine.step hashes .roll ⟨other :: tail, outcomes, cost⟩ := by
  unfold ByteMachine.step
  simp [same]

/-- `OP_MIN` consumes both raw operands and serializes the numerical minimum.
Equivalent parsed values give the same transition, even if either encoding is
nonminimal or negative zero. -/
theorem min_step_parse_extensional (hashes : Hashes)
    (left left' right right' : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (sameLeft : ByteIndex.parseScriptNum left =
      ByteIndex.parseScriptNum left')
    (sameRight : ByteIndex.parseScriptNum right =
      ByteIndex.parseScriptNum right') :
    ByteMachine.step hashes .min
      ⟨left :: right :: tail, outcomes, cost⟩ =
    ByteMachine.step hashes .min
      ⟨left' :: right' :: tail, outcomes, cost⟩ := by
  unfold ByteMachine.step
  simp [sameLeft, sameRight]

/-- `OP_ADD` likewise depends on the parsed pair, not their raw encodings. -/
theorem add_step_parse_extensional (hashes : Hashes)
    (left left' right right' : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (sameLeft : ByteIndex.parseScriptNum left =
      ByteIndex.parseScriptNum left')
    (sameRight : ByteIndex.parseScriptNum right =
      ByteIndex.parseScriptNum right') :
    ByteMachine.step hashes .add
      ⟨left :: right :: tail, outcomes, cost⟩ =
    ByteMachine.step hashes .add
      ⟨left' :: right' :: tail, outcomes, cost⟩ := by
  unfold ByteMachine.step
  simp [sameLeft, sameRight]

/-- The source-shaped bottom-first roll operation has the same raw-operand
extensionality for every underlying byte stack. -/
theorem source_roll_parse_extensional
    (raw other : Bytes) (bottom : List Bytes)
    (same : ByteIndex.parseScriptNum raw =
      ByteIndex.parseScriptNum other) :
    CoreRoll.coreRollWithRaw raw bottom =
      CoreRoll.coreRollWithRaw other bottom := by
  simp [CoreRoll.coreRollWithRaw,
    CoreScriptNum.coreSetVch_eq_parseScriptNum, same]

theorem source_min_parse_extensional
    (left left' right right' : Bytes)
    (sameLeft : ByteIndex.parseScriptNum left =
      ByteIndex.parseScriptNum left')
    (sameRight : ByteIndex.parseScriptNum right =
      ByteIndex.parseScriptNum right') :
    CoreNumericOps.coreMin left right =
      CoreNumericOps.coreMin left' right' := by
  simp [CoreNumericOps.coreMin_eq_model, CoreNumericOps.modelMin,
    sameLeft, sameRight]

theorem source_add_parse_extensional
    (left left' right right' : Bytes)
    (sameLeft : ByteIndex.parseScriptNum left =
      ByteIndex.parseScriptNum left')
    (sameRight : ByteIndex.parseScriptNum right =
      ByteIndex.parseScriptNum right') :
    CoreNumericOps.coreAdd left right =
      CoreNumericOps.coreAdd left' right' := by
  simp [CoreNumericOps.coreAdd_eq_model, CoreNumericOps.modelAdd,
    sameLeft, sameRight]

/-- Once a numeric opcode consumes an encoding, any subsequent modeled
program sees the identical state. This includes post-op stack-limit failure. -/
private theorem run_suffix_of_equal_step (hashes : Hashes) (op : Op)
    (suffix : List Op) (left right : State)
    (equal : ByteMachine.step hashes op left =
      ByteMachine.step hashes op right) :
    ByteMachine.run hashes (op :: suffix) left =
      ByteMachine.run hashes (op :: suffix) right := by
  simp only [ByteMachine.run, equal]

theorem roll_run_parse_extensional (hashes : Hashes)
    (raw other : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (suffix : List Op)
    (same : ByteIndex.parseScriptNum raw =
      ByteIndex.parseScriptNum other) :
    ByteMachine.run hashes (.roll :: suffix)
      ⟨raw :: tail, outcomes, cost⟩ =
    ByteMachine.run hashes (.roll :: suffix)
      ⟨other :: tail, outcomes, cost⟩ :=
  run_suffix_of_equal_step hashes .roll suffix _ _
    (roll_step_parse_extensional hashes raw other tail outcomes cost same)

theorem min_run_parse_extensional (hashes : Hashes)
    (left left' right right' : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (suffix : List Op)
    (sameLeft : ByteIndex.parseScriptNum left =
      ByteIndex.parseScriptNum left')
    (sameRight : ByteIndex.parseScriptNum right =
      ByteIndex.parseScriptNum right') :
    ByteMachine.run hashes (.min :: suffix)
      ⟨left :: right :: tail, outcomes, cost⟩ =
    ByteMachine.run hashes (.min :: suffix)
      ⟨left' :: right' :: tail, outcomes, cost⟩ :=
  run_suffix_of_equal_step hashes .min suffix _ _
    (min_step_parse_extensional hashes left left' right right' tail
      outcomes cost sameLeft sameRight)

theorem add_run_parse_extensional (hashes : Hashes)
    (left left' right right' : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (suffix : List Op)
    (sameLeft : ByteIndex.parseScriptNum left =
      ByteIndex.parseScriptNum left')
    (sameRight : ByteIndex.parseScriptNum right =
      ByteIndex.parseScriptNum right') :
    ByteMachine.run hashes (.add :: suffix)
      ⟨left :: right :: tail, outcomes, cost⟩ =
    ByteMachine.run hashes (.add :: suffix)
      ⟨left' :: right' :: tail, outcomes, cost⟩ :=
  run_suffix_of_equal_step hashes .add suffix _ _
    (add_step_parse_extensional hashes left left' right right' tail
      outcomes cost sameLeft sameRight)

end QSB.ScriptNumExtensional
