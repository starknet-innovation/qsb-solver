import QSB.CausalQueryAlgorithm

/-!
The explicit H-oracle calls of one source-shaped legacy signature digest.
For a present preimage the inner SHA256 result selects the outer query input.
An absent selected input makes `legacyDigest` fail without querying H; the
out-of-range SINGLE case returns Core's constant digest without querying H.

The trace covers `JointSourceChecks.legacyDigest` only. It does not include
queries made by a caller's key parser, ECDSA function, script interpreter,
scriptSig, setup, or adversary, and it is not a compiled-Core trace.
-/
namespace QSB.JointLegacyDigestQueries
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- Ordered H calls made by one source-shaped legacy digest. -/
def trace (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat) : List Query :=
  if selected ≥ tx.inputs.length then []
  else
    match LegacySighashWire.sourcePreimage tx selected scriptCode hashType with
    | none => []
    | some preimage => [.H preimage, .H (functions.H preimage)]

theorem trace_invalid_input (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat)
    (invalid : tx.inputs.length ≤ selected) :
    trace functions tx selected scriptCode hashType = [] := by
  simp [trace, invalid]

theorem trace_missing_preimage (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat)
    (inputValid : selected < tx.inputs.length)
    (missing : LegacySighashWire.sourcePreimage tx selected scriptCode
      hashType = none) :
    trace functions tx selected scriptCode hashType = [] := by
  simp [trace, Nat.not_le.mpr inputValid, missing]

/-- Core's out-of-range SINGLE digest is a constant, so it makes no H call. -/
theorem trace_single_bug (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat)
    (inputValid : selected < tx.inputs.length)
    (single : LegacySighashWire.baseType hashType = 3)
    (outputMissing : tx.outputs.length ≤ selected) :
    trace functions tx selected scriptCode hashType = [] :=
  trace_missing_preimage functions tx selected scriptCode hashType
    inputValid (LegacySighashWire.single_out_of_range tx selected
      scriptCode hashType inputValid single outputMissing)

theorem trace_present_preimage (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat) (preimage : Bytes)
    (inputValid : selected < tx.inputs.length)
    (present : LegacySighashWire.sourcePreimage tx selected scriptCode
      hashType = some preimage) :
    trace functions tx selected scriptCode hashType =
      [.H preimage, .H (functions.H preimage)] := by
  simp [trace, Nat.not_le.mpr inputValid, present]

/-- A digest makes no more than two explicit H calls and no R calls. -/
theorem trace_length_le_two (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat) :
    (trace functions tx selected scriptCode hashType).length ≤ 2 := by
  by_cases inputValid : selected < tx.inputs.length
  · cases present : LegacySighashWire.sourcePreimage tx selected
        scriptCode hashType with
    | none => simp [trace_missing_preimage functions tx selected
        scriptCode hashType inputValid present]
    | some preimage => simp [trace_present_preimage functions tx selected
        scriptCode hashType preimage inputValid present]
  · exact (trace_invalid_input functions tx selected scriptCode hashType
      (Nat.le_of_not_gt inputValid)).symm ▸ (by decide)

/-- The legacy digest is determined by H at the ordered queries in its
own trace. The second query input is the first response, so agreement on the
first query aligns the second query across the two worlds. -/
theorem legacyDigest_congr (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat)
    (agree : ∀ q ∈ trace functions tx selected scriptCode hashType,
      answer functions' q = answer functions q) :
    JointSourceChecks.legacyDigest functions' tx selected scriptCode hashType =
      JointSourceChecks.legacyDigest functions tx selected scriptCode hashType := by
  by_cases inputValid : selected < tx.inputs.length
  · have notInvalid : ¬ selected ≥ tx.inputs.length :=
      Nat.not_le.mpr inputValid
    cases present : LegacySighashWire.sourcePreimage tx selected
        scriptCode hashType with
    | none =>
        simp [JointSourceChecks.legacyDigest, notInvalid, present]
    | some preimage =>
        have first : functions'.H preimage = functions.H preimage :=
          agree (.H preimage) (by
            simp [trace_present_preimage functions tx selected
              scriptCode hashType preimage inputValid present])
        have second :
            functions'.H (functions.H preimage) =
              functions.H (functions.H preimage) :=
          agree (.H (functions.H preimage)) (by
            simp [trace_present_preimage functions tx selected
              scriptCode hashType preimage inputValid present])
        simp [JointSourceChecks.legacyDigest, notInvalid, present,
          first, second]
  · have invalid : selected ≥ tx.inputs.length :=
      Nat.le_of_not_gt inputValid
    simp [JointSourceChecks.legacyDigest, invalid]

/-- Under the same query agreement, the adaptive trace itself is unchanged. -/
theorem trace_congr (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (scriptCode : Bytes) (hashType : Nat)
    (agree : ∀ q ∈ trace functions tx selected scriptCode hashType,
      answer functions' q = answer functions q) :
    trace functions' tx selected scriptCode hashType =
      trace functions tx selected scriptCode hashType := by
  by_cases inputValid : selected < tx.inputs.length
  · cases present : LegacySighashWire.sourcePreimage tx selected
        scriptCode hashType with
    | none =>
        rw [trace_missing_preimage functions' tx selected scriptCode
          hashType inputValid present,
          trace_missing_preimage functions tx selected scriptCode
          hashType inputValid present]
    | some preimage =>
        have first : functions'.H preimage = functions.H preimage :=
          agree (.H preimage) (by
            simp [trace_present_preimage functions tx selected
              scriptCode hashType preimage inputValid present])
        rw [trace_present_preimage functions' tx selected scriptCode
          hashType preimage inputValid present,
          trace_present_preimage functions tx selected scriptCode
          hashType preimage inputValid present, first]
  · have invalid : tx.inputs.length ≤ selected :=
      Nat.le_of_not_gt inputValid
    rw [trace_invalid_input functions' tx selected scriptCode hashType invalid,
      trace_invalid_input functions tx selected scriptCode hashType invalid]

end QSB.JointLegacyDigestQueries
