import QSB.DynamicFullSerialized

/-!
The complete parameterized Config A serializer remains below Core's 10,000
byte legacy-script limit when its three fixed signatures use short direct
pushes and both commitment pools contain 20-byte values. This is a property
of the Lean serializer; universal Python-builder and compiled-Core refinement
remain separate obligations.
-/
namespace QSB.DynamicScriptLimits
open ByteMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem short_push_length (value : Bytes) (short : value.length < 76) :
    (CorePushSerialize.pushPattern value).length = value.length + 1 := by
  simp [CorePushSerialize.pushPattern, short]

theorem fixed_width_pushes_length (values : List Bytes) (n : Nat)
    (width : ∀ value ∈ values, value.length = n)
    (short : n < 76) :
    ((values.map CorePushSerialize.pushPattern).flatten).length =
      (n + 1) * values.length := by
  rw [List.length_flatten]
  simp only [List.map_map, Function.comp_def]
  have mapped : values.map
      (fun value => (CorePushSerialize.pushPattern value).length) =
      values.map (fun _ => n + 1) := by
    apply List.map_congr_left
    intro value present
    rw [short_push_length value (by rw [width value present]; exact short),
      width value present]
  rw [mapped, List.map_const', List.sum_const_nat]
  exact Nat.mul_comm _ _

theorem commitment_pushes_length (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20) :
    (((DynamicFinalInit.commitmentPushes commitmentAt).map
      CorePushSerialize.pushPattern).flatten).length = 3150 := by
  have widths : ∀ value ∈ DynamicFinalInit.commitmentPushes commitmentAt,
      value.length = 20 := by
    intro value present
    have inPool : value ∈ (List.finRange 150).map commitmentAt := by
      simpa [DynamicFinalInit.commitmentPushes,
        DynamicFinalInit.commitmentPool] using present
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp inPool
    exact width i
  rw [fixed_width_pushes_length _ 20 widths (by decide)]
  simp [DynamicFinalInit.commitmentPushes,
    DynamicFinalInit.commitmentPool]

theorem full_wire_length (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76) :
    (DynamicFullSerialized.fullWire pin nonce0 nonce1
      firstCommitment secondCommitment).length =
        9756 + pin.length + nonce0.length + nonce1.length := by
  have firstPool := commitment_pushes_length firstCommitment firstWidth
  have secondPool := commitment_pushes_length secondCommitment secondWidth
  have pinPush := short_push_length pin pinShort
  have nonce0Push := short_push_length nonce0 nonce0Short
  have nonce1Push := short_push_length nonce1 nonce1Short
  have static5 : (DynamicFullSerialized.staticChunks 1 5).flatten.length =
      5 := by decide
  have static151 :
      (DynamicFullSerialized.staticChunks 156 151).flatten.length =
        1501 := by decide
  have static138 :
      (DynamicFullSerialized.staticChunks 308 138).flatten.length =
        228 := by decide
  have finalStatic : (EncodedLayout.chunks.drop 749).flatten.length =
      217 := by decide
  have dummy :
      ((PoolRollInvariant.finalDummyPushes.map
        CorePushSerialize.pushPattern).flatten).length = 1500 := by decide
  have emptyPush : (CorePushSerialize.pushPattern []).length = 1 := by
    decide
  simp only [DynamicFullSerialized.fullWire, DynamicWireSource.fullWire,
    DynamicWireSource.fullChunks, DynamicFullSerialized.priorChunks,
    DynamicFullSerialized.pinChunks,
    DynamicFullSerialized.firstDataChunks,
    DynamicSerializedRound.chunks,
    DynamicSerializedRound.dataValues,
    List.flatten_append, List.length_append,
    List.flatten_cons, List.flatten_nil]
  simp [firstPool, secondPool, pinPush, nonce0Push, nonce1Push,
    static5, static151, static138, finalStatic, dummy, emptyPush,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Core 27.2's BASE-script size guard is strictly satisfied for every
parameterized lock in the direct-push domain. The maximum is 9,981 bytes. -/
theorem full_wire_below_core_limit (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76) :
    (DynamicFullSerialized.fullWire pin nonce0 nonce1
      firstCommitment secondCommitment).length ≤ 9981 ∧
    (DynamicFullSerialized.fullWire pin nonce0 nonce1
      firstCommitment secondCommitment).length < 10000 := by
  rw [full_wire_length pin nonce0 nonce1 firstCommitment
    secondCommitment firstWidth secondWidth pinShort nonce0Short
    nonce1Short]
  omega

end QSB.DynamicScriptLimits
