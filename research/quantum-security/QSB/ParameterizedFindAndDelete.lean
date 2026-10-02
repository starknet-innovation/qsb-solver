import QSB.DynamicFullSerialized
import QSB.CorePushFindAndDelete
import QSB.CoreMultisigSourceScan

/-!
The parameterized Config A serializer still has exactly 880 simple opcode
chunks when both commitment pools are 20-byte values and the three fixed
signatures use short pushes. Consequently the Core-shaped source deletion
loop filters whole chunks for any reached signature bytes. This is stronger
than the earlier literal-fixture result, but compiled C++ refinement remains
outside the theorem.
-/
namespace QSB.ParameterizedFindAndDelete
open ByteMachine
open ScriptCodeSelection
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def chunks (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes) : List Bytes :=
  DynamicWireSource.fullChunks
    (DynamicFullSerialized.priorChunks pin nonce0 firstCommitment)
    nonce1 secondCommitment

theorem chunks_length (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes) :
    (chunks pin nonce0 nonce1 firstCommitment secondCommitment).length =
      880 := by
  have firstStatic :
      (DynamicFullSerialized.staticChunks 1 5).length = 5 := by decide
  have dataStatic :
      (DynamicFullSerialized.staticChunks 156 151).length = 151 := by decide
  have priorStatic :
      (DynamicFullSerialized.staticChunks 308 138).length = 138 := by decide
  have finalStatic : (EncodedLayout.chunks.drop 749).length = 131 := by
    simp [EncodedLayout.chunks_length]
  have dummyLength : PoolRollInvariant.finalDummyPushes.length = 150 := by
    decide
  simp [chunks, DynamicWireSource.fullChunks,
    DynamicFullSerialized.priorChunks,
    DynamicFullSerialized.pinChunks,
    DynamicFullSerialized.firstDataChunks,
    DynamicSerializedRound.chunks,
    DynamicSerializedRound.dataValues,
    DynamicFinalInit.commitmentPushes,
    DynamicFinalInit.commitmentPool,
    firstStatic, dataStatic, priorStatic, finalStatic,
    dummyLength]

/-- With short fixed pushes and 20-byte commitments, every parameterized
opcode chunk has the simple parsing shape needed by the generic deletion
theorem. The commitment byte contents need not be random or DER-free here. -/
theorem chunks_simple (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76) :
    ∀ chunk ∈ chunks pin nonce0 nonce1 firstCommitment secondCommitment,
      FindAndDelete.simpleChunk chunk = true := by
  exact DynamicWireSource.full_chunks_simple
    (DynamicFullSerialized.priorChunks pin nonce0 firstCommitment)
    nonce1 secondCommitment
    (DynamicFullSerialized.prior_chunks_simple pin nonce0
      firstCommitment firstWidth pinShort nonce0Short)
    secondWidth nonce1Short

/-- For every list of reached signature bytes, the source-shaped
FindAndDelete loop on the parameterized lock removes precisely the original
opcode chunks whose bytes equal a Core-serialized signature push. Malformed,
long, or duplicate signatures are included; this theorem does not decide
whether a subsequent multisignature scan accepts them. -/
theorem runMany_eq_chunk_filter (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (sigs : List Bytes) :
    CoreFindAndDelete.runMany 880
      (DynamicFullSerialized.fullWire pin nonce0 nonce1
        firstCommitment secondCommitment)
      (sigs.map CorePushSerialize.pushPattern) =
    stripEncodedChunks (sigs.map CorePushSerialize.pushPattern)
      (chunks pin nonce0 nonce1 firstCommitment secondCommitment) := by
  change CoreFindAndDelete.runMany 880
      (chunks pin nonce0 nonce1 firstCommitment secondCommitment).flatten
      (sigs.map CorePushSerialize.pushPattern) =
    stripEncodedChunks (sigs.map CorePushSerialize.pushPattern)
      (chunks pin nonce0 nonce1 firstCommitment secondCommitment)
  exact CorePushFindAndDelete.simple_many_pushes 880 _
    (chunks_simple pin nonce0 nonce1 firstCommitment secondCommitment
      firstWidth secondWidth pinShort nonce0Short nonce1Short)
    (by rw [chunks_length]) sigs

/-- In particular, the generic ten-signature source scan at an arbitrary
reached stack has this exact chunk-filter result on the parameterized lock.
The stack need not satisfy any final-round source invariant. -/
theorem reached_ten_deleted_script (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (top : List Bytes) :
    CoreMultisigSourceScan.deletedScript
      (DynamicFullSerialized.fullWire pin nonce0 nonce1
        firstCommitment secondCommitment) top 10 10 =
    stripEncodedChunks
      ((CoreMultisigSourceScan.reachedSignatures top 10 10).map
        CorePushSerialize.pushPattern)
      (chunks pin nonce0 nonce1 firstCommitment secondCommitment) := by
  exact runMany_eq_chunk_filter pin nonce0 nonce1
    firstCommitment secondCommitment firstWidth secondWidth
    pinShort nonce0Short nonce1Short
    (CoreMultisigSourceScan.reachedSignatures top 10 10)

end QSB.ParameterizedFindAndDelete
