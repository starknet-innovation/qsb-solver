import QSB.DynamicCoreStructural

/-!
Parameterize the pinning and first-round data pushes as well as the final
round. The unchanged first-round suffix and deterministic dummy pushes come
from the checked literal fixture. This removes the arbitrary-prior-chunk
contract for the Lean serializer; equality with all executions of the pinned
Python builder is a separate source-refinement obligation.
-/
namespace QSB.DynamicFullSerialized
open ByteMachine EncodedScript
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def staticChunks (start count : Nat) : List Bytes :=
  (EncodedLayout.chunks.drop start).take count

def staticOps (start count : Nat) : List Op :=
  (ByteLayout.program.drop start).take count

theorem static_chunks_decode (start count : Nat) :
    (staticChunks start count).map decodeChunk =
      (staticOps start count).map some := by
  simpa [staticChunks, staticOps, List.map_drop, List.map_take] using
    congrArg (fun xs => (xs.drop start).take count)
      EncodedScript.literal_chunks_decode

theorem static_chunks_simple (start count : Nat) :
    ∀ chunk ∈ staticChunks start count,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  exact (List.all_eq_true.mp FindAndDelete.literal_simple_chunks)
    chunk (List.mem_of_mem_drop (List.mem_of_mem_take present))

theorem commitment_pushes_short (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20) :
    ∀ value ∈ DynamicFinalInit.commitmentPushes commitmentAt,
      value.length < 76 := by
  intro value present
  have inPool : value ∈ (List.finRange 150).map commitmentAt := by
    simpa [DynamicFinalInit.commitmentPushes,
      DynamicFinalInit.commitmentPool] using present
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp inPool
  rw [width i]
  omega

theorem commitment_chunks_decode (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20) :
    ((DynamicFinalInit.commitmentPushes commitmentAt).map
      CorePushSerialize.pushPattern).map decodeChunk =
      ((DynamicFinalInit.commitmentPushes commitmentAt).map Op.push).map some := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro value present
  exact DynamicSerializedRound.short_push_decodes value
    (commitment_pushes_short commitmentAt width value present)

theorem commitment_chunks_simple (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20) :
    ∀ chunk ∈ (DynamicFinalInit.commitmentPushes commitmentAt).map
      CorePushSerialize.pushPattern,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  obtain ⟨value, hValue, rfl⟩ := List.mem_map.mp present
  exact DynamicSerializedRound.short_push_simple value
    (commitment_pushes_short commitmentAt width value hValue)

def pinChunks (pin : Bytes) : List Bytes :=
  [CorePushSerialize.pushPattern pin] ++ staticChunks 1 5

def pinOps (pin : Bytes) : List Op :=
  [.push pin] ++ staticOps 1 5

def firstDataChunks (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Bytes :=
  (DynamicFinalInit.commitmentPushes commitmentAt).map
    CorePushSerialize.pushPattern ++
    staticChunks 156 151 ++ [CorePushSerialize.pushPattern nonce]

def firstDataOps (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  (DynamicFinalInit.commitmentPushes commitmentAt).map Op.push ++
    staticOps 156 151 ++ [.push nonce]

def priorChunks (pin nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Bytes :=
  pinChunks pin ++ firstDataChunks nonce commitmentAt ++
    staticChunks 308 138

def priorOps (pin nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  pinOps pin ++ firstDataOps nonce commitmentAt ++
    staticOps 308 138

theorem pin_chunks_decode (pin : Bytes) (short : pin.length < 76) :
    (pinChunks pin).map decodeChunk = (pinOps pin).map some := by
  simp [pinChunks, pinOps,
    DynamicSerializedRound.short_push_decodes pin short,
    static_chunks_decode]

theorem pin_chunks_simple (pin : Bytes) (short : pin.length < 76) :
    ∀ chunk ∈ pinChunks pin, FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  rcases List.mem_append.mp present with first | rest
  · have h : chunk = CorePushSerialize.pushPattern pin := by
      simpa [pinChunks] using first
    subst chunk
    exact DynamicSerializedRound.short_push_simple pin short
  · exact static_chunks_simple 1 5 chunk rest

theorem first_data_chunks_decode (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (short : nonce.length < 76) :
    (firstDataChunks nonce commitmentAt).map decodeChunk =
      (firstDataOps nonce commitmentAt).map some := by
  simp [firstDataChunks, firstDataOps,
    commitment_chunks_decode commitmentAt width,
    static_chunks_decode,
    DynamicSerializedRound.short_push_decodes nonce short]

theorem first_data_chunks_simple (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (short : nonce.length < 76) :
    ∀ chunk ∈ firstDataChunks nonce commitmentAt,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  simp only [firstDataChunks, List.mem_append, List.mem_singleton] at present
  rcases present with first | nonceChunk
  · rcases first with commitment | fixed
    · exact commitment_chunks_simple commitmentAt width chunk commitment
    · exact static_chunks_simple 156 151 chunk fixed
  · subst chunk
    exact DynamicSerializedRound.short_push_simple nonce short

theorem prior_chunks_decode (pin nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (pinShort : pin.length < 76) (nonceShort : nonce.length < 76) :
    (priorChunks pin nonce commitmentAt).map decodeChunk =
      (priorOps pin nonce commitmentAt).map some := by
  simp [priorChunks, priorOps, pin_chunks_decode pin pinShort,
    first_data_chunks_decode nonce commitmentAt width nonceShort,
    static_chunks_decode]

theorem prior_chunks_simple (pin nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (pinShort : pin.length < 76) (nonceShort : nonce.length < 76) :
    ∀ chunk ∈ priorChunks pin nonce commitmentAt,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  simp only [priorChunks, List.mem_append] at present
  rcases present with first | final
  · rcases first with pinChunk | dataChunk
    · exact pin_chunks_simple pin pinShort chunk pinChunk
    · exact first_data_chunks_simple nonce commitmentAt width nonceShort
        chunk dataChunk
  · exact static_chunks_simple 308 138 chunk final

/-- Extract fixture inputs only to check that the slice boundaries above
reconstruct the exact pinned 446-op prefix. General theorems use arbitrary
pin, nonce and commitment bytes, not these disposable values. -/
def literalPin : Bytes :=
  match ByteLayout.program[0]? with
  | some (Op.push value) => value
  | _ => []

def literalFirstNonce : Bytes :=
  match ByteLayout.program[307]? with
  | some (Op.push value) => value
  | _ => []

def literalFirstCommitment (i : Fin 150) : Bytes :=
  match ByteLayout.program[6 + (149 - i.val)]? with
  | some (Op.push value) => value
  | _ => []

theorem literal_prior_chunks :
    priorChunks literalPin literalFirstNonce literalFirstCommitment =
      EncodedLayout.chunks.take 446 := by decide

theorem literal_prior_ops :
    priorOps literalPin literalFirstNonce literalFirstCommitment =
      ByteLayout.program.take 446 := by decide

def fullWire (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes) : Bytes :=
  DynamicWireSource.fullWire (priorChunks pin nonce0 firstCommitment)
    nonce1 secondCommitment

/-- The complete parameterized Lean wire lock parses without an arbitrary
prior-chunk hypothesis. The pin, both nonce signatures, and both commitment
pools may vary; fixed dummy pushes and opcode suffixes remain Config A. -/
theorem full_wire_decodes (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76) :
    DynamicSerializedRound.parseCoreOps
      (DynamicWireSource.fullChunks
        (priorChunks pin nonce0 firstCommitment) nonce1 secondCommitment).length
      (fullWire pin nonce0 nonce1 firstCommitment secondCommitment) =
        some (DynamicWholeSource.fullProgram
          (priorOps pin nonce0 firstCommitment) nonce1 secondCommitment) := by
  exact DynamicWireSource.full_wire_decodes
    (priorChunks pin nonce0 firstCommitment)
    (priorOps pin nonce0 firstCommitment)
    nonce1 secondCommitment
    (prior_chunks_simple pin nonce0 firstCommitment firstWidth
      pinShort nonce0Short)
    (prior_chunks_decode pin nonce0 firstCommitment firstWidth
      pinShort nonce0Short)
    secondWidth nonce1Short

/-- Strict-DER source syntax of the three fixed signatures supplies the
short-push hypotheses of the complete wire parser. -/
theorem full_wire_decodes_der (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinDER : DERSyntax.valid pin = true)
    (nonce0DER : DERSyntax.valid nonce0 = true)
    (nonce1DER : DERSyntax.valid nonce1 = true) :
    DynamicSerializedRound.parseCoreOps
      (DynamicWireSource.fullChunks
        (priorChunks pin nonce0 firstCommitment) nonce1 secondCommitment).length
      (fullWire pin nonce0 nonce1 firstCommitment secondCommitment) =
        some (DynamicWholeSource.fullProgram
          (priorOps pin nonce0 firstCommitment) nonce1 secondCommitment) :=
  full_wire_decodes pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth
    (DERSyntax.valid_direct_push_width pin pinDER)
    (DERSyntax.valid_direct_push_width nonce0 nonce0DER)
    (DERSyntax.valid_direct_push_width nonce1 nonce1DER)

/-- The parameterized whole-lock serialization, rather than arbitrary prior
chunks, is the script evaluated by the bottom-first structural theorem. The
source execution and cryptographic checker remain premises. -/
theorem accepted_full_structural_good_setup_nine_positions
    (hashes : Hashes)
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (initial : State) (sourceFinal : CoreOpcodeStep.State)
    (parsedOps : List Op)
    (parsed : DynamicSerializedRound.parseCoreOps
      (DynamicWireSource.fullChunks
        (priorChunks pin nonce0 firstCommitment) nonce1 secondCommitment).length
      (fullWire pin nonce0 nonce1 firstCommitment secondCommitment) =
        some parsedOps)
    (accepted : CoreStructuralRun.run hashes parsedOps
      (CoreOpcodeStep.ofByte initial) = some sourceFinal)
    (checker : Bytes → Bytes → Bytes → Bool)
    (sourceEval : ∀ beforeCheck : CoreOpcodeStep.State,
      CoreStructuralRun.run hashes
        (DynamicWholeSource.beforeFinalCheckProgram
          (priorOps pin nonce0 firstCommitment) nonce1 secondCommitment)
        (CoreOpcodeStep.ofByte initial) = some beforeCheck →
      CoreMultisigEval.finalTenEval
        (fullWire pin nonce0 nonce1 firstCommitment secondCommitment) checker
        beforeCheck.stack.reverse = some true)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (secondCommitment id) = false) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      DynamicWholeSource.extractTrace hashes
        (priorOps pin nonce0 firstCommitment) initial = some trace ∧
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = secondCommitment p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  exact DynamicCoreStructural.accepted_structural_wire_good_setup_nine_positions
    hashes (priorChunks pin nonce0 firstCommitment)
    (priorOps pin nonce0 firstCommitment) nonce1 secondCommitment
    (prior_chunks_simple pin nonce0 firstCommitment firstWidth
      pinShort nonce0Short)
    (prior_chunks_decode pin nonce0 firstCommitment firstWidth
      pinShort nonce0Short)
    secondWidth nonce1Short initial sourceFinal parsedOps parsed accepted
    checker sourceEval noCommitmentDER

end QSB.DynamicFullSerialized
