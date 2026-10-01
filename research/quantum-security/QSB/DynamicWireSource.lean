import QSB.DynamicSerializedRound
import QSB.DynamicWholeSource

/-!
A full serialized source-shaped lock can be split into any well-formed prefix,
one first-round CHECKMULTISIG opcode, and the parameterized final segment.
The source-shaped Core GetOp parser then yields the exact opcode list consumed
by the arbitrary-prefix nine-position theorem. Actual Python-builder equality
and compiled Bitcoin Core acceptance remain separate obligations.
-/
namespace QSB.DynamicWireSource
open ByteMachine
open EncodedScript

def fullChunks (priorChunks : List Bytes) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Bytes :=
  priorChunks ++ [[0xae]] ++
    DynamicSerializedRound.chunks nonce commitmentAt

def fullWire (priorChunks : List Bytes) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : Bytes :=
  (fullChunks priorChunks nonce commitmentAt).flatten

theorem full_chunks_simple (priorChunks : List Bytes) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (priorSimple : ∀ chunk ∈ priorChunks,
      FindAndDelete.simpleChunk chunk = true)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    ∀ chunk ∈ fullChunks priorChunks nonce commitmentAt,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  simp only [fullChunks, List.mem_append, List.mem_singleton] at present
  rcases present with first | final
  · rcases first with prior | firstCheck
    · exact priorSimple chunk prior
    · subst chunk
      decide
  · exact DynamicSerializedRound.chunks_simple nonce commitmentAt
      width nonceShort chunk final

theorem full_chunks_decode (priorChunks : List Bytes)
    (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (priorDecoded : priorChunks.map decodeChunk = priorOps.map some)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    (fullChunks priorChunks nonce commitmentAt).map decodeChunk =
      (DynamicWholeSource.fullProgram priorOps nonce commitmentAt).map some := by
  unfold fullChunks DynamicWholeSource.fullProgram
  simp only [List.map_append]
  rw [priorDecoded,
    DynamicSerializedRound.chunks_decode nonce commitmentAt width nonceShort]
  have firstCheck : ([[0xae]] : List Bytes).map decodeChunk =
      ([.checkmultisig] : List Op).map some := by decide
  rw [firstCheck]

/-- Parsing the complete serialized source-shaped lock, including an
arbitrary simple-chunk prefix, yields the full opcode program used by the
dynamic extraction theorem. -/
theorem full_wire_decodes (priorChunks : List Bytes)
    (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (priorSimple : ∀ chunk ∈ priorChunks,
      FindAndDelete.simpleChunk chunk = true)
    (priorDecoded : priorChunks.map decodeChunk = priorOps.map some)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    DynamicSerializedRound.parseCoreOps
      (fullChunks priorChunks nonce commitmentAt).length
      (fullWire priorChunks nonce commitmentAt) =
        some (DynamicWholeSource.fullProgram priorOps nonce commitmentAt) := by
  rw [DynamicSerializedRound.parseCoreOps_eq_parseOps]
  simp only [DynamicSerializedRound.parseOps, fullWire,
    DynamicSerializedRound.parse_simple_chunks _
      (full_chunks_simple priorChunks nonce commitmentAt
        priorSimple width nonceShort)]
  exact DynamicSerializedRound.mapM_of_map_some _ _
    (full_chunks_decode priorChunks priorOps nonce commitmentAt
      priorDecoded width nonceShort)

/-- A successful source-shaped execution of the opcodes parsed from this
full serialized wire lock yields the nine-position result on a good setup.
The source evaluator, hash functions, and compiled-Core correspondence are
still explicit premises; this theorem does not assert consensus acceptance. -/
theorem accepted_wire_good_setup_nine_positions (hashes : Hashes)
    (priorChunks : List Bytes) (priorOps : List Op) (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (priorSimple : ∀ chunk ∈ priorChunks,
      FindAndDelete.simpleChunk chunk = true)
    (priorDecoded : priorChunks.map decodeChunk = priorOps.map some)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76)
    (initial final : State) (parsedOps : List Op)
    (parsed : DynamicSerializedRound.parseCoreOps
      (fullChunks priorChunks nonce commitmentAt).length
      (fullWire priorChunks nonce commitmentAt) = some parsedOps)
    (accepted : run hashes parsedOps initial = some final)
    (checker : Bytes → Bytes → Bytes → Bool)
    (sourceEval : ∀ beforeCheck : State,
      run hashes (DynamicWholeSource.beforeFinalCheckProgram
        priorOps nonce commitmentAt) initial = some beforeCheck →
      CoreMultisigEval.finalTenEval
        (fullWire priorChunks nonce commitmentAt) checker
        beforeCheck.stack = some true)
    (noCommitmentDER : ∀ id : Fin 150,
      DERSyntax.valid (commitmentAt id) = false) :
    ∃ (trace : List (Fin 150 × Bytes)) (a b : Fin 150),
      trace.length = 7 ∧
      (∀ p ∈ trace, hashes.h160 p.2 = commitmentAt p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      (a :: b :: trace.map Prod.fst).toFinset.card = 9 := by
  have identity := full_wire_decodes priorChunks priorOps nonce
    commitmentAt priorSimple priorDecoded width nonceShort
  have opsEq : parsedOps =
      DynamicWholeSource.fullProgram priorOps nonce commitmentAt :=
    Option.some.inj (parsed.symm.trans identity)
  subst parsedOps
  exact DynamicWholeSource.accepted_whole_good_setup_nine_positions
    hashes priorOps nonce commitmentAt width initial final accepted
    (fullWire priorChunks nonce commitmentAt) checker sourceEval
    noCommitmentDER

end QSB.DynamicWireSource
