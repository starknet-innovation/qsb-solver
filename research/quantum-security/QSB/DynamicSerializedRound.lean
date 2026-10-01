import QSB.DynamicBonusIndices
import QSB.CoreGetOp
import QSB.CorePushSerialize

/-!
Serialization bridge for the parameterized Config A final round. The first
302 instructions are arbitrary second-round commitment values, the fixed
dummy signatures, an empty multisig dummy, and a nonce signature. The
remaining chunks are the generated selection/puzzle/multisig suffix.

This proves facts about the Lean serialization and parser models. Equality
with every actual Python builder output, and refinement from compiled Bitcoin
Core, remain external obligations.
-/
namespace QSB.DynamicSerializedRound
open ByteMachine
open EncodedScript
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def dataValues (nonce : Bytes) (commitmentAt : Fin 150 → Bytes) : List Bytes :=
  DynamicFinalInit.commitmentPushes commitmentAt ++
    PoolRollInvariant.finalDummyPushes ++ [[], nonce]

def chunks (nonce : Bytes) (commitmentAt : Fin 150 → Bytes) : List Bytes :=
  (dataValues nonce commitmentAt).map CorePushSerialize.pushPattern ++
    EncodedLayout.chunks.drop 749

def script (nonce : Bytes) (commitmentAt : Fin 150 → Bytes) : Bytes :=
  (chunks nonce commitmentAt).flatten

theorem dataValues_length (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) :
    (dataValues nonce commitmentAt).length = 302 := by
  simpa [dataValues, DynamicFinalInit.dataOps] using
    DynamicFinalInit.dataOps_length nonce commitmentAt

theorem dataValues_map (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) :
    (dataValues nonce commitmentAt).map Op.push =
      DynamicFinalInit.dataOps nonce commitmentAt := rfl

theorem dataValue_short (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    ∀ value ∈ dataValues nonce commitmentAt, value.length < 76 := by
  intro value present
  change value ∈ DynamicFinalInit.commitmentPushes commitmentAt ++
    PoolRollInvariant.finalDummyPushes ++ [[], nonce] at present
  rcases List.mem_append.mp present with prior | tail
  · rcases List.mem_append.mp prior with commitment | dummy
    · obtain ⟨i, rfl⟩ : ∃ i : Fin 150, commitmentAt i = value := by
        simpa [DynamicFinalInit.commitmentPushes,
          DynamicFinalInit.commitmentPool] using commitment
      simp [width]
    · have widths := FinalSignedBoundary.generated_dummy_pool_width
      have hd : value ∈ PoolRollInvariant.finalDummyPool := by
        simpa [PoolRollInvariant.finalDummyPool] using dummy
      have w := widths value hd
      omega
  · simp only [List.mem_cons] at tail
    rcases tail with empty | rest
    · simp [empty]
    · have nonceEq : value = nonce := by simpa using rest
      subst value
      exact nonceShort

theorem short_push_decodes (value : Bytes) (short : value.length < 76) :
    decodeChunk (CorePushSerialize.pushPattern value) = some (.push value) := by
  rw [CorePushSerialize.pushPattern_direct value short]
  cases value with
  | nil => decide
  | cons b rest =>
      have small : rest.length + 1 < 76 := by simpa using short
      have sizeLess : rest.length + 1 < 256 := by omega
      simp [decodeChunk, ScriptCodeSelection.directPushPattern,
        Nat.mod_eq_of_lt sizeLess]
      omega

theorem short_push_simple (value : Bytes) (short : value.length < 76) :
    FindAndDelete.simpleChunk (CorePushSerialize.pushPattern value) = true := by
  rw [CorePushSerialize.pushPattern_direct value short]
  cases value with
  | nil => decide
  | cons b rest =>
      have small : rest.length + 1 < 76 := by simpa using short
      have sizeLess : rest.length + 1 < 256 := by omega
      simp [FindAndDelete.simpleChunk,
        ScriptCodeSelection.directPushPattern, Nat.mod_eq_of_lt sizeLess]
      omega

theorem chunks_decode (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    (chunks nonce commitmentAt).map decodeChunk =
      (DynamicFinalInit.finalRoundProgram nonce commitmentAt).map some := by
  have dataDecode :
      ((dataValues nonce commitmentAt).map CorePushSerialize.pushPattern).map
        decodeChunk = ((dataValues nonce commitmentAt).map Op.push).map some := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro value present
    exact short_push_decodes value
      (dataValue_short nonce commitmentAt width nonceShort value present)
  have suffixDecode :
      (EncodedLayout.chunks.drop 749).map decodeChunk =
        (ByteLayout.program.drop 749).map some := by
    simpa using
      congrArg (List.drop 749) EncodedScript.literal_chunks_decode
  simp [chunks, DynamicFinalInit.finalRoundProgram,
    ← dataValues_map, dataDecode, suffixDecode]

theorem chunks_simple (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    ∀ chunk ∈ chunks nonce commitmentAt,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  rcases List.mem_append.mp present with data | suffix
  · obtain ⟨value, hValue, rfl⟩ := List.mem_map.mp data
    exact short_push_simple value
      (dataValue_short nonce commitmentAt width nonceShort value hValue)
  · exact List.all_eq_true.mp
      FindAndDelete.literal_simple_chunks chunk
        (List.mem_of_mem_drop suffix)

theorem parse_simple_chunks (xs : List Bytes)
    (simple : ∀ x ∈ xs, FindAndDelete.simpleChunk x = true) :
    parseChunks xs.length xs.flatten = some xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      have headSimple := simple head (List.mem_cons_self ..)
      have tailSimple : ∀ x ∈ tail,
          FindAndDelete.simpleChunk x = true := by
        intro x hx
        exact simple x (List.mem_cons_of_mem _ hx)
      have headParse := FindAndDelete.simple_chunk_stable head headSimple
        tail.flatten
      have nonempty : head ≠ [] := by
        intro empty
        simp [empty, FindAndDelete.simpleChunk] at headSimple
      cases head with
      | nil => contradiction
      | cons op payload =>
          change (parseOne ((op :: payload) ++ tail.flatten)).bind
            (fun p => (parseChunks tail.length p.2).bind
              (fun xs => some (p.1 :: xs))) =
              some ((op :: payload) :: tail)
          rw [headParse]
          simp [ih tailSimple]

theorem serialized_final_round_parses (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    parseChunks (chunks nonce commitmentAt).length
      (script nonce commitmentAt) = some (chunks nonce commitmentAt) := by
  exact parse_simple_chunks _ (chunks_simple nonce commitmentAt width nonceShort)

/-- Parse serialized bytes into opcodes using the source-shaped GetOp
segmentation and chunk decoder. The fuel is an opcode count, not a byte count. -/
def parseOps (fuel : Nat) (wire : Bytes) : Option (List Op) := do
  let parsed ← parseChunks fuel wire
  parsed.mapM decodeChunk

/-- The same complete-chunk parser with the separately written, Core-shaped
GetOp iterator-width step. -/
def parseCoreChunks : Nat → Bytes → Option (List Bytes)
  | 0, [] => some []
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, wire => do
      let (chunk, rest) ← CoreGetOp.parse wire
      let later ← parseCoreChunks fuel rest
      some (chunk :: later)

theorem parseCoreChunks_eq_parseChunks (fuel : Nat) (wire : Bytes) :
    parseCoreChunks fuel wire = parseChunks fuel wire := by
  induction fuel generalizing wire with
  | zero =>
      cases wire <;> rfl
  | succ fuel ih =>
      cases wire with
      | nil => rfl
      | cons op rest =>
          simp only [parseCoreChunks, parseChunks,
            CoreGetOp.parse_eq_parseOne]
          cases parsed : parseOne (op :: rest) with
          | none => simp
          | some pair =>
              simp [ih]

def parseCoreOps (fuel : Nat) (wire : Bytes) : Option (List Op) := do
  let parsed ← parseCoreChunks fuel wire
  parsed.mapM decodeChunk

theorem parseCoreOps_eq_parseOps (fuel : Nat) (wire : Bytes) :
    parseCoreOps fuel wire = parseOps fuel wire := by
  simp [parseCoreOps, parseOps, parseCoreChunks_eq_parseChunks]

private theorem mapM_of_map_some (xs : List Bytes) (ops : List Op)
    (aligned : xs.map decodeChunk = ops.map some) :
    xs.mapM decodeChunk = some ops := by
  induction xs generalizing ops with
  | nil =>
      cases ops with
      | nil => rfl
      | cons op rest => simp at aligned
  | cons x rest ih =>
      cases ops with
      | nil => simp at aligned
      | cons op tail =>
          have head : decodeChunk x = some op := by
            exact (List.cons.inj aligned).1
          have restAligned : rest.map decodeChunk = tail.map some :=
            (List.cons.inj aligned).2
          simp [head, ih tail restAligned]

/-- The parameterized final-round bytes have a single parsed opcode program:
exactly the one used by the dynamic nine-position extraction theorem. This is
universal over supplied commitment values and short nonce bytes, but not over
the Python builder or compiled Core. -/
theorem serialized_final_round_decodes (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    parseOps (chunks nonce commitmentAt).length
      (script nonce commitmentAt) =
        some (DynamicFinalInit.finalRoundProgram nonce commitmentAt) := by
  simp only [parseOps, serialized_final_round_parses nonce commitmentAt
    width nonceShort]
  exact mapM_of_map_some _ _
    (chunks_decode nonce commitmentAt width nonceShort)

theorem serialized_final_round_core_decodes (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (nonceShort : nonce.length < 76) :
    parseCoreOps (chunks nonce commitmentAt).length
      (script nonce commitmentAt) =
        some (DynamicFinalInit.finalRoundProgram nonce commitmentAt) := by
  rw [parseCoreOps_eq_parseOps]
  exact serialized_final_round_decodes nonce commitmentAt width nonceShort

end QSB.DynamicSerializedRound
