import QSB.EncodedLayout
import QSB.ScriptCodeSelection

/-!
The generated lock viewed as serialized opcode chunks. Decoding each whole
chunk must recover the existing ByteMachine program. This verifies alignment
of two generated fixtures in Lean; it does not establish equivalence with
Bitcoin Core's C++ GetOp or hash the 9,923 bytes inside Lean.
-/
namespace QSB.EncodedScript
open ByteMachine
open ScriptCodeSelection
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def decodeChunk : Bytes → Option Op
  | [] => none
  | op :: payload =>
      if op == 0x00 && payload == [] then some (.push [])
      else if 1 ≤ op.toNat && op.toNat ≤ 75 && payload.length == op.toNat then
        some (.push payload)
      else if 0x51 ≤ op.toNat && op.toNat ≤ 0x60 && payload == [] then
        some (.push [UInt8.ofNat (op.toNat - 0x50)])
      else if payload == [] then
        match op.toNat with
        | 0x76 => some .dup
        | 0x78 => some .over
        | 0x7c => some .swap
        | 0x7a => some .roll
        | 0xa3 => some .min
        | 0x93 => some .add
        | 0xa9 => some .hash160
        | 0xa8 => some .sha256
        | 0x88 => some .equalverify
        | 0xad => some .checksigverify
        | 0xae => some .checkmultisig
        | _ => none
      else none

/-- Parse one serialized Bitcoin opcode, including PUSHDATA length prefixes.
This is a Lean model of GetOp's byte segmentation; equivalence to the pinned
C++ implementation remains a separate refinement obligation. -/
def consumePush (header rest : Bytes) (size : Nat) : Option (Bytes × Bytes) :=
  if size ≤ rest.length then
    some (header ++ rest.take size, rest.drop size)
  else none

def parseOne : Bytes → Option (Bytes × Bytes)
  | [] => none
  | op :: rest =>
      let n := op.toNat
      if 1 ≤ n && n ≤ 75 then consumePush [op] rest n
      else if n == 0x4c then
        match rest with
        | size :: tail => consumePush [op, size] tail size.toNat
        | _ => none
      else if n == 0x4d then
        match rest with
        | lo :: hi :: tail =>
            consumePush [op, lo, hi] tail (lo.toNat + 256 * hi.toNat)
        | _ => none
      else if n == 0x4e then
        match rest with
        | a :: b :: c :: d :: tail =>
            consumePush [op, a, b, c, d] tail
              (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)
        | _ => none
      else some ([op], rest)

def parseChunks : Nat → Bytes → Option (List Bytes)
  | 0, [] => some []
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, script => do
      let (chunk, rest) ← parseOne script
      let chunks ← parseChunks fuel rest
      some (chunk :: chunks)

/-- All 880 serialized opcode chunks decode to the instructions used in the
arbitrary-stack byte-machine theorems. Both fixtures come from one source
generator, and this theorem checks their internal byte/opcode alignment. -/
theorem literal_chunks_decode :
    EncodedLayout.chunks.map decodeChunk =
      ByteLayout.program.map some := by decide

/-- The 9,923 serialized fixture bytes parse into precisely the generated
880 chunks under the source-shaped GetOp model. -/
theorem literal_parse_chunks :
    parseChunks 880 EncodedLayout.chunks.flatten =
      some EncodedLayout.chunks := by decide

/-- No parsed opcode is OP_CODESEPARATOR (0xab), so legacy scriptCode for the
literal lock starts with the whole locking script before signature deletion. -/
theorem no_code_separator :
    EncodedLayout.chunks.all (fun chunk => chunk.head? != some 0xab) = true := by
  decide

def finalPatterns : List Bytes :=
  (PoolRollInvariant.finalDummyPool ++ [PoolRollInvariant.finalNonce]).map
    directPushPattern

/-- Every selected final signature uses a direct-push opcode. -/
theorem final_patterns_direct :
    (PoolRollInvariant.finalDummyPool ++ [PoolRollInvariant.finalNonce]).all
      (fun sig => sig.length > 0 && sig.length ≤ 75) = true := by decide

/-- No selected pattern collides with another among the 151 literal bytes. -/
theorem final_patterns_nodup : finalPatterns.Nodup := by decide

/-- Every selected final signature has exactly one complete serialized push
in this one generated lock. This is a fixture theorem, not a Core parser
refinement or a statement about arbitrary vault setups. -/
theorem final_pattern_one_chunk :
    ∀ pattern ∈ finalPatterns,
      (EncodedLayout.chunks.filter (· == pattern)).length = 1 := by decide

/-- For every selected direct-push pattern, any encoded opcode with the same
first byte has exactly its total length. Thus a boundary prefix match cannot
extend into the next encoded opcode. -/
theorem final_pattern_boundary_width :
    ∀ pattern ∈ finalPatterns, ∀ chunk ∈ EncodedLayout.chunks,
      chunk.head? = pattern.head? → chunk.length = pattern.length := by
  decide

theorem literal_chunks_nonempty :
    ∀ chunk ∈ EncodedLayout.chunks, chunk ≠ [] := by decide

private theorem head_eq_of_prefix_match (pattern chunk suffix : Bytes)
    (patternNonempty : pattern ≠ []) (chunkNonempty : chunk ≠ [])
    (isMatch : (chunk ++ suffix).take pattern.length = pattern) :
    chunk.head? = pattern.head? := by
  cases pattern with
  | nil => contradiction
  | cons p ps =>
    cases chunk with
    | nil => contradiction
    | cons c cs =>
      have same := congrArg List.head? isMatch
      simpa using same

/-- A selected signature pattern matching at a generated opcode boundary
is exactly that complete opcode, independently of the following bytes. -/
theorem selected_boundary_match_complete (sig chunk suffix : Bytes)
    (selected : directPushPattern sig ∈ finalPatterns)
    (boundary : chunk ∈ EncodedLayout.chunks)
    (isMatch : (chunk ++ suffix).take (directPushPattern sig).length =
      directPushPattern sig) :
    chunk = directPushPattern sig := by
  have sameFirst : chunk.head? = (directPushPattern sig).head? :=
    head_eq_of_prefix_match _ _ _ (by simp [directPushPattern])
      (literal_chunks_nonempty chunk boundary) isMatch
  exact boundary_match_consumes_chunk sig chunk suffix
    (final_pattern_boundary_width _ selected _ boundary sameFirst) isMatch

theorem generated_dummy_pattern_mem (i : Fin 150) :
    directPushPattern (FinalSignedLoop.generatedDummyAt i) ∈ finalPatterns := by
  have all : ∀ j : Fin 150,
      directPushPattern (FinalSignedLoop.generatedDummyAt j) ∈ finalPatterns := by
    decide
  exact all i

/-- Any actual selected final signature, not only a fixed sample, has one
complete serialized push in the literal locking script. -/
theorem selected_signature_one_chunk (ids : List (Fin 150))
    (sig : Bytes) (selected : sig ∈ finalSignatureBytes ids) :
    (EncodedLayout.chunks.filter (· == directPushPattern sig)).length = 1 := by
  have member : directPushPattern sig ∈ finalPatterns := by
    rcases List.mem_append.mp selected with dummy | nonce
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp dummy
      exact generated_dummy_pattern_mem i
    · simp only [List.mem_singleton] at nonce
      subst sig
      simp [finalPatterns]
  exact final_pattern_one_chunk _ member

def finalEncodedScriptCode (ids : List (Fin 150)) : Bytes :=
  stripEncodedChunks
    ((finalSignatureBytes ids).map directPushPattern)
    EncodedLayout.chunks

/-- The exact serialized-chunk filter for a chosen final set is independent
of draw order. This still does not assert equivalence to Core's FindAndDelete
on the 9,923-byte script. -/
theorem finalEncodedScriptCode_perm {left right : List (Fin 150)}
    (same : left.Perm right) :
    finalEncodedScriptCode left = finalEncodedScriptCode right := by
  apply stripEncodedChunks_perm
  have signatures : (finalSignatureBytes left).Perm
      (finalSignatureBytes right) := by
    exact (same.map FinalSignedLoop.generatedDummyAt).append_right _
  exact signatures.map directPushPattern

end QSB.EncodedScript
