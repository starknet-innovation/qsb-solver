import QSB.EncodedScript
import QSB.FirstOvershoot

/-!
A source-shaped byte loop for Core's legacy FindAndDelete: at each opcode
boundary, remove a matching byte pattern and retry at that boundary;
otherwise advance with GetOp. The fuel is explicit for totality. This module
proves when the byte loop equals filtering whole parsed opcode chunks.
It does not prove C++/Lean parser equivalence or Bitcoin sighash behavior.
-/
namespace QSB.FindAndDelete
open ByteMachine
open EncodedScript
open ScriptCodeSelection
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def scan : Nat → Bytes → Bytes → Bytes
  | 0, script, _ => script
  | fuel + 1, script, pattern =>
      if script = [] then []
      else if script.take pattern.length = pattern then
        scan fuel (script.drop pattern.length) pattern
      else
        match parseOne script with
        | some (chunk, rest) => chunk ++ scan fuel rest pattern
        | none => script

def stableChunks (chunks : List Bytes) : Prop :=
  ∀ chunk ∈ chunks, ∀ suffix,
    parseOne (chunk ++ suffix) = some (chunk, suffix)

def rigidChunks (pattern : Bytes) (chunks : List Bytes) : Prop :=
  ∀ chunk ∈ chunks, ∀ suffix,
    ((chunk ++ suffix).take pattern.length = pattern) ↔ chunk = pattern

/-- The literal lock uses only direct pushes and one-byte non-push opcodes.
PUSHDATA opcodes are handled by `parseOne` but do not occur in this fixture. -/
def simpleChunk : Bytes → Bool
  | [] => false
  | op :: payload =>
      if 1 ≤ op.toNat ∧ op.toNat ≤ 75 then
        payload.length == op.toNat
      else
        op.toNat != 0x4c && op.toNat != 0x4d &&
          op.toNat != 0x4e && payload == []

theorem simple_chunk_stable (chunk : Bytes) (simple : simpleChunk chunk = true) :
    ∀ suffix, parseOne (chunk ++ suffix) = some (chunk, suffix) := by
  cases chunk with
  | nil => simp [simpleChunk] at simple
  | cons op payload =>
      by_cases direct : 1 ≤ op.toNat ∧ op.toNat ≤ 75
      · have width : payload.length = op.toNat := by
          simpa [simpleChunk, direct] using simple
        intro suffix
        have consumed : consumePush [op] (payload ++ suffix) op.toNat =
            some (op :: payload, suffix) := by
          rw [← width]
          simp [consumePush]
        simpa [parseOne, direct] using consumed
      · intro suffix
        simp_all [simpleChunk, parseOne]

/-- If the parsed chunks remain stable under deletion and a pattern match
consumes one whole chunk, Core's repeated delete/parse loop equals filtering
those chunks. This is a generic structural statement with explicit premises. -/
theorem scan_eq_chunk_filter (pattern : Bytes) (chunks : List Bytes)
    (nonempty : ∀ chunk ∈ chunks, chunk ≠ [])
    (stable : stableChunks chunks) (rigid : rigidChunks pattern chunks)
    (fuel : Nat) (enough : chunks.length ≤ fuel) :
    scan fuel chunks.flatten pattern =
      (chunks.filter (· ≠ pattern)).flatten := by
  induction chunks generalizing fuel with
  | nil =>
      cases fuel <;> simp [scan]
  | cons chunk rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ remaining =>
          have restEnough : rest.length ≤ remaining := by
            simpa using enough
          have restStable : stableChunks rest := by
            intro c present suffix
            exact stable c (List.mem_cons_of_mem _ present) suffix
          have restRigid : rigidChunks pattern rest := by
            intro c present suffix
            exact rigid c (List.mem_cons_of_mem _ present) suffix
          have parseHead := stable chunk (List.mem_cons_self ..) rest.flatten
          have rigidHead := rigid chunk (List.mem_cons_self ..) rest.flatten
          have restNonempty : ∀ c ∈ rest, c ≠ [] := by
            intro c present
            exact nonempty c (List.mem_cons_of_mem _ present)
          have chunkNonempty : chunk ≠ [] :=
            nonempty chunk (List.mem_cons_self ..)
          have scriptNonempty : chunk ++ rest.flatten ≠ [] := by
            simp [chunkNonempty]
          by_cases same : chunk = pattern
          · subst chunk
            have hit : (pattern ++ rest.flatten).take pattern.length = pattern := by
              simp
            have drop : (pattern ++ rest.flatten).drop pattern.length =
                rest.flatten := by simp
            simpa [scan, scriptNonempty, hit, drop] using
              ih restNonempty restStable restRigid remaining restEnough
          · have miss : (chunk ++ rest.flatten).take pattern.length ≠ pattern := by
              exact fun h => same (rigidHead.mp h)
            simpa [scan, scriptNonempty, miss, parseHead, same] using
              ih restNonempty restStable restRigid remaining restEnough

/-- Kernel-checked syntactic classification of all 880 original encoded
opcodes. Together with `simple_chunk_stable`, this supplies stability after
removing any subset of complete chunks. -/
theorem literal_simple_chunks :
    EncodedLayout.chunks.all simpleChunk = true := by decide

theorem literal_stable_chunks : stableChunks EncodedLayout.chunks := by
  intro chunk present suffix
  exact simple_chunk_stable chunk
    (List.all_eq_true.mp literal_simple_chunks chunk present) suffix

theorem literal_rigid_chunks (sig : Bytes)
    (selected : directPushPattern sig ∈ finalPatterns) :
    rigidChunks (directPushPattern sig) EncodedLayout.chunks := by
  intro chunk boundary suffix
  constructor
  · exact selected_boundary_match_complete sig chunk suffix selected boundary
  · intro same
    subst chunk
    simp

/-- For any one of the 151 final signature patterns, the source-shaped raw
delete/parse loop removes precisely its serialized opcode from this lock. -/
theorem literal_single_delete (sig : Bytes)
    (selected : directPushPattern sig ∈ finalPatterns) :
    scan 880 EncodedLayout.chunks.flatten (directPushPattern sig) =
      stripEncodedChunks [directPushPattern sig] EncodedLayout.chunks := by
  have enough : EncodedLayout.chunks.length ≤ 880 := by
    simp [EncodedLayout.chunks_length]
  simpa [stripEncodedChunks] using
    scan_eq_chunk_filter (directPushPattern sig) EncodedLayout.chunks
      EncodedScript.literal_chunks_nonempty literal_stable_chunks
      (literal_rigid_chunks sig selected) 880 enough

def scanMany (fuel : Nat) (script : Bytes) : List Bytes → Bytes
  | [] => script
  | pattern :: rest => scanMany fuel (scan fuel script pattern) rest

/-- Repeating the source-shaped byte deletion for any list of rigid patterns
filters precisely those parsed chunks, including duplicate patterns. -/
theorem scanMany_eq_chunk_filter (patterns : List Bytes) (chunks : List Bytes)
    (nonempty : ∀ chunk ∈ chunks, chunk ≠ [])
    (stable : stableChunks chunks)
    (rigid : ∀ pattern ∈ patterns, rigidChunks pattern chunks)
    (fuel : Nat) (enough : chunks.length ≤ fuel) :
    scanMany fuel chunks.flatten patterns =
      (chunks.filter (fun chunk => chunk ∉ patterns)).flatten := by
  induction patterns generalizing chunks with
  | nil => simp [scanMany]
  | cons pattern rest ih =>
      let surviving := chunks.filter (· ≠ pattern)
      have first : scan fuel chunks.flatten pattern = surviving.flatten :=
        scan_eq_chunk_filter pattern chunks nonempty
          stable (rigid pattern (List.mem_cons_self ..)) fuel enough
      have survivingNonempty : ∀ chunk ∈ surviving, chunk ≠ [] := by
        intro chunk present
        exact nonempty chunk (List.mem_filter.mp present).1
      have survivingStable : stableChunks surviving := by
        intro chunk present suffix
        exact stable chunk (List.mem_filter.mp present).1 suffix
      have survivingRigid : ∀ p ∈ rest, rigidChunks p surviving := by
        intro p present chunk inSurviving suffix
        exact rigid p (List.mem_cons_of_mem _ present) chunk
          (List.mem_filter.mp inSurviving).1 suffix
      have survivingEnough : surviving.length ≤ fuel :=
        (List.length_filter_le _ _).trans enough
      have filters :
          surviving.filter (fun chunk => chunk ∉ rest) =
            chunks.filter (fun chunk => chunk ∉ pattern :: rest) := by
        dsimp [surviving]
        rw [List.filter_filter]
        apply List.filter_congr
        intro chunk _
        simp [List.mem_cons, Bool.and_comm]
      calc
        scanMany fuel chunks.flatten (pattern :: rest) =
            scanMany fuel surviving.flatten rest := by
              simp [scanMany, first]
        _ = (surviving.filter (fun chunk => chunk ∉ rest)).flatten :=
          ih surviving survivingNonempty survivingStable survivingRigid
            survivingEnough
        _ = (chunks.filter (fun chunk => chunk ∉ pattern :: rest)).flatten := by
          rw [filters]

theorem literal_rigid_final_pattern (pattern : Bytes)
    (selected : pattern ∈ finalPatterns) :
    rigidChunks pattern EncodedLayout.chunks := by
  obtain ⟨sig, _, rfl⟩ := List.mem_map.mp selected
  exact literal_rigid_chunks sig selected

/-- Any ordered list drawn from the 151 literal final signature patterns has
the same byte result under repeated source-shaped deletion as filtering the
complete encoded chunks. The list may contain repeated patterns. -/
theorem literal_many_delete (patterns : List Bytes)
    (selected : ∀ pattern ∈ patterns, pattern ∈ finalPatterns) :
    scanMany 880 EncodedLayout.chunks.flatten patterns =
      stripEncodedChunks patterns EncodedLayout.chunks := by
  have rigid : ∀ p ∈ patterns, rigidChunks p EncodedLayout.chunks := by
    intro p present
    exact literal_rigid_final_pattern p (selected p present)
  have enough : EncodedLayout.chunks.length ≤ 880 := by
    simp [EncodedLayout.chunks_length]
  simpa [stripEncodedChunks] using
    scanMany_eq_chunk_filter patterns EncodedLayout.chunks
      EncodedScript.literal_chunks_nonempty literal_stable_chunks rigid
      880 enough

theorem selected_patterns_subset (ids : List (Fin 150)) :
    ∀ pattern ∈ (finalSignatureBytes ids).map directPushPattern,
      pattern ∈ finalPatterns := by
  intro pattern present
  obtain ⟨sig, sigPresent, rfl⟩ := List.mem_map.mp present
  rcases List.mem_append.mp sigPresent with dummy | nonce
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp dummy
    exact generated_dummy_pattern_mem i
  · simp only [List.mem_singleton] at nonce
    subst sig
    simp [finalPatterns]

/-- The selected final signatures from any original-index list, plus the
fixed ALL nonce signature, determine the precise byte-level scriptCode of
the modeled sequential FindAndDelete loop for this literal lock. -/
theorem final_scriptCode_scan (ids : List (Fin 150)) :
    scanMany 880 EncodedLayout.chunks.flatten
      ((finalSignatureBytes ids).map directPushPattern) =
      finalEncodedScriptCode ids := by
  exact literal_many_delete _ (selected_patterns_subset ids)

/-- The fixed pinning CHECKSIGVERIFY signature's serialized push. -/
def pinPattern : Bytes :=
  directPushPattern FirstOvershoot.pinSignature

theorem pin_signature_sighash_all :
    FirstOvershoot.pinSignature.getLast? = some 0x01 := by decide

/-- This exact generated lock contains the pin signature as one complete
direct-push opcode. It says nothing about other generated vault instances. -/
theorem pin_pattern_one_chunk :
    (EncodedLayout.chunks.filter (· == pinPattern)).length = 1 := by decide

theorem pin_pattern_boundary_width :
    ∀ chunk ∈ EncodedLayout.chunks,
      chunk.head? = pinPattern.head? → chunk.length = pinPattern.length := by
  decide

theorem pin_pattern_rigid : rigidChunks pinPattern EncodedLayout.chunks := by
  intro chunk boundary suffix
  constructor
  · intro matched
    have sameFirst := EncodedScript.head_eq_of_prefix_match
      pinPattern chunk suffix (by simp [pinPattern, directPushPattern])
      (EncodedScript.literal_chunks_nonempty chunk boundary) matched
    have sameLength := pin_pattern_boundary_width chunk boundary sameFirst
    exact boundary_match_consumes_chunk FirstOvershoot.pinSignature
      chunk suffix (by simpa [pinPattern] using sameLength)
      (by simpa [pinPattern] using matched)
  · intro same
    subst chunk
    simp

/-- In the source-shaped FindAndDelete loop, removal of the *reached fixed
pin signature* deletes precisely its complete serialized push. The remaining
bytes are the pinning scriptCode candidate for legacy SIGHASH_ALL. The Core
C++ parser and ECDSA checker still require refinement. -/
theorem pin_scriptCode_scan :
    scan 880 EncodedLayout.chunks.flatten pinPattern =
      stripEncodedChunks [pinPattern] EncodedLayout.chunks := by
  have enough : EncodedLayout.chunks.length ≤ 880 := by
    simp [EncodedLayout.chunks_length]
  simpa [stripEncodedChunks] using
    scan_eq_chunk_filter pinPattern EncodedLayout.chunks
      EncodedScript.literal_chunks_nonempty literal_stable_chunks
      pin_pattern_rigid 880 enough

end QSB.FindAndDelete
