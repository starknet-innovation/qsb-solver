import QSB.CoreFindAndDelete
import QSB.CorePushSerialize

/-!
For the fixed generated lock, every canonical Core signature-push pattern
either equals one complete encoded opcode or does not match at an opcode
boundary. This permits the source-shaped FindAndDelete loop to process an
arbitrary ordered list of reached signatures with 880 steps per deletion,
even when signatures are long, malformed, duplicated, or later skipped by
the CHECKMULTISIG pair scan. The theorem concerns this literal lock and the
Lean source model; it is not compiled-C++ refinement.
-/
namespace QSB.CorePushFindAndDelete
open ByteMachine
open FindAndDelete
open ScriptCodeSelection

private theorem simple_direct_width (chunk : Bytes)
    (simple : simpleChunk chunk = true) (n : Nat)
    (short : n < 76)
    (head : chunk.head? = some (UInt8.ofNat n)) :
    chunk.length = n + 1 := by
  cases chunk with
  | nil => simp at head
  | cons op payload =>
      have opEq : op = UInt8.ofNat n := by simpa using head
      subst op
      have byteN : (UInt8.ofNat n).toNat = n :=
        UInt8.toNat_ofNat_of_lt (by change n < 256; omega)
      by_cases zero : n = 0
      · subst n
        have empty : payload = [] := by
          simpa [simpleChunk, byteN] using simple
        simp [empty]
      · have direct : 1 ≤ n ∧ n ≤ 75 := by omega
        have width : payload.length = n := by
          simpa [simpleChunk, byteN, direct] using simple
        simp [width]

private theorem simple_no_pushdata_head (chunk : Bytes)
    (simple : simpleChunk chunk = true) :
    chunk.head? ≠ some 0x4c ∧
      chunk.head? ≠ some 0x4d ∧
      chunk.head? ≠ some 0x4e := by
  cases chunk with
  | nil => simp
  | cons op payload =>
      have no76 : op ≠ 0x4c := by
        intro eq
        subst op
        simp [simpleChunk] at simple
      have no77 : op ≠ 0x4d := by
        intro eq
        subst op
        simp [simpleChunk] at simple
      have no78 : op ≠ 0x4e := by
        intro eq
        subst op
        simp [simpleChunk] at simple
      simpa using ⟨no76, no77, no78⟩

/-- Canonical serialized signature pushes are rigid at every opcode boundary
of any script split into simple direct-push or one-byte opcode chunks. This
also covers arbitrary long or malformed signature bytes: their PUSHDATA
prefix cannot match a simple chunk header. -/
theorem simple_push_rigid (chunks : List Bytes)
    (simple : ∀ chunk ∈ chunks, simpleChunk chunk = true)
    (sig : Bytes) :
    rigidChunks (CorePushSerialize.pushPattern sig) chunks := by
  intro chunk present suffix
  have chunkSimple := simple chunk present
  have chunkNonempty : chunk ≠ [] := by
    intro empty
    subst chunk
    simp [simpleChunk] at chunkSimple
  constructor
  · intro matched
    by_cases short : sig.length < 76
    · have pattern := CorePushSerialize.pushPattern_direct sig short
      have headEq : chunk.head? = some (UInt8.ofNat sig.length) := by
        have both := EncodedScript.head_eq_of_prefix_match
          (CorePushSerialize.pushPattern sig) chunk suffix
          (CorePushSerialize.pushPattern_nonempty sig)
          chunkNonempty matched
        simpa [pattern, ScriptCodeSelection.directPushPattern] using both
      have width := simple_direct_width chunk chunkSimple sig.length short headEq
      have width' : chunk.length =
          (ScriptCodeSelection.directPushPattern sig).length := by
        simpa [ScriptCodeSelection.directPushPattern] using width
      have matched' :
          (chunk ++ suffix).take
            (ScriptCodeSelection.directPushPattern sig).length =
              ScriptCodeSelection.directPushPattern sig := by
        simpa [pattern] using matched
      exact (ScriptCodeSelection.boundary_match_consumes_chunk sig chunk
        suffix width' matched').trans pattern.symm
    · have long : 76 ≤ sig.length := by omega
      have patternHead := CorePushSerialize.long_head sig long
      have chunkHead := simple_no_pushdata_head chunk chunkSimple
      have sameHead := EncodedScript.head_eq_of_prefix_match
        (CorePushSerialize.pushPattern sig) chunk suffix
        (CorePushSerialize.pushPattern_nonempty sig)
        chunkNonempty matched
      rcases patternHead with h | h | h
      · exact False.elim (chunkHead.1 (sameHead.trans h))
      · exact False.elim (chunkHead.2.1 (sameHead.trans h))
      · exact False.elim (chunkHead.2.2 (sameHead.trans h))
  · intro same
    subst chunk
    simp

/-- Canonical pushes are rigid on the 880 simple chunks of the literal lock,
even for malformed or long reached signatures. -/
theorem literal_push_rigid (sig : Bytes) :
    rigidChunks (CorePushSerialize.pushPattern sig)
      EncodedLayout.chunks :=
  simple_push_rigid EncodedLayout.chunks
    (fun chunk present =>
      List.all_eq_true.mp literal_simple_chunks chunk present) sig

/-- On any simple-chunk script, Core-shaped repeated FindAndDelete of an
arbitrary reached signature list equals filtering complete original opcode
chunks. The fuel must cover the original chunk count; no short-signature or
distinctness premise is needed. -/
theorem simple_many_pushes (fuel : Nat) (chunks : List Bytes)
    (simple : ∀ chunk ∈ chunks, simpleChunk chunk = true)
    (enough : chunks.length ≤ fuel) (sigs : List Bytes) :
    CoreFindAndDelete.runMany fuel chunks.flatten
      (sigs.map CorePushSerialize.pushPattern) =
      stripEncodedChunks (sigs.map CorePushSerialize.pushPattern)
        chunks := by
  rw [CoreFindAndDelete.runMany_eq_model_scanMany]
  apply scanMany_eq_chunk_filter _ _
  · intro chunk present empty
    subst chunk
    have impossible := simple [] present
    simp [simpleChunk] at impossible
  · intro chunk present suffix
    exact simple_chunk_stable chunk (simple chunk present) suffix
  · intro pattern present
    obtain ⟨sig, _, rfl⟩ := List.mem_map.mp present
    exact simple_push_rigid chunks simple sig
  · exact enough

/-- With arbitrary reached signatures, the 880-step source-shaped deletion
loop equals filtering complete original chunks by their Core-serialized push
patterns. Thus no deletion can create extra opcode boundaries or exhaust the
fuel before the fixed lock is consumed. -/
theorem literal_many_pushes (sigs : List Bytes) :
    CoreFindAndDelete.runMany 880 EncodedLayout.chunks.flatten
      (sigs.map CorePushSerialize.pushPattern) =
      stripEncodedChunks (sigs.map CorePushSerialize.pushPattern)
        EncodedLayout.chunks := by
  exact simple_many_pushes 880 EncodedLayout.chunks
    (fun chunk present =>
      List.all_eq_true.mp literal_simple_chunks chunk present)
    (by simp [EncodedLayout.chunks_length]) sigs

end QSB.CorePushFindAndDelete
