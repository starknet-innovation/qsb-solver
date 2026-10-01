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

/-- Canonical serialized signature pushes are rigid at every opcode
boundary of the literal lock, for arbitrary signature bytes. -/
theorem literal_push_rigid (sig : Bytes) :
    rigidChunks (CorePushSerialize.pushPattern sig)
      EncodedLayout.chunks := by
  intro chunk present suffix
  have simple := (List.all_eq_true.mp literal_simple_chunks chunk present)
  constructor
  · intro matched
    by_cases short : sig.length < 76
    · have pattern := CorePushSerialize.pushPattern_direct sig short
      have headEq : chunk.head? = some (UInt8.ofNat sig.length) := by
        have both := EncodedScript.head_eq_of_prefix_match
          (CorePushSerialize.pushPattern sig) chunk suffix
          (CorePushSerialize.pushPattern_nonempty sig)
          (EncodedScript.literal_chunks_nonempty chunk present) matched
        simpa [pattern, ScriptCodeSelection.directPushPattern] using both
      have width := simple_direct_width chunk simple sig.length short headEq
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
      have chunkHead := simple_no_pushdata_head chunk simple
      have sameHead := EncodedScript.head_eq_of_prefix_match
        (CorePushSerialize.pushPattern sig) chunk suffix
        (CorePushSerialize.pushPattern_nonempty sig)
        (EncodedScript.literal_chunks_nonempty chunk present) matched
      rcases patternHead with h | h | h
      · exact False.elim (chunkHead.1 (sameHead.trans h))
      · exact False.elim (chunkHead.2.1 (sameHead.trans h))
      · exact False.elim (chunkHead.2.2 (sameHead.trans h))
  · intro same
    subst chunk
    simp

/-- With arbitrary reached signatures, the 880-step source-shaped deletion
loop equals filtering complete original chunks by their Core-serialized push
patterns. Thus no deletion can create extra opcode boundaries or exhaust the
fuel before the fixed lock is consumed. -/
theorem literal_many_pushes (sigs : List Bytes) :
    CoreFindAndDelete.runMany 880 EncodedLayout.chunks.flatten
      (sigs.map CorePushSerialize.pushPattern) =
      stripEncodedChunks (sigs.map CorePushSerialize.pushPattern)
        EncodedLayout.chunks := by
  rw [CoreFindAndDelete.runMany_eq_model_scanMany]
  apply scanMany_eq_chunk_filter _ _
    EncodedScript.literal_chunks_nonempty literal_stable_chunks
  · intro pattern present
    obtain ⟨sig, _, rfl⟩ := List.mem_map.mp present
    exact literal_push_rigid sig
  · simp [EncodedLayout.chunks_length]

end QSB.CorePushFindAndDelete
