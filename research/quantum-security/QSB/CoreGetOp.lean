import QSB.FindAndDelete

/-!
A byte-count model of Bitcoin Core v27.2 `GetScriptOp` in
`src/script/script.cpp` lines 289-340: read an opcode and an optional
PUSHDATA length, then either advance past the payload or fail on truncation.
The returned width is the C++ iterator advance from the original position.

This is a source-level model, not a proof about compiled C++ semantics.
-/
namespace QSB.CoreGetOp
open ByteMachine
open EncodedScript
open FindAndDelete
open ScriptCodeSelection

def width : Bytes → Option Nat
  | [] => none
  | op :: rest =>
      let n := op.toNat
      if n ≤ 75 then
        if n ≤ rest.length then some (1 + n) else none
      else if n == 0x4c then
        match rest with
        | size :: tail =>
            if size.toNat ≤ tail.length then some (2 + size.toNat) else none
        | _ => none
      else if n == 0x4d then
        match rest with
        | lo :: hi :: tail =>
            let size := lo.toNat + 256 * hi.toNat
            if size ≤ tail.length then some (3 + size) else none
        | _ => none
      else if n == 0x4e then
        match rest with
        | a :: b :: c :: d :: tail =>
            let size := a.toNat + 256 * b.toNat +
              65536 * c.toNat + 16777216 * d.toNat
            if size ≤ tail.length then some (5 + size) else none
        | _ => none
      else some 1

def parse (script : Bytes) : Option (Bytes × Bytes) := do
  let consumed ← width script
  some (script.take consumed, script.drop consumed)

/-- The independent iterator-width model sees every literal QSB opcode
boundary as exactly one complete serialized chunk. -/
theorem simple_chunk_width (chunk : Bytes)
    (simple : simpleChunk chunk = true) (suffix : Bytes) :
    width (chunk ++ suffix) = some chunk.length := by
  cases chunk with
  | nil => simp [simpleChunk] at simple
  | cons op payload =>
      by_cases direct : 1 ≤ op.toNat ∧ op.toNat ≤ 75
      · have size : payload.length = op.toNat := by
          simpa [simpleChunk, direct] using simple
        have atMost : op.toNat ≤ 75 := direct.2
        simp [width, atMost, size, Nat.add_comm]
      · have parts :
            ((op.toNat ≠ 76 ∧ op.toNat ≠ 77) ∧ op.toNat ≠ 78) ∧
              payload = [] := by
          simpa [simpleChunk, direct] using simple
        rcases parts with ⟨⟨⟨not76, not77⟩, not78⟩, empty⟩
        subst payload
        by_cases small : op.toNat ≤ 75
        · have zero : op.toNat = 0 := by omega
          simp [width, zero]
        · simp [width, small, not76, not77, not78]

theorem parse_simple_chunk (chunk : Bytes)
    (simple : simpleChunk chunk = true) (suffix : Bytes) :
    parse (chunk ++ suffix) = some (chunk, suffix) := by
  simp [parse, simple_chunk_width chunk simple suffix]

/-- On every residual suffix of the literal lock after complete-chunk
deletions, the source-shaped iterator parser and the existing byte parser
advance past the same opcode bytes. -/
theorem parse_matches_model_simple (chunk : Bytes)
    (simple : simpleChunk chunk = true) (suffix : Bytes) :
    parse (chunk ++ suffix) = parseOne (chunk ++ suffix) := by
  rw [parse_simple_chunk chunk simple suffix,
    simple_chunk_stable chunk simple suffix]

theorem literal_parse_stable :
    ∀ chunk ∈ EncodedLayout.chunks, ∀ suffix,
      parse (chunk ++ suffix) = some (chunk, suffix) := by
  intro chunk present suffix
  exact parse_simple_chunk chunk
    (List.all_eq_true.mp literal_simple_chunks chunk present) suffix

/-- Source-shaped FindAndDelete with the separate `GetScriptOp` iterator-width
model. `FindAndDelete.scan` uses `parseOne` instead. -/
def scan : Nat → Bytes → Bytes → Bytes
  | 0, script, _ => script
  | fuel + 1, script, pattern =>
      if script = [] then []
      else if script.take pattern.length = pattern then
        scan fuel (script.drop pattern.length) pattern
      else
        match parse script with
        | some (chunk, rest) => chunk ++ scan fuel rest pattern
        | none => script

/-- The two separately defined source-shaped deletion loops agree whenever
the input consists of stable simple chunks and the deletion pattern can match
only an entire chunk at an opcode boundary. -/
theorem scan_eq_model_scan (pattern : Bytes) (chunks : List Bytes)
    (nonempty : ∀ chunk ∈ chunks, chunk ≠ [])
    (simple : ∀ chunk ∈ chunks, simpleChunk chunk = true)
    (rigid : rigidChunks pattern chunks)
    (fuel : Nat) (enough : chunks.length ≤ fuel) :
    scan fuel chunks.flatten pattern =
      FindAndDelete.scan fuel chunks.flatten pattern := by
  induction chunks generalizing fuel with
  | nil => cases fuel <;> simp [scan, FindAndDelete.scan]
  | cons chunk rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ remaining =>
          have restEnough : rest.length ≤ remaining := by simpa using enough
          have restNonempty : ∀ c ∈ rest, c ≠ [] := by
            intro c present
            exact nonempty c (List.mem_cons_of_mem _ present)
          have restSimple : ∀ c ∈ rest, simpleChunk c = true := by
            intro c present
            exact simple c (List.mem_cons_of_mem _ present)
          have restRigid : rigidChunks pattern rest := by
            intro c present suffix
            exact rigid c (List.mem_cons_of_mem _ present) suffix
          have chunkNonempty : chunk ≠ [] :=
            nonempty chunk (List.mem_cons_self ..)
          have scriptNonempty : chunk ++ rest.flatten ≠ [] := by
            simp [chunkNonempty]
          have parseHead := parse_simple_chunk chunk
            (simple chunk (List.mem_cons_self ..)) rest.flatten
          have modelHead := simple_chunk_stable chunk
            (simple chunk (List.mem_cons_self ..)) rest.flatten
          have rigidHead := rigid chunk (List.mem_cons_self ..) rest.flatten
          by_cases same : chunk = pattern
          · subst chunk
            have hit : (pattern ++ rest.flatten).take pattern.length = pattern := by
              simp
            have drop : (pattern ++ rest.flatten).drop pattern.length =
                rest.flatten := by simp
            simpa [scan, FindAndDelete.scan, scriptNonempty, hit, drop]
              using ih restNonempty restSimple restRigid remaining restEnough
          · have miss :
                (chunk ++ rest.flatten).take pattern.length ≠ pattern := by
              exact fun h => same (rigidHead.mp h)
            simpa [scan, FindAndDelete.scan, scriptNonempty, miss,
              parseHead, modelHead] using
              ih restNonempty restSimple restRigid remaining restEnough

/-- For each selected final signature, the Core-shaped parser/deletion model
and the existing byte-model deletion loop agree on the literal 9,923-byte
locking script. -/
theorem literal_selected_delete (sig : Bytes)
    (selected : directPushPattern sig ∈ finalPatterns) :
    scan 880 EncodedLayout.chunks.flatten (directPushPattern sig) =
      stripEncodedChunks [directPushPattern sig] EncodedLayout.chunks := by
  rw [scan_eq_model_scan (directPushPattern sig) EncodedLayout.chunks
    EncodedScript.literal_chunks_nonempty
    (by intro chunk present
        exact List.all_eq_true.mp literal_simple_chunks chunk present)
    (literal_rigid_chunks sig selected) 880 (by
      simp [EncodedLayout.chunks_length])]
  exact literal_single_delete sig selected

def scanMany (fuel : Nat) (script : Bytes) : List Bytes → Bytes
  | [] => script
  | pattern :: rest => scanMany fuel (scan fuel script pattern) rest

/-- Sequential Core-shaped deletions agree with the existing source-shaped
loop for any pattern list rigid on the original simple chunks. -/
theorem scanMany_eq_model_scanMany (patterns : List Bytes)
    (chunks : List Bytes)
    (nonempty : ∀ chunk ∈ chunks, chunk ≠ [])
    (simple : ∀ chunk ∈ chunks, simpleChunk chunk = true)
    (rigid : ∀ pattern ∈ patterns, rigidChunks pattern chunks)
    (fuel : Nat) (enough : chunks.length ≤ fuel) :
    scanMany fuel chunks.flatten patterns =
      FindAndDelete.scanMany fuel chunks.flatten patterns := by
  induction patterns generalizing chunks with
  | nil => rfl
  | cons pattern rest ih =>
      let surviving := chunks.filter (· ≠ pattern)
      have firstModel :
          FindAndDelete.scan fuel chunks.flatten pattern =
            surviving.flatten :=
        scan_eq_chunk_filter pattern chunks nonempty
          (by intro c present suffix
              exact simple_chunk_stable c (simple c present) suffix)
          (rigid pattern (List.mem_cons_self ..)) fuel enough
      have firstCore : scan fuel chunks.flatten pattern =
          surviving.flatten := by
        rw [scan_eq_model_scan pattern chunks nonempty simple
          (rigid pattern (List.mem_cons_self ..)) fuel enough]
        exact firstModel
      have survivingNonempty : ∀ c ∈ surviving, c ≠ [] := by
        intro c present
        exact nonempty c (List.mem_filter.mp present).1
      have survivingSimple : ∀ c ∈ surviving, simpleChunk c = true := by
        intro c present
        exact simple c (List.mem_filter.mp present).1
      have survivingRigid : ∀ p ∈ rest, rigidChunks p surviving := by
        intro p present c cPresent suffix
        exact rigid p (List.mem_cons_of_mem _ present) c
          (List.mem_filter.mp cPresent).1 suffix
      have survivingEnough : surviving.length ≤ fuel :=
        (List.length_filter_le _ _).trans enough
      calc
        scanMany fuel chunks.flatten (pattern :: rest) =
            scanMany fuel surviving.flatten rest := by
              simp [scanMany, firstCore]
        _ = FindAndDelete.scanMany fuel surviving.flatten rest :=
          ih surviving survivingNonempty survivingSimple survivingRigid
            survivingEnough
        _ = FindAndDelete.scanMany fuel chunks.flatten (pattern :: rest) := by
          simp [FindAndDelete.scanMany, firstModel]

/-- The complete sequential final-signature FindAndDelete result for the
literal lock agrees with the prior chunk-filter scriptCode theorem. -/
theorem final_scriptCode_scan (ids : List (Fin 150)) :
    scanMany 880 EncodedLayout.chunks.flatten
      ((finalSignatureBytes ids).map directPushPattern) =
      finalEncodedScriptCode ids := by
  rw [scanMany_eq_model_scanMany _ EncodedLayout.chunks
    EncodedScript.literal_chunks_nonempty
    (by intro chunk present
        exact List.all_eq_true.mp literal_simple_chunks chunk present)
    (by intro pattern present
        exact literal_rigid_final_pattern pattern
          (selected_patterns_subset ids pattern present))
    880 (by simp [EncodedLayout.chunks_length])]
  exact FindAndDelete.final_scriptCode_scan ids

/-- The same parser refinement applies to the fixed pinning signature. -/
theorem pin_scriptCode_scan :
    scan 880 EncodedLayout.chunks.flatten pinPattern =
      stripEncodedChunks [pinPattern] EncodedLayout.chunks := by
  rw [scan_eq_model_scan pinPattern EncodedLayout.chunks
    EncodedScript.literal_chunks_nonempty
    (by intro chunk present
        exact List.all_eq_true.mp literal_simple_chunks chunk present)
    pin_pattern_rigid 880 (by simp [EncodedLayout.chunks_length])]
  exact FindAndDelete.pin_scriptCode_scan

end QSB.CoreGetOp
