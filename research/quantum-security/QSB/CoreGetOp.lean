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

private theorem take_header (header rest : Bytes) (size : Nat) :
    (header ++ rest).take (header.length + size) =
      header ++ rest.take size := by
  rw [List.take_append]
  simp

private theorem drop_header (header rest : Bytes) (size : Nat) :
    (header ++ rest).drop (header.length + size) = rest.drop size := by
  rw [List.drop_append]
  simp

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

/-- The iterator-width and chunk-return parsers agree on every input byte
string, including truncated PUSHDATA headers and payloads. -/
theorem parse_eq_parseOne (script : Bytes) :
    parse script = parseOne script := by
  cases script with
  | nil => rfl
  | cons op rest =>
      by_cases zero : op.toNat = 0
      · simp [parse, width, parseOne, zero]
      · by_cases direct : 1 ≤ op.toNat ∧ op.toNat ≤ 75
        · have small : op.toNat ≤ 75 := direct.2
          by_cases enough : op.toNat ≤ rest.length
          · simp only [parse, width, parseOne, consumePush]
            simp [direct, enough]
            constructor
            · simpa [Nat.add_comm] using take_header [op] rest op.toNat
            · simpa [Nat.add_comm] using drop_header [op] rest op.toNat
          · simp [parse, width, parseOne, consumePush, direct, enough]
        · have large : op.toNat > 75 := by omega
          by_cases push1 : op.toNat = 0x4c
          · cases rest with
            | nil => simp [parse, width, parseOne, push1]
            | cons size tail =>
                by_cases enough : size.toNat ≤ tail.length
                · simp [parse, width, parseOne, consumePush,
                    push1, enough]
                  constructor
                  · simpa [Nat.add_comm, Nat.add_assoc] using
                      take_header [op, size] tail size.toNat
                  · simpa [Nat.add_comm, Nat.add_assoc] using
                      drop_header [op, size] tail size.toNat
                · simp [parse, width, parseOne, consumePush,
                    push1, enough]
          · by_cases push2 : op.toNat = 0x4d
            · cases rest with
              | nil => simp [parse, width, parseOne, push2]
              | cons lo rest =>
                  cases rest with
                  | nil => simp [parse, width, parseOne, push2]
                  | cons hi tail =>
                      let size := lo.toNat + 256 * hi.toNat
                      by_cases enough : size ≤ tail.length
                      · simp [parse, width, parseOne, consumePush,
                          push2, size, enough]
                        constructor
                        · simpa [size, Nat.add_assoc, Nat.add_comm,
                            Nat.add_left_comm] using
                            take_header [op, lo, hi] tail size
                        · simpa [size, Nat.add_assoc, Nat.add_comm,
                            Nat.add_left_comm] using
                            drop_header [op, lo, hi] tail size
                      · simp [parse, width, parseOne, consumePush,
                          push2, size, enough]
            · by_cases push4 : op.toNat = 0x4e
              · cases rest with
                | nil => simp [parse, width, parseOne, push4]
                | cons a rest =>
                    cases rest with
                    | nil => simp [parse, width, parseOne, push4]
                    | cons b rest =>
                        cases rest with
                        | nil => simp [parse, width, parseOne, push4]
                        | cons c rest =>
                            cases rest with
                            | nil => simp [parse, width, parseOne, push4]
                            | cons d tail =>
                                let size := a.toNat + 256 * b.toNat +
                                  65536 * c.toNat + 16777216 * d.toNat
                                by_cases enough : size ≤ tail.length
                                · simp [parse, width, parseOne, consumePush,
                                    push4, size, enough]
                                  constructor
                                  · simpa [size, Nat.add_assoc, Nat.add_comm,
                                      Nat.add_left_comm] using
                                      take_header [op, a, b, c, d] tail size
                                  · simpa [size, Nat.add_assoc, Nat.add_comm,
                                      Nat.add_left_comm] using
                                      drop_header [op, a, b, c, d] tail size
                                · simp [parse, width, parseOne, consumePush,
                                    push4, size, enough]
              · have notSmall : ¬ op.toNat ≤ 75 := by omega
                simp [parse, width, parseOne, notSmall,
                  push1, push2, push4]

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

/-- A successfully parsed opcode partitions the original byte string. -/
theorem parse_split (script chunk rest : Bytes)
    (parsed : parse script = some (chunk, rest)) :
    chunk ++ rest = script := by
  unfold parse at parsed
  cases hwidth : width script with
  | none => simp [hwidth] at parsed
  | some count =>
      have pair : (script.take count, script.drop count) =
          (chunk, rest) := by simpa [hwidth] using parsed
      have hc : chunk = script.take count := (Prod.mk.inj pair).1.symm
      have hr : rest = script.drop count := (Prod.mk.inj pair).2.symm
      subst chunk
      subst rest
      exact List.take_append_drop count script

/-- Any successful source-shaped opcode decomposition reconstructs the exact
input bytes, including arbitrary PUSHDATA forms in a scriptSig. This is a
parser provenance fact; it does not execute the decoded opcodes or establish
that compiled Core uses this Lean parser. -/
theorem parseChunks_sound (fuel : Nat) (script : Bytes)
    (chunks : List Bytes)
    (parsed : EncodedScript.parseChunks fuel script = some chunks) :
    chunks.flatten = script := by
  induction fuel generalizing script chunks with
  | zero =>
      cases script with
      | nil =>
          simp [EncodedScript.parseChunks] at parsed
          subst chunks
          rfl
      | cons op rest => simp [EncodedScript.parseChunks] at parsed
  | succ fuel ih =>
      cases script with
      | nil =>
          simp [EncodedScript.parseChunks] at parsed
          subst chunks
          rfl
      | cons op rest =>
          simp only [EncodedScript.parseChunks] at parsed
          cases first : parseOne (op :: rest) with
          | none => simp [first] at parsed
          | some value =>
              rcases value with ⟨chunk, tail⟩
              cases later : EncodedScript.parseChunks fuel tail with
              | none => simp [first, later] at parsed
              | some following =>
                  simp [first, later] at parsed
                  subst chunks
                  have split : chunk ++ tail = op :: rest :=
                    parse_split (op :: rest) chunk tail (by
                      rw [parse_eq_parseOne]
                      exact first)
                  simpa [ih tail following later] using split

/-- Source-shaped FindAndDelete never increases script byte length, even
for malformed scripts, empty patterns, or insufficient loop fuel. -/
theorem scan_length_le (fuel : Nat) (script pattern : Bytes) :
    (scan fuel script pattern).length ≤ script.length := by
  induction fuel generalizing script with
  | zero => rfl
  | succ fuel ih =>
      by_cases empty : script = []
      · simp [scan, empty]
      · by_cases hit : script.take pattern.length = pattern
        · have h := ih (script.drop pattern.length)
          simp only [scan, empty, ↓reduceIte, hit]
          have dropLe : (script.drop pattern.length).length ≤
              script.length := by simp
          exact h.trans dropLe
        · cases parsed : parse script with
          | none => simp [scan, empty, hit, parsed]
          | some pair =>
              obtain ⟨chunk, rest⟩ := pair
              have split := parse_split script chunk rest parsed
              have h := ih rest
              simp only [scan, empty, hit, ↓reduceIte, parsed,
                List.length_append]
              have lengths := congrArg List.length split
              simp only [List.length_append] at lengths
              omega

/-- The two deletion loops agree on every byte string and pattern, with no
well-formed-script or complete-chunk premise. The theorem concerns the two
Lean source models; C++ semantic correspondence is still external. -/
theorem scan_eq_model_scan_all (fuel : Nat) (script pattern : Bytes) :
    scan fuel script pattern = FindAndDelete.scan fuel script pattern := by
  induction fuel generalizing script with
  | zero => rfl
  | succ fuel ih =>
      simp only [scan, FindAndDelete.scan, parse_eq_parseOne]
      simp [ih]
      rfl

/-- For each selected final signature, the Core-shaped parser/deletion model
and the existing byte-model deletion loop agree on the literal 9,923-byte
locking script. -/
theorem literal_selected_delete (sig : Bytes)
    (selected : directPushPattern sig ∈ finalPatterns) :
    scan 880 EncodedLayout.chunks.flatten (directPushPattern sig) =
      stripEncodedChunks [directPushPattern sig] EncodedLayout.chunks := by
  rw [scan_eq_model_scan_all]
  exact literal_single_delete sig selected

def scanMany (fuel : Nat) (script : Bytes) : List Bytes → Bytes
  | [] => script
  | pattern :: rest => scanMany fuel (scan fuel script pattern) rest

theorem scanMany_eq_model_scanMany_all (fuel : Nat) (script : Bytes)
    (patterns : List Bytes) :
    scanMany fuel script patterns =
      FindAndDelete.scanMany fuel script patterns := by
  induction patterns generalizing script with
  | nil => rfl
  | cons pattern rest ih =>
      simp only [scanMany, FindAndDelete.scanMany]
      rw [scan_eq_model_scan_all, ih]

/-- The complete sequential final-signature FindAndDelete result for the
literal lock agrees with the prior chunk-filter scriptCode theorem. -/
theorem final_scriptCode_scan (ids : List (Fin 150)) :
    scanMany 880 EncodedLayout.chunks.flatten
      ((finalSignatureBytes ids).map directPushPattern) =
      finalEncodedScriptCode ids := by
  rw [scanMany_eq_model_scanMany_all]
  exact FindAndDelete.final_scriptCode_scan ids

/-- The same parser refinement applies to the fixed pinning signature. -/
theorem pin_scriptCode_scan :
    scan 880 EncodedLayout.chunks.flatten pinPattern =
      stripEncodedChunks [pinPattern] EncodedLayout.chunks := by
  rw [scan_eq_model_scan_all]
  exact FindAndDelete.pin_scriptCode_scan

end QSB.CoreGetOp
