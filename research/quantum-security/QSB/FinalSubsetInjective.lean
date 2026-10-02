import QSB.ScriptSigSighash
import QSB.DynamicSerializedRound

/-!
The literal final signature set controls which serialized opcode chunks are
removed. This module recovers that set from the source-shaped final scriptCode
on the disposable lock. It does not claim that every set is a reachable QSB
witness or that SHA256d is injective.
-/
namespace QSB.FinalSubsetInjective
open ByteMachine ScriptCodeSelection
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def dummyPattern (i : Fin 150) : Bytes :=
  directPushPattern (FinalSignedLoop.generatedDummyAt i)

def noncePattern : Bytes :=
  directPushPattern PoolRollInvariant.finalNonce

def selectedPatterns (ids : List (Fin 150)) : List Bytes :=
  (finalSignatureBytes ids).map directPushPattern

def residualChunks (ids : List (Fin 150)) : List Bytes :=
  EncodedLayout.chunks.filter (fun chunk => chunk ∉ selectedPatterns ids)

private theorem parse_simple_chunks_fuel (xs : List Bytes) (fuel : Nat)
    (simple : ∀ chunk ∈ xs, FindAndDelete.simpleChunk chunk = true)
    (enough : xs.length ≤ fuel) :
    EncodedScript.parseChunks fuel xs.flatten = some xs := by
  induction xs generalizing fuel with
  | nil =>
      cases fuel <;> rfl
  | cons chunk rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ n =>
          have head : FindAndDelete.simpleChunk chunk = true :=
            simple chunk (List.mem_cons_self ..)
          have tailSimple : ∀ c ∈ rest,
              FindAndDelete.simpleChunk c = true := by
            intro c mem
            exact simple c (List.mem_cons_of_mem _ mem)
          have tailEnough : rest.length ≤ n := by simpa using enough
          have chunkParse := FindAndDelete.simple_chunk_stable
            chunk head rest.flatten
          rw [List.flatten_cons]
          cases chunk with
          | nil => simp [FindAndDelete.simpleChunk] at head
          | cons op payload =>
              have parse : EncodedScript.parseOne
                  (op :: (payload ++ rest.flatten)) =
                    some (op :: payload, rest.flatten) := by
                simpa only [List.cons_append] using chunkParse
              simp [EncodedScript.parseChunks, parse,
                ih n tailSimple tailEnough]

private theorem residual_simple (ids : List (Fin 150)) :
    ∀ chunk ∈ residualChunks ids,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk mem
  exact List.all_eq_true.mp FindAndDelete.literal_simple_chunks chunk
    (List.mem_filter.mp mem).1

private theorem residual_length (ids : List (Fin 150)) :
    (residualChunks ids).length ≤ 880 := by
  exact (List.length_filter_le _ _).trans (by
    simp [EncodedLayout.chunks_length])

private theorem selected_short (ids : List (Fin 150)) :
    ∀ sig ∈ finalSignatureBytes ids, sig.length < 76 := by
  intro sig selected
  rcases List.mem_append.mp selected with dummy | nonce
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp dummy
    have all : ∀ j : Fin 150,
        (FinalSignedLoop.generatedDummyAt j).length < 76 := by decide
    exact all i
  · simp only [List.mem_singleton] at nonce
    subst sig
    decide

private theorem selected_patterns_core (ids : List (Fin 150)) :
    (finalSignatureBytes ids).map CorePushSerialize.pushPattern =
      selectedPatterns ids := by
  apply List.map_congr_left
  intro sig present
  exact CorePushSerialize.pushPattern_direct sig
    (selected_short ids sig present)

theorem residual_from_scriptCode (ids : List (Fin 150)) :
    EncodedScript.parseChunks 880
      (ScriptSigSighash.tenDeletedScript ids) =
        some (residualChunks ids) := by
  unfold ScriptSigSighash.tenDeletedScript
  rw [CorePushFindAndDelete.literal_many_pushes
    (finalSignatureBytes ids)]
  rw [selected_patterns_core]
  change EncodedScript.parseChunks 880 (residualChunks ids).flatten =
    some (residualChunks ids)
  exact parse_simple_chunks_fuel (residualChunks ids) 880
    (residual_simple ids) (residual_length ids)

theorem equal_scriptCode_equal_residual {left right : List (Fin 150)}
    (same : ScriptSigSighash.tenDeletedScript left =
      ScriptSigSighash.tenDeletedScript right) :
    residualChunks left = residualChunks right := by
  have parsed := congrArg (EncodedScript.parseChunks 880) same
  rw [residual_from_scriptCode, residual_from_scriptCode] at parsed
  exact Option.some.inj parsed

private theorem dummyPattern_injective : Function.Injective dummyPattern := by
  intro i j same
  apply FinalSignedLoop.generatedDummyAt_injective
  have payload := congrArg List.tail same
  simpa [dummyPattern, directPushPattern] using payload

private theorem dummyPattern_ne_nonce (i : Fin 150) :
    dummyPattern i ≠ noncePattern := by
  have all : ∀ j : Fin 150,
      dummyPattern j ≠ noncePattern := by decide
  exact all i

private theorem selectedPatterns_eq (ids : List (Fin 150)) :
    selectedPatterns ids = ids.map dummyPattern ++ [noncePattern] := by
  simp [selectedPatterns, finalSignatureBytes, dummyPattern,
    noncePattern, List.map_append, List.map_map]

private theorem dummyPattern_selected_iff (ids : List (Fin 150))
    (i : Fin 150) :
    dummyPattern i ∈ selectedPatterns ids ↔ i ∈ ids := by
  rw [selectedPatterns_eq]
  simp [List.mem_map_of_injective dummyPattern_injective,
    dummyPattern_ne_nonce]

private theorem dummyPattern_in_chunks (i : Fin 150) :
    dummyPattern i ∈ EncodedLayout.chunks := by
  have one := EncodedScript.final_pattern_one_chunk
    (dummyPattern i) (EncodedScript.generated_dummy_pattern_mem i)
  cases filtered : EncodedLayout.chunks.filter
      (· == dummyPattern i) with
  | nil => simp [filtered] at one
  | cons chunk rest =>
      have member : chunk ∈ EncodedLayout.chunks.filter
          (· == dummyPattern i) := by
        rw [filtered]
        exact List.mem_cons_self
      have exactPattern : chunk = dummyPattern i := by
        simpa using (List.mem_filter.mp member).2
      exact exactPattern ▸ (List.mem_filter.mp member).1

private theorem selectedPatterns_mem_iff_of_set_eq
    {left right : List (Fin 150)}
    (same : left.toFinset = right.toFinset) (pattern : Bytes) :
    pattern ∈ selectedPatterns left ↔
      pattern ∈ selectedPatterns right := by
  have indices : ∀ i : Fin 150, i ∈ left ↔ i ∈ right := by
    intro i
    have memEq := congrArg (fun s : Finset (Fin 150) => i ∈ s) same
    simpa using memEq
  rw [selectedPatterns_eq, selectedPatterns_eq]
  simp only [List.mem_append, List.mem_singleton, List.mem_map]
  constructor
  · rintro (⟨i, present, rfl⟩ | nonce)
    · exact Or.inl ⟨i, (indices i).mp present, rfl⟩
    · exact Or.inr nonce
  · rintro (⟨i, present, rfl⟩ | nonce)
    · exact Or.inl ⟨i, (indices i).mpr present, rfl⟩
    · exact Or.inr nonce

private theorem residual_eq_of_set_eq {left right : List (Fin 150)}
    (same : left.toFinset = right.toFinset) :
    residualChunks left = residualChunks right := by
  unfold residualChunks
  apply List.filter_congr
  intro chunk _
  by_cases present : chunk ∈ selectedPatterns left
  · have other := (selectedPatterns_mem_iff_of_set_eq same chunk).mp present
    simp [present, other]
  · have other : chunk ∉ selectedPatterns right := by
      intro h
      exact present ((selectedPatterns_mem_iff_of_set_eq same chunk).mpr h)
    simp [present, other]

private theorem scriptCode_eq_residual_flatten (ids : List (Fin 150)) :
    ScriptSigSighash.tenDeletedScript ids = (residualChunks ids).flatten := by
  unfold ScriptSigSighash.tenDeletedScript
  rw [CorePushFindAndDelete.literal_many_pushes
    (finalSignatureBytes ids)]
  rw [selected_patterns_core]
  rfl

/-- Equal source-shaped final scriptCodes on the literal lock force equal
selected dummy-position sets, even when lists repeat positions or use a
different order. This is about exact preimage bytes, not SHA256d digests. -/
theorem equal_scriptCode_equal_selected_set {left right : List (Fin 150)}
    (same : ScriptSigSighash.tenDeletedScript left =
      ScriptSigSighash.tenDeletedScript right) :
    left.toFinset = right.toFinset := by
  classical
  have residualEq := equal_scriptCode_equal_residual same
  ext i
  have residualMem :
      dummyPattern i ∈ residualChunks left ↔
        dummyPattern i ∈ residualChunks right := by
    rw [residualEq]
  have excluded :
      dummyPattern i ∉ selectedPatterns left ↔
        dummyPattern i ∉ selectedPatterns right := by
    simpa [residualChunks, dummyPattern_in_chunks i] using residualMem
  have indexExcluded : i ∉ left ↔ i ∉ right := by
    simpa only [dummyPattern_selected_iff] using excluded
  simpa using not_congr indexExcluded

/-- On the literal source-shaped lock, the final scriptCode is determined by
the set of selected dummy positions; deletion order and repeats do not add
distinct ALL messages. -/
theorem same_selected_set_equal_scriptCode {left right : List (Fin 150)}
    (same : left.toFinset = right.toFinset) :
    ScriptSigSighash.tenDeletedScript left =
      ScriptSigSighash.tenDeletedScript right := by
  rw [scriptCode_eq_residual_flatten, scriptCode_eq_residual_flatten,
    residual_eq_of_set_eq same]

theorem scriptCode_eq_iff_selected_set_eq
    {left right : List (Fin 150)} :
    ScriptSigSighash.tenDeletedScript left =
      ScriptSigSighash.tenDeletedScript right ↔
        left.toFinset = right.toFinset :=
  ⟨equal_scriptCode_equal_selected_set,
    same_selected_set_equal_scriptCode⟩

private theorem tenDeletedScript_width (ids : List (Fin 150)) :
    (ScriptSigSighash.tenDeletedScript ids).length < 256 ^ 8 := by
  have bounded := CoreFindAndDelete.runMany_length_le 880
    EncodedLayout.chunks.flatten
    ((finalSignatureBytes ids).map CorePushSerialize.pushPattern)
  have lockLength := EncodedLayout.script_length
  change (ScriptSigSighash.tenDeletedScript ids).length ≤
    EncodedLayout.chunks.flatten.length at bounded
  omega

/-- Distinct selected sets give distinct source-shaped ALL preimages for any
valid transaction and selected input. The hash may still collide. -/
theorem distinct_selected_sets_distinct_all_preimages
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    {left right : List (Fin 150)}
    (different : left.toFinset ≠ right.toFinset) :
    SighashAllWire.sourceAllPreimage tx selected
      (ScriptSigSighash.tenDeletedScript left) ≠
    SighashAllWire.sourceAllPreimage tx selected
      (ScriptSigSighash.tenDeletedScript right) := by
  intro same
  apply different
  exact equal_scriptCode_equal_selected_set
    (ScriptSigSighash.sourceAllPreimage_injective_scriptCode
      tx selected _ _ txValid selectedValid
      (tenDeletedScript_width left)
      (tenDeletedScript_width right) same)

/-- For a valid selected input, the source-shaped final ALL preimage has
exactly the same equality classes as selected dummy-position sets. This is
not a statement about SHA256d collision resistance or Core reachability. -/
theorem all_preimage_eq_iff_selected_set_eq
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    {left right : List (Fin 150)} :
    SighashAllWire.sourceAllPreimage tx selected
      (ScriptSigSighash.tenDeletedScript left) =
    SighashAllWire.sourceAllPreimage tx selected
      (ScriptSigSighash.tenDeletedScript right) ↔
      left.toFinset = right.toFinset := by
  constructor
  · intro same
    exact equal_scriptCode_equal_selected_set
      (ScriptSigSighash.sourceAllPreimage_injective_scriptCode
        tx selected _ _ txValid selectedValid
        (tenDeletedScript_width left)
        (tenDeletedScript_width right) same)
  · intro same
    rw [same_selected_set_equal_scriptCode same]

/-- Source-shaped FindAndDelete bytes for the fixed pin signature on the
literal 880-chunk lock. -/
def pinDeletedScript : Bytes :=
  CoreFindAndDelete.run 880 EncodedLayout.chunks.flatten
    FindAndDelete.pinPattern

private def pinResidualChunks : List Bytes :=
  EncodedLayout.chunks.filter (fun chunk =>
    chunk ∉ [FindAndDelete.pinPattern])

private theorem pin_residual_simple :
    ∀ chunk ∈ pinResidualChunks,
      FindAndDelete.simpleChunk chunk = true := by
  intro chunk present
  exact List.all_eq_true.mp FindAndDelete.literal_simple_chunks chunk
    (List.mem_filter.mp present).1

private theorem pin_residual_length :
    pinResidualChunks.length ≤ 880 := by
  exact (List.length_filter_le _ _).trans (by
    simp [EncodedLayout.chunks_length])

private theorem pin_residual_parse :
    EncodedScript.parseChunks 880 pinDeletedScript =
      some pinResidualChunks := by
  unfold pinDeletedScript
  rw [CoreFindAndDelete.pin_scriptCode_run]
  change EncodedScript.parseChunks 880 pinResidualChunks.flatten =
    some pinResidualChunks
  exact parse_simple_chunks_fuel pinResidualChunks 880
    pin_residual_simple pin_residual_length

private theorem nonce_pattern_in_chunks :
    noncePattern ∈ EncodedLayout.chunks := by decide

private theorem nonce_pattern_ne_pin :
    noncePattern ≠ FindAndDelete.pinPattern := by decide

/-- The fixed final nonce push survives pin-signature deletion but is
removed by every final multisignature deletion list. Thus even an empty or
repeated selected-index list cannot alias the pin scriptCode. -/
theorem pin_scriptCode_ne_final_scriptCode (ids : List (Fin 150)) :
    pinDeletedScript ≠ ScriptSigSighash.tenDeletedScript ids := by
  intro same
  have parsed := congrArg (EncodedScript.parseChunks 880) same
  rw [pin_residual_parse, residual_from_scriptCode] at parsed
  have residualEq := Option.some.inj parsed
  have inPin : noncePattern ∈ pinResidualChunks := by
    exact List.mem_filter.mpr ⟨nonce_pattern_in_chunks,
      by simp [nonce_pattern_ne_pin]⟩
  have notFinal : noncePattern ∉ residualChunks ids := by
    simp [residualChunks, selectedPatterns_eq]
  exact notFinal (residualEq ▸ inPin)

private theorem pinDeletedScript_width :
    pinDeletedScript.length < 256 ^ 8 := by
  have bounded := CoreFindAndDelete.run_length_le 880
    EncodedLayout.chunks.flatten FindAndDelete.pinPattern
  have lockLength := EncodedLayout.script_length
  change pinDeletedScript.length ≤ EncodedLayout.chunks.flatten.length
    at bounded
  omega

/-- On any valid selected input, the pin and final fixed-SIGHASH_ALL
source preimages are different for every final selected-index list. This
does not imply distinct SHA256d digests or distinct verification keys. -/
theorem pin_all_preimage_ne_final_all_preimage
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    (ids : List (Fin 150)) :
    SighashAllWire.sourceAllPreimage tx selected pinDeletedScript ≠
      SighashAllWire.sourceAllPreimage tx selected
        (ScriptSigSighash.tenDeletedScript ids) := by
  intro same
  exact pin_scriptCode_ne_final_scriptCode ids
    (ScriptSigSighash.sourceAllPreimage_injective_scriptCode
      tx selected _ _ txValid selectedValid
      pinDeletedScript_width (tenDeletedScript_width ids) same)

end QSB.FinalSubsetInjective
