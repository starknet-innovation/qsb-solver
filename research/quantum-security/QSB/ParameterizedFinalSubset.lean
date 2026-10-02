import QSB.ParameterizedFindAndDelete
import QSB.FinalSubsetInjective
import QSB.DynamicScriptLimits

/-!
Classify final signature deletions for a parameterized Config A lock. The
dummy pushes remain the deterministic generated Config A values, while pin,
nonce, and both commitment pools may vary. The fixed final nonce must not
alias a dummy signature push; its SIGHASH_ALL byte supplies this condition
because every generated dummy ends in SIGHASH_SINGLE.

This module concerns source-shaped FindAndDelete bytes, not actual Core
acceptance or SHA256d collision resistance.
-/
namespace QSB.ParameterizedFinalSubset
open ByteMachine ScriptCodeSelection
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def dummyPattern (i : Fin 150) : Bytes :=
  directPushPattern (FinalSignedLoop.generatedDummyAt i)

def noncePattern (nonce : Bytes) : Bytes :=
  CorePushSerialize.pushPattern nonce

def selectedPatterns (nonce : Bytes) (ids : List (Fin 150)) :
    List Bytes :=
  ((ids.map FinalSignedLoop.generatedDummyAt) ++ [nonce]).map
    CorePushSerialize.pushPattern

def residualChunks (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (ids : List (Fin 150)) : List Bytes :=
  (ParameterizedFindAndDelete.chunks pin nonce0 nonce1
    firstCommitment secondCommitment).filter
      (fun chunk => chunk ∉ selectedPatterns nonce1 ids)

def deletedScript (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (ids : List (Fin 150)) : Bytes :=
  CoreFindAndDelete.runMany 880
    (DynamicFullSerialized.fullWire pin nonce0 nonce1
      firstCommitment secondCommitment)
    (selectedPatterns nonce1 ids)

private theorem dummy_short (i : Fin 150) :
    (FinalSignedLoop.generatedDummyAt i).length < 76 := by
  have all : ∀ j : Fin 150,
      (FinalSignedLoop.generatedDummyAt j).length < 76 := by decide
  exact all i

private theorem dummy_core_pattern (i : Fin 150) :
    CorePushSerialize.pushPattern (FinalSignedLoop.generatedDummyAt i) =
      dummyPattern i := by
  exact CorePushSerialize.pushPattern_direct _ (dummy_short i)

private theorem selectedPatterns_eq (nonce : Bytes)
    (ids : List (Fin 150)) :
    selectedPatterns nonce ids =
      ids.map dummyPattern ++ [noncePattern nonce] := by
  simp [selectedPatterns, noncePattern, List.map_append,
    List.map_map, dummy_core_pattern, dummyPattern]

private theorem dummyPattern_injective : Function.Injective dummyPattern := by
  intro i j same
  apply FinalSignedLoop.generatedDummyAt_injective
  have payload := congrArg List.tail same
  simpa [dummyPattern, directPushPattern] using payload

private theorem dummyPattern_ne_nonce (nonce : Bytes)
    (nonceShort : nonce.length < 76)
    (nonceAll : nonce.getLast? = some 0x01)
    (i : Fin 150) :
    dummyPattern i ≠ noncePattern nonce := by
  intro same
  have nonceDirect := CorePushSerialize.pushPattern_direct nonce nonceShort
  have payload := congrArg List.tail same
  have sameBytes : FinalSignedLoop.generatedDummyAt i = nonce := by
    simpa [dummyPattern, noncePattern, nonceDirect,
      directPushPattern] using payload
  have last := congrArg List.getLast? sameBytes
  rw [ScriptCodeSelection.generatedDummyAt_sighash_single i,
    nonceAll] at last
  cases last

private theorem dummyPattern_selected_iff (nonce : Bytes)
    (nonceShort : nonce.length < 76)
    (nonceAll : nonce.getLast? = some 0x01)
    (ids : List (Fin 150)) (i : Fin 150) :
    dummyPattern i ∈ selectedPatterns nonce ids ↔ i ∈ ids := by
  rw [selectedPatterns_eq]
  simp [List.mem_map_of_injective dummyPattern_injective,
    dummyPattern_ne_nonce nonce nonceShort nonceAll i]

private theorem dummyPattern_in_chunks (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (i : Fin 150) :
    dummyPattern i ∈ ParameterizedFindAndDelete.chunks
      pin nonce0 nonce1 firstCommitment secondCommitment := by
  have pool : FinalSignedLoop.generatedDummyAt i ∈
      PoolRollInvariant.finalDummyPool := by
    exact List.getElem_mem (by
      rw [PoolRollInvariant.generated_dummy_pool_length]
      exact i.isLt)
  have pushed : FinalSignedLoop.generatedDummyAt i ∈
      PoolRollInvariant.finalDummyPushes := by
    simpa [PoolRollInvariant.finalDummyPool] using pool
  have data : FinalSignedLoop.generatedDummyAt i ∈
      DynamicSerializedRound.dataValues nonce1 secondCommitment := by
    simp [DynamicSerializedRound.dataValues, pushed]
  have encoded : CorePushSerialize.pushPattern
      (FinalSignedLoop.generatedDummyAt i) ∈
      (DynamicSerializedRound.dataValues nonce1 secondCommitment).map
        CorePushSerialize.pushPattern :=
    List.mem_map_of_mem data
  rw [dummy_core_pattern] at encoded
  simp only [ParameterizedFindAndDelete.chunks,
    DynamicWireSource.fullChunks,
    DynamicSerializedRound.chunks, List.mem_append]
  exact Or.inr (Or.inl encoded)

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

private theorem scriptCode_eq_residual_flatten (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (ids : List (Fin 150)) :
    deletedScript pin nonce0 nonce1 firstCommitment secondCommitment ids =
      (residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment ids).flatten := by
  exact ParameterizedFindAndDelete.runMany_eq_chunk_filter
    pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short
    (ids.map FinalSignedLoop.generatedDummyAt ++ [nonce1])

private theorem residual_parse (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (ids : List (Fin 150)) :
    EncodedScript.parseChunks 880
      (deletedScript pin nonce0 nonce1
        firstCommitment secondCommitment ids) =
      some (residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment ids) := by
  rw [scriptCode_eq_residual_flatten pin nonce0 nonce1
    firstCommitment secondCommitment firstWidth secondWidth
    pinShort nonce0Short nonce1Short ids]
  apply parse_simple_chunks_fuel
  · intro chunk present
    exact ParameterizedFindAndDelete.chunks_simple
      pin nonce0 nonce1 firstCommitment secondCommitment
      firstWidth secondWidth pinShort nonce0Short nonce1Short
      chunk (List.mem_filter.mp present).1
  · exact (List.length_filter_le _ _).trans (by
      rw [ParameterizedFindAndDelete.chunks_length])

private theorem selectedPatterns_mem_iff_of_set_eq (nonce : Bytes)
    {left right : List (Fin 150)}
    (same : left.toFinset = right.toFinset) (pattern : Bytes) :
    pattern ∈ selectedPatterns nonce left ↔
      pattern ∈ selectedPatterns nonce right := by
  have indices : ∀ i : Fin 150, i ∈ left ↔ i ∈ right := by
    intro i
    have memEq := congrArg (fun s : Finset (Fin 150) => i ∈ s) same
    simpa using memEq
  rw [selectedPatterns_eq, selectedPatterns_eq]
  simp only [List.mem_append, List.mem_singleton, List.mem_map]
  constructor
  · rintro (⟨i, present, rfl⟩ | nonceHit)
    · exact Or.inl ⟨i, (indices i).mp present, rfl⟩
    · exact Or.inr nonceHit
  · rintro (⟨i, present, rfl⟩ | nonceHit)
    · exact Or.inl ⟨i, (indices i).mpr present, rfl⟩
    · exact Or.inr nonceHit

/-- For any parameterized Config A lock with 20-byte commitments and short
fixed pushes, equal final source-shaped scriptCodes force equal selected
dummy-position sets when the fixed final nonce uses SIGHASH_ALL. Extra
occurrences of a dummy push elsewhere in the script do not invalidate the
argument: the whole original chunk list is recovered after deletion. -/
theorem equal_scriptCode_equal_selected_set
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (nonceAll : nonce1.getLast? = some 0x01)
    {left right : List (Fin 150)}
    (same : deletedScript pin nonce0 nonce1
      firstCommitment secondCommitment left =
      deletedScript pin nonce0 nonce1
        firstCommitment secondCommitment right) :
    left.toFinset = right.toFinset := by
  classical
  have parsed := congrArg (EncodedScript.parseChunks 880) same
  rw [residual_parse pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short left,
    residual_parse pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short right] at parsed
  have residualEq := Option.some.inj parsed
  ext i
  have residualMem :
      dummyPattern i ∈ residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment left ↔
      dummyPattern i ∈ residualChunks pin nonce0 nonce1
        firstCommitment secondCommitment right := by
    rw [residualEq]
  have excluded :
      dummyPattern i ∉ selectedPatterns nonce1 left ↔
      dummyPattern i ∉ selectedPatterns nonce1 right := by
    simpa [residualChunks,
      dummyPattern_in_chunks pin nonce0 nonce1
        firstCommitment secondCommitment i] using residualMem
  have indexExcluded : i ∉ left ↔ i ∉ right := by
    simpa only [dummyPattern_selected_iff nonce1 nonce1Short nonceAll]
      using excluded
  simpa using not_congr indexExcluded

/-- The selected position set also suffices for equality, regardless of
deletion order or duplicate indices. This direction does not need the ALL
flag: the nonce push is present in both pattern lists. -/
theorem same_selected_set_equal_scriptCode
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    {left right : List (Fin 150)}
    (same : left.toFinset = right.toFinset) :
    deletedScript pin nonce0 nonce1 firstCommitment secondCommitment left =
      deletedScript pin nonce0 nonce1 firstCommitment secondCommitment right := by
  rw [scriptCode_eq_residual_flatten pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short left,
    scriptCode_eq_residual_flatten pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short right]
  congr 1
  unfold residualChunks
  apply List.filter_congr
  intro chunk _
  by_cases present : chunk ∈ selectedPatterns nonce1 left
  · have other := (selectedPatterns_mem_iff_of_set_eq nonce1 same chunk).mp
      present
    simp [present, other]
  · have other : chunk ∉ selectedPatterns nonce1 right := by
      intro h
      exact present ((selectedPatterns_mem_iff_of_set_eq nonce1 same chunk).mpr h)
    simp [present, other]

/-- The parameterized source-shaped final scriptCode equality classes are
exactly the selected original dummy-position sets, under the fixed final
SIGHASH_ALL flag and serializer width premises. -/
theorem scriptCode_eq_iff_selected_set_eq
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (nonceAll : nonce1.getLast? = some 0x01)
    {left right : List (Fin 150)} :
    deletedScript pin nonce0 nonce1 firstCommitment secondCommitment left =
      deletedScript pin nonce0 nonce1 firstCommitment secondCommitment right ↔
    left.toFinset = right.toFinset := by
  exact ⟨equal_scriptCode_equal_selected_set pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short nonceAll,
    same_selected_set_equal_scriptCode pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short⟩

private theorem deletedScript_width
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (ids : List (Fin 150)) :
    (deletedScript pin nonce0 nonce1 firstCommitment secondCommitment
      ids).length < 256 ^ 8 := by
  have reduced := CoreFindAndDelete.runMany_length_le 880
    (DynamicFullSerialized.fullWire pin nonce0 nonce1
      firstCommitment secondCommitment)
    (selectedPatterns nonce1 ids)
  have bounded := (DynamicScriptLimits.full_wire_below_core_limit
    pin nonce0 nonce1 firstCommitment secondCommitment
    firstWidth secondWidth pinShort nonce0Short nonce1Short).1
  change (deletedScript pin nonce0 nonce1 firstCommitment
    secondCommitment ids).length ≤
      (DynamicFullSerialized.fullWire pin nonce0 nonce1
        firstCommitment secondCommitment).length at reduced
  omega

/-- At a valid selected input and fixed source transaction fields, the
parameterized final ALL *preimages* have exactly the selected dummy-set
equality classes. A SHA256d collision could still equate their digests. -/
theorem all_preimage_eq_iff_selected_set_eq
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (nonceAll : nonce1.getLast? = some 0x01)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (txValid : SighashAllWire.valid tx)
    (selectedValid : selected < tx.inputs.length)
    {left right : List (Fin 150)} :
    SighashAllWire.sourceAllPreimage tx selected
      (deletedScript pin nonce0 nonce1 firstCommitment secondCommitment
        left) =
    SighashAllWire.sourceAllPreimage tx selected
      (deletedScript pin nonce0 nonce1 firstCommitment secondCommitment
        right) ↔
    left.toFinset = right.toFinset := by
  constructor
  · intro same
    have codes := ScriptSigSighash.sourceAllPreimage_injective_scriptCode
      tx selected _ _ txValid selectedValid
      (deletedScript_width pin nonce0 nonce1 firstCommitment
        secondCommitment firstWidth secondWidth pinShort nonce0Short
        nonce1Short left)
      (deletedScript_width pin nonce0 nonce1 firstCommitment
        secondCommitment firstWidth secondWidth pinShort nonce0Short
        nonce1Short right) same
    exact equal_scriptCode_equal_selected_set pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short nonceAll codes
  · intro same
    rw [same_selected_set_equal_scriptCode pin nonce0 nonce1
      firstCommitment secondCommitment firstWidth secondWidth
      pinShort nonce0Short nonce1Short same]

/-- Original scriptSig bytes are erased by the source-shaped ALL serializer.
For two transactions equal after that erasure, the parameterized selected-set
classification persists even if their raw scriptSig programs differ. -/
theorem all_preimage_eq_iff_selected_set_eq_of_erased
    (pin nonce0 nonce1 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (nonce1Short : nonce1.length < 76)
    (nonceAll : nonce1.getLast? = some 0x01)
    (leftTx rightTx : SighashAllWire.TxFields) (selected : Nat)
    (leftValid : SighashAllWire.valid leftTx)
    (selectedValid : selected < leftTx.inputs.length)
    (sameErased : ScriptSigSighash.eraseScripts leftTx =
      ScriptSigSighash.eraseScripts rightTx)
    {left right : List (Fin 150)} :
    SighashAllWire.sourceAllPreimage leftTx selected
      (deletedScript pin nonce0 nonce1 firstCommitment secondCommitment
        left) =
    SighashAllWire.sourceAllPreimage rightTx selected
      (deletedScript pin nonce0 nonce1 firstCommitment secondCommitment
        right) ↔
    left.toFinset = right.toFinset := by
  have erased :=
    ScriptSigSighash.sourceAllPreimage_eq_of_erased_scripts_eq
      leftTx rightTx selected
      (deletedScript pin nonce0 nonce1 firstCommitment secondCommitment
        right) sameErased
  rw [← erased]
  exact all_preimage_eq_iff_selected_set_eq pin nonce0 nonce1
    firstCommitment secondCommitment firstWidth secondWidth
    pinShort nonce0Short nonce1Short nonceAll
    leftTx selected leftValid selectedValid

/-- The final nonce's ALL flag is necessary for the unrestricted-list
selected-set injectivity theorem.
If it equals a generated SINGLE dummy byte-for-byte, selecting that dummy
adds no new deletion pattern, so distinct selected sets produce the same
source-shaped scriptCode. This is outside the stated Config A nonce premise;
it is not a spend of the real lock. -/
theorem nonce_alias_counterexample
    (pin nonce0 : Bytes)
    (firstCommitment secondCommitment : Fin 150 → Bytes)
    (firstWidth : ∀ i, (firstCommitment i).length = 20)
    (secondWidth : ∀ i, (secondCommitment i).length = 20)
    (pinShort : pin.length < 76)
    (nonce0Short : nonce0.length < 76)
    (i : Fin 150) :
    deletedScript pin nonce0 (FinalSignedLoop.generatedDummyAt i)
      firstCommitment secondCommitment [] =
      deletedScript pin nonce0 (FinalSignedLoop.generatedDummyAt i)
        firstCommitment secondCommitment [i] ∧
    ([] : List (Fin 150)).toFinset ≠ ([i] : List (Fin 150)).toFinset := by
  have nonceShort := dummy_short i
  constructor
  · rw [scriptCode_eq_residual_flatten pin nonce0
        (FinalSignedLoop.generatedDummyAt i)
        firstCommitment secondCommitment firstWidth secondWidth
        pinShort nonce0Short nonceShort [],
      scriptCode_eq_residual_flatten pin nonce0
        (FinalSignedLoop.generatedDummyAt i)
        firstCommitment secondCommitment firstWidth secondWidth
        pinShort nonce0Short nonceShort [i]]
    congr 1
    unfold residualChunks
    apply List.filter_congr
    intro chunk _
    simp [selectedPatterns]
  · simp

end QSB.ParameterizedFinalSubset
