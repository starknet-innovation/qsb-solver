import QSB.BuilderWitnessPushBridge

/-!
A parameterized source model of the witness-construction loop in the pinned
`qsb_pipeline.py` `cmd_assemble`: round 2 is emitted before round 1, and each
round emits its two keys, reversed dummy public keys, reversed openings, and
reversed model-derived index depths. The pinning keys follow both rounds.

The supplied bytes and depths remain inputs. In particular this file does not
prove that Python's recovery or stack-model calculations produce them, that
Python emits the same bytes as `encodeTokens`, or that Bitcoin Core executes
those bytes according to this Lean evaluator.
-/
namespace QSB.BuilderWitnessRoleOrder
open ByteMachine BuilderWitnessPushBridge

abbrev ShortData := { bytes : Bytes // bytes.length < 76 }

def dataToken (data : ShortData) : BuilderToken :=
  .data data.val data.property

def dataTokens (data : List ShortData) : List BuilderToken :=
  data.map dataToken

def indexTokens (depths : List (Fin 256)) : List BuilderToken :=
  depths.map BuilderToken.number

structure RoundInputs where
  keyPuzzle : ShortData
  keyNonce : ShortData
  dummyPubkeys : List ShortData
  preimages : List ShortData
  indexDepths : List (Fin 256)

/-- Bottom-to-top tokens emitted for one round by the source-shaped builder. -/
def roundTokens (round : RoundInputs) : List BuilderToken :=
  [dataToken round.keyPuzzle, dataToken round.keyNonce] ++
  dataTokens round.dummyPubkeys.reverse ++
  dataTokens round.preimages.reverse ++
  indexTokens round.indexDepths.reverse

/-- The top-first cell view of one round after its pushes have executed. -/
def roundCellsTop (round : RoundInputs) : List Bytes :=
  round.indexDepths.map numberBytes ++
  round.preimages.map Subtype.val ++
  round.dummyPubkeys.map Subtype.val ++
  [round.keyNonce.val, round.keyPuzzle.val]

/-- Token order from the pinned `cmd_assemble` witness loop. -/
def scriptTokens (roundOne roundTwo : RoundInputs)
    (pinPuzzle pinNonce : ShortData) : List BuilderToken :=
  roundTokens roundTwo ++ roundTokens roundOne ++
  [dataToken pinPuzzle, dataToken pinNonce]

/-- Top-first stack, suitable for the existing `ByteMachine` initial-state
convention. -/
def scriptCellsTop (roundOne roundTwo : RoundInputs)
    (pinPuzzle pinNonce : ShortData) : List Bytes :=
  [pinNonce.val, pinPuzzle.val] ++
  roundCellsTop roundOne ++ roundCellsTop roundTwo

theorem roundTokens_values_reverse (round : RoundInputs) :
    (values (roundTokens round)).reverse = roundCellsTop round := by
  simp [values, roundTokens, roundCellsTop, dataTokens, indexTokens,
    dataToken, BuilderToken.value, List.map_append, List.map_map]

/-- Executing the builder-shaped pushes yields the exact top-first role order:
pin nonce, pin puzzle, first-round depths/openings/pubkeys/nonce/puzzle, then
second-round depths/openings/pubkeys/nonce/puzzle. -/
theorem scriptTokens_values_reverse
    (roundOne roundTwo : RoundInputs) (pinPuzzle pinNonce : ShortData) :
    (values (scriptTokens roundOne roundTwo pinPuzzle pinNonce)).reverse =
      scriptCellsTop roundOne roundTwo pinPuzzle pinNonce := by
  have first := roundTokens_values_reverse roundOne
  have second := roundTokens_values_reverse roundTwo
  simp only [values] at first second
  simp [values, scriptTokens, scriptCellsTop, List.map_append,
    List.reverse_append, dataToken, BuilderToken.value,
    first, second, List.append_assoc]

theorem roundTokens_length (round : RoundInputs) :
    (roundTokens round).length =
      2 + round.dummyPubkeys.length + round.preimages.length +
        round.indexDepths.length := by
  simp [roundTokens, dataTokens, indexTokens]
  omega

/-- Every permitted source-shaped token uses at most 76 serialized bytes. -/
theorem token_encode_length_le_76 (token : BuilderToken) :
    token.encode.length ≤ 76 := by
  cases token with
  | data bytes short =>
      simp [BuilderToken.encode, CorePushSerialize.pushPattern, short]
  | number n =>
      by_cases zero : n.val = 0
      · simp [BuilderToken.encode, zero]
      · by_cases small : n.val ≤ 16
        · simp [BuilderToken.encode, zero, small]
        · have short := numberBytes_short n
          simp [BuilderToken.encode, zero, small,
            CorePushSerialize.pushPattern, short]

theorem encodeTokens_length_le_76_times_count (tokens : List BuilderToken) :
    (encodeTokens tokens).length ≤ 76 * tokens.length := by
  induction tokens with
  | nil => simp [encodeTokens]
  | cons token rest ih =>
      have head := token_encode_length_le_76 token
      simp [encodeTokens, List.length_append] at ih ⊢
      omega

/-- Config A's 9 public keys and 9 index depths per round, with 8 then 7
preimages, yield 57 pushed cells. The length equalities are explicit premises. -/
theorem scriptTokens_length_configA
    (roundOne roundTwo : RoundInputs) (pinPuzzle pinNonce : ShortData)
    (pubOne : roundOne.dummyPubkeys.length = 9)
    (pubTwo : roundTwo.dummyPubkeys.length = 9)
    (preOne : roundOne.preimages.length = 8)
    (preTwo : roundTwo.preimages.length = 7)
    (idxOne : roundOne.indexDepths.length = 9)
    (idxTwo : roundTwo.indexDepths.length = 9) :
    (scriptTokens roundOne roundTwo pinPuzzle pinNonce).length = 57 := by
  simp [scriptTokens, roundTokens_length, pubOne, pubTwo,
    preOne, preTwo, idxOne, idxTwo]

/-- Under the source evaluator's resource limits, the builder-shaped byte
stream pushes exactly these 57 cells in the stated order. -/
theorem execution_configA
    (roundOne roundTwo : RoundInputs) (pinPuzzle pinNonce : ShortData)
    (pubOne : roundOne.dummyPubkeys.length = 9)
    (pubTwo : roundTwo.dummyPubkeys.length = 9)
    (preOne : roundOne.preimages.length = 8)
    (preTwo : roundTwo.preimages.length = 7)
    (idxOne : roundOne.indexDepths.length = 9)
    (idxTwo : roundTwo.indexDepths.length = 9) :
    PushOnlyScriptSig.execution
        (encodeTokens (scriptTokens roundOne roundTwo pinPuzzle pinNonce)) =
      (some (scriptCellsTop roundOne roundTwo pinPuzzle pinNonce).reverse, 57) := by
  have count := scriptTokens_length_configA roundOne roundTwo pinPuzzle pinNonce
    pubOne pubTwo preOne preTwo idxOne idxTwo
  have capacity :
      (scriptTokens roundOne roundTwo pinPuzzle pinNonce).length ≤ 1000 := by
    omega
  have sizeBound := encodeTokens_length_le_76_times_count
    (scriptTokens roundOne roundTwo pinPuzzle pinNonce)
  have scriptSize :
      (encodeTokens (scriptTokens roundOne roundTwo pinPuzzle pinNonce)).length ≤ 10000 := by
    omega
  rw [execution_tokens _ scriptSize capacity]
  rw [← List.reverse_reverse (values (scriptTokens roundOne roundTwo pinPuzzle pinNonce))]
  rw [scriptTokens_values_reverse]
  simp [count]

end QSB.BuilderWitnessRoleOrder
