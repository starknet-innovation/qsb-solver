import QSB.ByteWitness
import QSB.BuilderWitnessPushBridge

/-!
A finite source-model scriptSig fixture for the disposable public
`ByteWitness.witness`. The byte machine stores its initial stack top first;
builder push order and the push-only evaluator's stack are bottom first.

This fixture classifies the two nine-cell index blocks as `number` tokens and
the other 39 cells as short `data` tokens. It is not the witness produced by
Python `cmd_assemble` for a real transaction, and it asserts no Python-byte
or compiled-Bitcoin-Core equivalence.
-/
namespace QSB.ByteWitnessPushFixture
open ByteMachine
open BuilderWitnessPushBridge
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- The disposable byte witness in builder push order. -/
def bottomCells : List Bytes := ByteWitness.witness.reverse

theorem bottomCells_length : bottomCells.length = 57 := by
  simp [bottomCells, ByteWitness.witness_length]

def cellAt (i : Fin 57) : Bytes :=
  bottomCells[i.val]'(by
    rw [bottomCells_length]
    exact i.isLt)

private theorem cellAt_short : ∀ i : Fin 57, (cellAt i).length < 76 := by
  decide

/-- Positions 18–26 and 46–54 are the reversed index sequences 10 down to 2;
all other positions are the fixture's data cells. -/
def tokenAt (i : Fin 57) : BuilderToken :=
  if _h : 18 ≤ i.val ∧ i.val < 27 then
    .number ⟨28 - i.val, by omega⟩
  else if _h : 46 ≤ i.val ∧ i.val < 55 then
    .number ⟨56 - i.val, by omega⟩
  else
    .data (cellAt i) (cellAt_short i)

def tokens : List BuilderToken := List.ofFn tokenAt

theorem tokens_length : tokens.length = 57 := by
  simp [tokens]

/-- The token values are precisely the disposable witness's bottom-first
cells, including both numeric index blocks. -/
theorem values_tokens : values tokens = ByteWitness.witness.reverse := by
  decide

/-- The finite fixture uses 39 direct-push length bytes, 18 small-number
opcodes, and 654 data payload bytes. -/
theorem encoded_length : (encodeTokens tokens).length = 711 := by
  decide

/-- Applying the generic source-level builder-token bridge yields exactly
the bottom-first fixture stack and one reached push event per token. -/
theorem execution_tokens_exact :
    PushOnlyScriptSig.execution (encodeTokens tokens) =
      (some ByteWitness.witness.reverse, 57) := by
  have size : (encodeTokens tokens).length ≤ 10000 := by
    rw [encoded_length]
    omega
  have capacity : tokens.length ≤ 1000 := by
    rw [tokens_length]
    omega
  have executed := BuilderWitnessPushBridge.execution_tokens tokens size capacity
  simpa only [values_tokens, tokens_length] using executed

theorem reached_length :
    (PushOnlyScriptSig.reached (encodeTokens tokens)).length = 57 := by
  simp [PushOnlyScriptSig.reached, execution_tokens_exact]

end QSB.ByteWitnessPushFixture
