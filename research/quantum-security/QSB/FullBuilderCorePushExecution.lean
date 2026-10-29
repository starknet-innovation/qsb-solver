import QSB.FullBuilderPushBridge
import QSB.CorePushEvalRefinement

/-!
For a source-shaped builder token list whose data cells are at most 520 bytes,
numeric depths are below 256, encoded script is at most 10,000 bytes, and
stack has at most 1,000 cells, the independent Core-shaped BASE push fragment
with `MINIMALDATA` disabled produces the exact ordered bottom-first cells and
one decoded push per token.

This composes two Lean source models. It does not identify the encoded bytes
with Python `cmd_assemble`, refine compiled Bitcoin Core, cover other
`EvalScript` opcodes, or prove whole-transaction `VerifyScript` acceptance.
-/
namespace QSB.FullBuilderCorePushExecution
open ByteMachine

theorem execution_tokens (tokens : List FullBuilderPushBridge.Token)
    (scriptSize :
      (FullBuilderPushBridge.encodeTokens tokens).length ≤ 10000)
    (stackCapacity : tokens.length ≤ 1000) :
    CorePushEvalRefinement.execution
      (FullBuilderPushBridge.encodeTokens tokens) =
      (some (FullBuilderPushBridge.values tokens), tokens.length) := by
  exact CorePushEvalRefinement.execution_success
    (FullBuilderPushBridge.encodeTokens tokens)
    (FullBuilderPushBridge.values tokens) tokens.length
    (FullBuilderPushBridge.execution_tokens tokens
      scriptSize stackCapacity)

end QSB.FullBuilderCorePushExecution
