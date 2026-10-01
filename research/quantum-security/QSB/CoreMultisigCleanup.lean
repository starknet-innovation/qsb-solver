import QSB.CoreMultisigEval

/-!
The bottom-first stack cleanup at the end of Core 27.2's BASE
`OP_CHECKMULTISIG` source case. Once counts and pair scanning have completed,
Core pops the key/signature/count arguments, checks the extra dummy under
NULLDUMMY, pops it, then pushes the Boolean result. The pinned VERIFY_ALL
mask omits NULLFAIL, so a false first-round result follows the same cleanup.
The pair scan and compiled-C++ refinement remain separate obligations.
-/
namespace QSB.CoreMultisigCleanup
open ByteMachine

def parseSourceCount (bottom : List Bytes) (depth : Nat) : Option Int :=
  (CoreMultisigStack.stacktopNeg bottom depth).bind
    CoreScriptNum.coreSetVch

/-- `nKeys + nSigs + 3` cells comprise the two count cells, keys,
signatures, and the extra dummy. `stacktopNeg` uses Core's one-based address
from the bottom-first stack. -/
def cleanup (bottom : List Bytes) (nKeys nSigs : Nat)
    (result : Bool) : Option (List Bytes) :=
  let depth := CoreMultisigStack.sourceArgumentDepth nKeys nSigs
  if depth ≤ bottom.length then
    match CoreMultisigStack.stacktopNeg bottom depth with
    | some dummy =>
        if dummy.isEmpty then
          some (bottom.take (bottom.length - depth) ++ [boolBytes result])
        else none
    | none => none
  else none

/-- Under the source's successful count/capacity and NULLDUMMY checks,
Core's bottom-first cleanup is exactly the reverse of the byte model's
top-first `bool :: drop arguments` stack effect. This holds for either
Boolean result and arbitrary count values. -/
theorem cleanup_reverse (top : List Bytes) (nKeys nSigs : Nat)
    (result : Bool)
    (enough : CoreMultisigStack.sourceArgumentDepth nKeys nSigs ≤
      top.length)
    (empty : top[CoreMultisigStack.sourceArgumentDepth nKeys nSigs - 1]? =
      some []) :
    cleanup top.reverse nKeys nSigs result =
      some (boolBytes result ::
        top.drop (CoreMultisigStack.sourceArgumentDepth nKeys nSigs)).reverse := by
  let depth := CoreMultisigStack.sourceArgumentDepth nKeys nSigs
  have positive : 1 ≤ depth := by
    dsimp [depth, CoreMultisigStack.sourceArgumentDepth]
    omega
  have sourceDummy := CoreMultisigStack.stacktopNeg_reverse top depth
    ⟨positive, enough⟩
  have readDummy : CoreMultisigStack.stacktopNeg top.reverse depth =
      some [] := sourceDummy.trans empty
  have capacity : depth ≤ top.reverse.length := by simpa using enough
  have takePrefix : top.reverse.take (top.length - depth) =
      (top.drop depth).reverse := by
    exact List.reverse_drop.symm
  calc
    cleanup top.reverse nKeys nSigs result =
        some (top.reverse.take (top.length - depth) ++
          [boolBytes result]) := by
      change (if depth ≤ top.reverse.length then
        match CoreMultisigStack.stacktopNeg top.reverse depth with
        | some dummy =>
            if dummy.isEmpty then
              some (top.reverse.take (top.reverse.length - depth) ++
                [boolBytes result])
            else none
        | none => none
        else none) = _
      rw [if_pos capacity, readDummy]
      simp only [List.isEmpty_nil, ↓reduceIte,
        List.length_reverse]
    _ = some (boolBytes result :: top.drop depth).reverse := by
      rw [takePrefix]
      simp only [List.reverse_cons]

/-- A source-shaped successful cleanup forces the extra consumed cell to be
empty. The result shape then follows even when the scan returned false. -/
theorem cleanup_success (top : List Bytes) (nKeys nSigs : Nat)
    (result : Bool) (after : List Bytes)
    (success : cleanup top.reverse nKeys nSigs result = some after) :
    top[CoreMultisigStack.sourceArgumentDepth nKeys nSigs - 1]? =
        some [] ∧
      after = (boolBytes result ::
        top.drop (CoreMultisigStack.sourceArgumentDepth nKeys nSigs)).reverse := by
  let depth := CoreMultisigStack.sourceArgumentDepth nKeys nSigs
  have positive : 1 ≤ depth := by
    dsimp [depth, CoreMultisigStack.sourceArgumentDepth]
    omega
  have original := success
  change (if depth ≤ top.reverse.length then
    match CoreMultisigStack.stacktopNeg top.reverse depth with
    | some dummy =>
        if dummy.isEmpty then
          some (top.reverse.take (top.reverse.length - depth) ++
            [boolBytes result])
        else none
    | none => none
    else none) = some after at success
  by_cases enough : depth ≤ top.length
  · have sourceDummy := CoreMultisigStack.stacktopNeg_reverse top depth
      ⟨positive, enough⟩
    have capacity : depth ≤ top.reverse.length := by simpa using enough
    rw [if_pos capacity, sourceDummy] at success
    cases dummy : top[depth - 1]? with
    | none => simp [dummy] at success
    | some value =>
        cases value with
        | nil =>
          have emptyCell : top[depth - 1]? = some [] := dummy
          have shape := cleanup_reverse top nKeys nSigs result enough
            (by simpa [depth] using emptyCell)
          exact ⟨rfl,
            Option.some.inj (original.symm.trans shape)⟩
        | cons _ _ => simp [dummy] at success
  · have capacity : ¬depth ≤ top.reverse.length := by simpa using enough
    rw [if_neg capacity] at success
    simp at success

/-- A true final ten-pair source evaluation supplies the exact capacity and
NULLDUMMY premises for Core's bottom-first cleanup. The surviving underlying
stack is arbitrary; the pushed true Boolean becomes its new top. -/
theorem finalTenEval_cleanup (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (success : CoreMultisigEval.finalTenEval script checker top = some true) :
    cleanup top.reverse 10 10 true =
      some (boolBytes true :: top.drop 23).reverse := by
  obtain ⟨_keys, _sigs, dummy, enough⟩ :=
    CoreMultisigEval.finalTenEval_success_layout script checker top success
  simpa [CoreMultisigStack.sourceArgumentDepth] using
    cleanup_reverse top 10 10 true (by simpa [CoreMultisigStack.sourceArgumentDepth] using enough)
      (by simpa [CoreMultisigStack.sourceArgumentDepth] using dummy)

/-- The successful final source evaluator's literal count cells decode as ten
under Core's non-minimal ScriptNum parser, and its bottom-first cleanup has
the same resulting stack as the byte model. Only the ECDSA scan outcome and
compiled interpreter correspondence remain outside this structural step. -/
theorem finalTenEval_count_and_cleanup (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (success : CoreMultisigEval.finalTenEval script checker top = some true) :
    parseSourceCount top.reverse 1 = some 10 ∧
      parseSourceCount top.reverse 12 = some 10 ∧
      cleanup top.reverse 10 10 true =
        some (boolBytes true :: top.drop 23).reverse := by
  obtain ⟨keys, sigs, _dummy, enough⟩ :=
    CoreMultisigEval.finalTenEval_success_layout script checker top success
  obtain ⟨keyAddress, sigAddress, _dummyAddress, _pairs⟩ :=
    CoreMultisigStack.final_source_layout top enough
  have parsed : CoreScriptNum.coreSetVch [0x0a] = some 10 := by decide
  refine ⟨?_, ?_, finalTenEval_cleanup script checker top success⟩
  · simp [parseSourceCount, keyAddress, keys, parsed]
  · simp [parseSourceCount, sigAddress, sigs, parsed]

end QSB.CoreMultisigCleanup
