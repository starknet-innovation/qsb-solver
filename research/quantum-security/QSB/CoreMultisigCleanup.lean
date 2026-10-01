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

theorem parseSourceCount_reverse (top : List Bytes) (depth : Nat)
    (positive : 1 ≤ depth) (within : depth ≤ top.length) :
    parseSourceCount top.reverse depth =
      (top[depth - 1]?).bind ByteIndex.parseScriptNum := by
  rw [parseSourceCount,
    CoreMultisigStack.stacktopNeg_reverse top depth ⟨positive, within⟩]
  cases top[depth - 1]? with
  | none => rfl
  | some raw => exact CoreScriptNum.coreSetVch_eq_parseScriptNum raw

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

/-- Starting from the top-first cells read by the byte interpreter, Core's
one-based bottom-first addresses read the same two ScriptNum counts and the
same NULLDUMMY cell. The source cleanup then has the same stack result for
either scan Boolean. This is for arbitrary count encodings and underlying
stack cells; count bounds and the ECDSA scan are caller obligations. -/
theorem source_cells_from_byte_cells (rawN rawM : Bytes)
    (xs : List Bytes) (n m : Int) (result : Bool)
    (keyParsed : ByteIndex.parseScriptNum rawN = some n)
    (sigCell : xs[n.toNat]? = some rawM)
    (sigParsed : ByteIndex.parseScriptNum rawM = some m)
    (dummy : xs[n.toNat + 1 + m.toNat]? = some []) :
    parseSourceCount (rawN :: xs).reverse 1 = some n ∧
      parseSourceCount (rawN :: xs).reverse (n.toNat + 2) = some m ∧
      CoreMultisigStack.stacktopNeg (rawN :: xs).reverse
        (CoreMultisigStack.sourceArgumentDepth n.toNat m.toNat) = some [] ∧
      cleanup (rawN :: xs).reverse n.toNat m.toNat result =
        some (boolBytes result :: xs.drop (n.toNat + m.toNat + 2)).reverse := by
  have sigIndex : n.toNat < xs.length :=
    (List.getElem?_eq_some_iff.mp sigCell).choose
  have dummyIndex : n.toNat + 1 + m.toNat < xs.length :=
    (List.getElem?_eq_some_iff.mp dummy).choose
  have enoughSig : n.toNat + 2 ≤ (rawN :: xs).length := by
    simp only [List.length_cons]
    omega
  have enoughDummy :
      CoreMultisigStack.sourceArgumentDepth n.toNat m.toNat ≤
        (rawN :: xs).length := by
    dsimp [CoreMultisigStack.sourceArgumentDepth]
    omega
  have keySource := parseSourceCount_reverse (rawN :: xs) 1
    (by omega) (by simp)
  have sigSource := parseSourceCount_reverse (rawN :: xs)
    (n.toNat + 2) (by omega) enoughSig
  have dummySource := CoreMultisigStack.stacktopNeg_reverse
    (rawN :: xs)
    (CoreMultisigStack.sourceArgumentDepth n.toNat m.toNat)
    ⟨by simp [CoreMultisigStack.sourceArgumentDepth], enoughDummy⟩
  have dummyAt : (rawN :: xs)[CoreMultisigStack.sourceArgumentDepth
      n.toNat m.toNat - 1]? = some [] := by
    simpa [CoreMultisigStack.sourceArgumentDepth,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dummy
  refine ⟨?_, ?_, dummySource.trans dummyAt, ?_⟩
  · rw [keySource]
    simpa using keyParsed
  · rw [sigSource]
    have sigAt : (rawN :: xs)[n.toNat + 1]? = some rawM := by
      simpa using sigCell
    simp [sigAt, sigParsed]
  · have clean := cleanup_reverse (rawN :: xs) n.toNat m.toNat
      result enoughDummy dummyAt
    simpa [CoreMultisigStack.sourceArgumentDepth, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using clean

/-- Any successful byte-model CHECKMULTISIG transition, including a false
first-round result, reads the same count and NULLDUMMY cells under Core's
one-based bottom-first addresses and has the same cleanup stack. The Boolean
remains externally supplied by the byte model. -/
theorem successful_byte_multisig_source_cells (hashes : Hashes)
    (before after : ByteMachine.State)
    (executed : ByteMachine.step hashes .checkmultisig before = some after) :
    ∃ (n m : Int) (result : Bool),
      parseSourceCount before.stack.reverse 1 = some n ∧
      parseSourceCount before.stack.reverse (n.toNat + 2) = some m ∧
      cleanup before.stack.reverse n.toNat m.toNat result =
        some after.stack.reverse ∧
      before.outcomes = result :: after.outcomes ∧
      after.ops = before.ops + 1 + n.toNat := by
  cases before with
  | mk stack outcomes ops =>
    unfold ByteMachine.step at executed
    cases stack with
    | nil => simp at executed
    | cons rawN xs =>
      by_cases budget : ops + 1 > 201
      · simp [budget] at executed
      · cases parsedN : ByteIndex.parseScriptNum rawN with
        | none => simp [budget, parsedN] at executed
        | some n =>
          by_cases badN : n < 0 ∨ n > 20 ∨ ops + 1 + n.toNat > 201
          · simp [budget, parsedN, badN] at executed
          · cases sigCell : xs[n.toNat]? with
            | none =>
                simp [budget, parsedN, badN,
                  sigCell] at executed
            | some rawM =>
              cases parsedM : ByteIndex.parseScriptNum rawM with
              | none =>
                  simp [budget, parsedN, badN,
                    sigCell, parsedM] at executed
              | some m =>
                by_cases badM : m < 0 ∨ m > n
                · simp [budget, parsedN, badN,
                    sigCell, parsedM, badM] at executed
                · cases dummy : xs[n.toNat + 1 + m.toNat]? with
                  | none =>
                      simp [budget, parsedN, badN,
                        sigCell, parsedM, badM, dummy] at executed
                  | some dummyBytes =>
                    by_cases dummyBad : !dummyBytes.isEmpty
                    · have emptyValue : dummyBytes = [] := by
                        have parts := executed
                        simp [budget, parsedN, badN,
                          sigCell, parsedM, badM, dummy] at parts
                        exact parts.1
                      subst dummyBytes
                      simp at dummyBad
                    · cases outcomes with
                      | nil =>
                          simp [budget, parsedN] at executed
                      | cons result rest =>
                          have dummyEmpty : dummyBytes = [] := by
                            cases dummyBytes with
                            | nil => rfl
                            | cons _ _ => simp at dummyBad
                          subst dummyBytes
                          have cells := source_cells_from_byte_cells
                            rawN rawM xs n m result parsedN sigCell
                            parsedM dummy
                          have output : after =
                              { stack := boolBytes result ::
                                  xs.drop (n.toNat + m.toNat + 2),
                                outcomes := rest,
                                ops := ops + 1 + n.toNat } := by
                            have stepResult := executed
                            simp [budget, parsedN, badN,
                              sigCell, parsedM, badM, dummy]
                              at stepResult
                            exact stepResult.symm
                          subst after
                          exact ⟨n, m, result, cells.1, cells.2.1,
                            cells.2.2.2, rfl, rfl⟩

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
