import QSB.CoreGetOp

/-!
A second source-level model of Bitcoin Core v27.2's legacy
`FindAndDelete` (`src/script/interpreter.cpp` lines 228-255). It retains the
C++ loop's delayed copy: `pending` is the last opcode consumed by `GetOp`,
`kept` is the bytes already copied to `result`, and `found` records whether
a pattern was removed. This is a Lean control-flow model, not compiled-C++
refinement.
-/
namespace QSB.CoreFindAndDelete
open ByteMachine
open CoreGetOp

def loop : Nat → Bytes → Bytes → Bytes → Bytes → Bool → Bytes × Bool
  | 0, _, kept, pending, remaining, found =>
      (kept ++ pending ++ remaining, found)
  | fuel + 1, pattern, kept, pending, remaining, found =>
      let copied := kept ++ pending
      if remaining.take pattern.length = pattern then
        loop fuel pattern copied [] (remaining.drop pattern.length) true
      else
        match parse remaining with
        | some (chunk, rest) => loop fuel pattern copied chunk rest found
        | none => (copied ++ remaining, found)

/-- The delayed-copy loop and the direct recursive delete/parse loop emit
the same bytes at every fuel value. The empty pattern is excluded because
Core returns immediately before entering its loop in that case. -/
theorem loop_bytes_eq_scan (pattern : Bytes) (nonempty : pattern ≠ [])
    (fuel : Nat) (kept pending remaining : Bytes) (found : Bool) :
    (loop fuel pattern kept pending remaining found).1 =
      kept ++ pending ++ CoreGetOp.scan fuel remaining pattern := by
  induction fuel generalizing kept pending remaining found with
  | zero => simp [loop, CoreGetOp.scan, List.append_assoc]
  | succ fuel ih =>
      by_cases empty : remaining = []
      · subst remaining
        simp [loop, CoreGetOp.scan, parse, width, nonempty]
      · by_cases hit : remaining.take pattern.length = pattern
        · simp [loop, CoreGetOp.scan, empty, hit, ih, List.append_assoc]
        · cases parsed : parse remaining with
          | none =>
              simp [loop, CoreGetOp.scan, empty, hit, parsed,
                List.append_assoc]
          | some pair =>
              obtain ⟨chunk, rest⟩ := pair
              simp [loop, CoreGetOp.scan, empty, hit, parsed,
                ih, List.append_assoc]

private theorem parse_split (script chunk rest : Bytes)
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

private theorem loop_found_preserved (pattern : Bytes) (fuel : Nat)
    (kept pending remaining : Bytes) :
    (loop fuel pattern kept pending remaining true).2 = true := by
  induction fuel generalizing kept pending remaining with
  | zero => rfl
  | succ fuel ih =>
      simp only [loop]
      split
      · exact ih _ _ _
      · split
        · exact ih _ _ _
        · rfl

/-- If the delayed-copy loop reports no removal, its emitted bytes equal
the original concatenation of already-copied, pending, and remaining bytes.
This justifies Core's no-match branch that returns the original script. -/
theorem loop_no_match_preserves_bytes (pattern : Bytes) (fuel : Nat)
    (kept pending remaining : Bytes)
    (noMatch : (loop fuel pattern kept pending remaining false).2 = false) :
    (loop fuel pattern kept pending remaining false).1 =
      kept ++ pending ++ remaining := by
  induction fuel generalizing kept pending remaining with
  | zero => simp [loop, List.append_assoc]
  | succ fuel ih =>
      by_cases hit : remaining.take pattern.length = pattern
      · simp only [loop, hit, ↓reduceIte] at noMatch ⊢
        have found := loop_found_preserved pattern fuel
          (kept ++ pending) [] (remaining.drop pattern.length)
        simp [found] at noMatch
      · cases parsed : parse remaining with
        | none => simp [loop, hit, parsed, List.append_assoc]
        | some pair =>
            obtain ⟨chunk, rest⟩ := pair
            have splitBytes := parse_split remaining chunk rest parsed
            have later :
                (loop fuel pattern (kept ++ pending) chunk rest false).2 =
                  false := by simpa [loop, hit, parsed] using noMatch
            have result := ih (kept ++ pending) chunk rest later
            simp [loop, hit, parsed, result, List.append_assoc]
            exact splitBytes

def run (fuel : Nat) (script pattern : Bytes) : Bytes :=
  if pattern = [] then script
  else
    let (result, found) := loop fuel pattern [] [] script false
    if found then result else script

private theorem scan_empty_pattern (fuel : Nat) (script : Bytes) :
    CoreGetOp.scan fuel script [] = script := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      by_cases empty : script = []
      · simp [CoreGetOp.scan, empty]
      · simp [CoreGetOp.scan, empty, ih]

/-- The complete source-shaped delayed-copy model, including its early empty
pattern return and no-match return-original branch, has the same output as
the direct deletion model for every script, pattern, and fuel. -/
theorem run_eq_scan (fuel : Nat) (script pattern : Bytes) :
    run fuel script pattern = CoreGetOp.scan fuel script pattern := by
  by_cases empty : pattern = []
  · subst pattern
    simp [run, scan_empty_pattern]
  · have bytes := loop_bytes_eq_scan pattern empty fuel [] [] script false
    have noMatch := loop_no_match_preserves_bytes pattern fuel [] [] script
    cases outcome : loop fuel pattern [] [] script false with
    | mk result found =>
        cases found with
        | true => simpa [run, empty, outcome] using bytes
        | false =>
            have original : result = script := by
              simpa [outcome] using noMatch (by simp [outcome])
            have scanned : CoreGetOp.scan fuel script pattern = script := by
              simpa [outcome, original] using bytes.symm
            simp [run, empty, outcome, scanned]

theorem run_eq_model_scan (fuel : Nat) (script pattern : Bytes) :
    run fuel script pattern = FindAndDelete.scan fuel script pattern :=
  (run_eq_scan fuel script pattern).trans
    (CoreGetOp.scan_eq_model_scan_all fuel script pattern)

def runMany (fuel : Nat) (script : Bytes) : List Bytes → Bytes
  | [] => script
  | pattern :: rest => runMany fuel (run fuel script pattern) rest

theorem runMany_eq_model_scanMany (fuel : Nat) (script : Bytes)
    (patterns : List Bytes) :
    runMany fuel script patterns =
      FindAndDelete.scanMany fuel script patterns := by
  induction patterns generalizing script with
  | nil => rfl
  | cons pattern rest ih =>
      simp only [runMany, FindAndDelete.scanMany]
      rw [run_eq_model_scan, ih]

/-- The delayed-copy source model removes precisely the reached selected
signature pushes from the literal lock, for every selected index list. -/
theorem final_scriptCode_run (ids : List (Fin 150)) :
    runMany 880 EncodedLayout.chunks.flatten
      ((ScriptCodeSelection.finalSignatureBytes ids).map
        ScriptCodeSelection.directPushPattern) =
      EncodedScript.finalEncodedScriptCode ids := by
  rw [runMany_eq_model_scanMany]
  exact FindAndDelete.final_scriptCode_scan ids

/-- The delayed-copy source model removes the fixed pinning signature's
serialized push from the literal lock. -/
theorem pin_scriptCode_run :
    run 880 EncodedLayout.chunks.flatten FindAndDelete.pinPattern =
      ScriptCodeSelection.stripEncodedChunks [FindAndDelete.pinPattern]
        EncodedLayout.chunks := by
  rw [run_eq_model_scan]
  exact FindAndDelete.pin_scriptCode_scan

end QSB.CoreFindAndDelete
