import QSB.ByteTrace
import QSB.FinalSignedChain

/-!
Identify the executable opening records for the seven generated final signed
blocks inside any successful literal byte-model run. This pins their program
source region, but does not yet attach the selected original pool indices to
the computed records or refine an accepted Core transaction to this run.
-/
namespace QSB.FinalOpeningTrace
open ByteMachine
open ByteTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def prefixOps : List Op := ByteLayout.program.take 749
def suffixOps : List Op := ByteLayout.program.drop 840

theorem literal_signed_split :
    ByteLayout.program =
      prefixOps ++ (FinalSignedChain.allSignedBlocks ++ suffixOps) := by
  decide

theorem prefix_paired : hashesPaired prefixOps = true := by decide
theorem signed_paired :
    hashesPaired FinalSignedChain.allSignedBlocks = true := by decide
theorem suffix_paired : hashesPaired suffixOps = true := by decide

theorem prefix_hash_count : hashCount prefixOps = 8 := by decide
theorem signed_hash_count :
    hashCount FinalSignedChain.allSignedBlocks = 7 := by decide
theorem suffix_hash_count : hashCount suffixOps = 0 := by decide

/-- Dropping the eight first-round records of any terminating literal run
leaves exactly the records computed while executing the seven final signed
blocks. The trailing bonus and signature opcodes contain no HASH160. -/
theorem literal_final_trace_is_signed_blocks (hashes : Hashes)
    (initial final : State) (trace : List (HashOpening hashes))
    (accepted : runOpenings hashes ByteLayout.program initial =
      some (final, trace)) :
    ∃ (beforeSigned afterSigned : State)
      (first signed : List (HashOpening hashes)),
      runOpenings hashes prefixOps initial = some (beforeSigned, first) ∧
      runOpenings hashes FinalSignedChain.allSignedBlocks beforeSigned =
        some (afterSigned, signed) ∧
      trace.drop 8 = signed ∧ signed.length = 7 := by
  rw [literal_signed_split, runOpenings_append] at accepted
  cases hprefix : runOpenings hashes prefixOps initial with
  | none => simp [hprefix] at accepted
  | some prefixValue =>
      rcases prefixValue with ⟨beforeSigned, first⟩
      simp only [hprefix, Option.bind_some] at accepted
      rw [runOpenings_append] at accepted
      cases hsigned : runOpenings hashes
          FinalSignedChain.allSignedBlocks beforeSigned with
      | none => simp [hsigned] at accepted
      | some signedValue =>
          rcases signedValue with ⟨afterSigned, signed⟩
          simp only [hsigned, Option.bind_some] at accepted
          cases hsuffix : runOpenings hashes suffixOps afterSigned with
          | none => simp [hsuffix] at accepted
          | some suffixValue =>
              rcases suffixValue with ⟨reached, last⟩
              simp [hsuffix] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              have firstLength : first.length = 8 := by
                have counted := runOpenings_length_of_paired hashes prefixOps
                  initial beforeSigned first prefix_paired hprefix
                simpa [prefix_hash_count] using counted
              have signedLength : signed.length = 7 := by
                have counted := runOpenings_length_of_paired hashes
                  FinalSignedChain.allSignedBlocks beforeSigned afterSigned
                  signed signed_paired hsigned
                simpa [signed_hash_count] using counted
              have lastLength : last.length = 0 := by
                have counted := runOpenings_length_of_paired hashes suffixOps
                  afterSigned reached last suffix_paired hsuffix
                simpa [suffix_hash_count] using counted
              have lastNil : last = [] := List.length_eq_zero_iff.mp lastLength
              subst last
              refine ⟨beforeSigned, afterSigned, first, signed,
                rfl, hsigned, ?_, signedLength⟩
              simp [firstLength]

/-- The public executable projection `finalSevenOpenings` is the opening
trace of the reached final signed-block segment, for any terminating run. -/
theorem extracted_seven_are_signed_blocks (hashes : Hashes)
    (initial final : State) (seven : List (HashOpening hashes))
    (extracted : finalSevenOpenings hashes initial = some (final, seven)) :
    ∃ beforeSigned afterSigned,
      runOpenings hashes FinalSignedChain.allSignedBlocks beforeSigned =
        some (afterSigned, seven) := by
  unfold finalSevenOpenings at extracted
  cases hrun : runOpenings hashes ByteLayout.program initial with
  | none => simp [hrun] at extracted
  | some value =>
      rcases value with ⟨reached, trace⟩
      simp [hrun] at extracted
      rcases extracted with ⟨rfl, rfl⟩
      obtain ⟨beforeSigned, afterSigned, _, signed, _, signedRun,
          traceEq, _⟩ :=
        literal_final_trace_is_signed_blocks hashes initial reached
          trace hrun
      rw [traceEq]
      exact ⟨beforeSigned, afterSigned, signedRun⟩

end QSB.FinalOpeningTrace
