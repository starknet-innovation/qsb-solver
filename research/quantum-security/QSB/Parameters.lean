import Mathlib.Data.Nat.Choose.Basic
import QSB.Game

/-! Concrete arithmetic, NOT security levels. Bonus counts presume exactly the
required distinct disclosed signed positions and disjoint distinct bonus sets.
Neither this file nor its arithmetic proves those properties of Bitcoin Script.
-/
namespace QSB

set_option maxRecDepth 3000

theorem configA_round1_bonus_choices : Nat.choose (150 - 8) 1 = 142 := by
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide
theorem configA_round2_bonus_choices : Nat.choose (150 - 7) 2 = 10153 := by
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide
theorem configA_pool_choices : Nat.choose 150 9 = 82947113349100 := by
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide

/-- If `d` distinct final-round positions have already been disclosed, the
number of abstract (covered signed seven-set, disjoint bonus two-set) choices
is C(d,7)*C(143,2). This counts choices only; it is not a puzzle-success bound,
and source extraction of the seven-plus-two shape remains open. -/
def coveredFinalChoices (d : Nat) : Nat :=
  Nat.choose d 7 * Nat.choose 143 2

theorem coveredFinalChoices_mono {d e : Nat} (h : d ≤ e) :
    coveredFinalChoices d ≤ coveredFinalChoices e := by
  unfold coveredFinalChoices
  exact Nat.mul_le_mul_right _ (Nat.choose_le_choose 7 h)

theorem coveredFinalChoices_zero : coveredFinalChoices 0 = 0 := by decide
theorem coveredFinalChoices_one_disclosure : coveredFinalChoices 7 = 10153 := by decide
theorem coveredFinalChoices_two_disjoint_disclosures :
    coveredFinalChoices 14 = 34845096 := by decide
theorem coveredFinalChoices_three_disjoint_disclosures :
    coveredFinalChoices 21 = 1180590840 := by decide

/-- A conservative upper bound after `r = history.length` releases. It counts
all signing records, even those for other vaults or rounds; a per-vault record
count gives a sharper version. It still says nothing about QROM success. -/
theorem coveredFinalChoices_after_history {Secret : Type*}
    (history : List (Game.Disclosure (Fin 150) Secret))
    (vault : Nat) (round : Fin 2)
    (each : ∀ d ∈ history, d.opened.card ≤ 7) :
    coveredFinalChoices (Game.disclosedAt history vault round).card ≤
      coveredFinalChoices (min 150 (7 * history.length)) := by
  apply coveredFinalChoices_mono
  simpa using Game.disclosedAt_card_le_min history vault round 7 each

/-- Count minimally encoded, nonnegative DER integers of a specified byte length.
Zero is included at length one, because syntax validity alone permits it.
For length >= 2: first byte 1..127, or leading 0 with the next byte >= 128. -/
def derIntegerCount : Nat → Nat
  | 0 => 0
  | 1 => 128
  | n + 2 => 127 * 256 ^ (n + 1) + 128 * 256 ^ n

/-- Count by the 24 possible nonempty integer-length pairs summing to 25,
multiplied by the 256 unconstrained sighash bytes. The combinatorial expression
is explicit; a bijection with a formal BIP66 parser has not yet been proved. -/
def der32Count : Nat :=
  ((List.range 24).map (fun i => derIntegerCount (i + 1) * derIntegerCount (24 - i))).sum * 256

/-- Syntactic DER target density exceeds 2^-46 and is below 2^-45.
This is arithmetic about the count expression, not a quantum adversary bound. -/
theorem der32_count_lower : 2 ^ 210 < der32Count := by decide
theorem der32_count_upper : der32Count < 2 ^ 211 := by decide

end QSB
