import QSB.Layout

/-!
The first final-round bonus selection also reaches the first unselected HORS
commitment at its capped index 152 after canonical preceding signed selections.
The second bonus index is adjusted to 11 to select the remaining dummy that
the canonical witness would have selected. Signature outcomes are supplied
Booleans; the altered-lock Core test in `evidence/bonus-overshoot.json` checks
the DER-shaped source exception separately.
-/
namespace QSB.FirstBonus
open StackMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def firstBonusOvershootProbe : List Cell :=
  (Layout.witness.set 37 (.num 152)).set 38 (.num 11)

theorem first_bonus_overshoot_selects_commitment :
    (run (Layout.program.take 845)
      (State.mk firstBonusOvershootProbe
        [true, true, true, false, true, true] 0)).bind
      (fun s => s.stack.head?) = some (.hash160 (.atom 157)) := by
  decide

theorem first_bonus_overshoot_reaches_signature_slot :
    (run (Layout.program.take 879)
      (State.mk firstBonusOvershootProbe
        [true, true, true, false, true, true] 0)).bind
      (fun s => s.stack[13]?) = some (.hash160 (.atom 157)) := by
  decide

theorem first_bonus_overshoot_symbolic_trace_accepts :
    (run Layout.program
      (State.mk firstBonusOvershootProbe
        [true, true, true, false, true, true] 0)).map
      (fun s => finalTruth s && s.outcomes.isEmpty) = some true := by
  decide

end QSB.FirstBonus
