import QSB.Layout

/-!
The final bonus `OP_ROLL` has a sharper source boundary than the abstract
without-replacement model suggests. This file classifies the 153 cells reachable
at that opcode after the *canonical preceding trace*. The result is a local
stack fact; it is not arbitrary-witness source extraction. In particular, the
attacker may choose the earlier witness cells and indices differently.

The region is read immediately before instruction 849 of the exact generated
Config A program. Instruction 848 has already applied `OP_MIN` with cap 152.
The top is the clamped index; the following 153 cells are the potential source
of `OP_ROLL`. A successful roll requires a nonnegative index.
-/
namespace QSB.Bonus
open StackMachine

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def reachableRegion : List Cell :=
  [.atom 1157, .atom 1156, .atom 1155, .atom 1154,
   .atom 1153, .atom 1152, .atom 1151, .atom 1150,
   .atom 2002, .num 0] ++
  (List.range 142).map (fun i => .atom (1158 + i)) ++
  [.hash160 (.atom 157)]

/-- Exact generated symbolic trace, with the canonical first eight final-round
selections. This does not generalize those selections to arbitrary witnesses. -/
theorem canonical_region_matches_generated_program :
    (run (Layout.program.take 849)
      (State.mk Layout.witness [true, true, true, false, true, true] 0)).map
      (fun s => (s.stack.drop 1).take 153) = some reachableRegion := by
  decide

def cellAt (n : Nat) : Cell :=
  if n < 8 then .atom (1157 - n)
  else if n = 8 then .atom 2002
  else if n = 9 then .num 0
  else if n < 152 then .atom (1148 + n)
  else .hash160 (.atom 157)

/-- The full index range under the cap: 0..7 revisits gathered dummy
signatures, 8 reaches the fixed nonce signature, 9 the CHECKMULTISIG dummy,
10..151 unused dummy signatures, and 152 a HORS commitment. This is a
classification of stack *cells*, not a claim that all these choices pass Core. -/
theorem region_cell (n : Fin 153) :
    reachableRegion[n.val]? = some (cellAt n.val) := by
  decide +revert

theorem region_length : reachableRegion.length = 153 := by decide

theorem first_fresh_dummy : reachableRegion[10]? = some (.atom 1158) := by decide
theorem last_fresh_dummy : reachableRegion[151]? = some (.atom 1299) := by decide
theorem commitment_boundary :
    reachableRegion[152]? = some (.hash160 (.atom 157)) := by decide

/-- Replay the actual `OP_MIN; OP_ROLL` suffix against this region. The
preceding opcode has already fetched the raw index. -/
def selectFromRegion (raw : Int) : Option Cell :=
  (run [.push (.num 152), .min, .roll]
    (State.mk (.num raw :: reachableRegion) [] 0)).bind
    (fun s => s.stack.head?)

theorem bounded_select_role (n : Fin 153) :
    selectFromRegion n.val = some (cellAt n.val) := by
  decide +revert

theorem negative_index_rejected : selectFromRegion (-1) = none := by decide
theorem oversized_index_selects_commitment :
    selectFromRegion 153 = some (.hash160 (.atom 157)) := by decide

/-- Relative stack order after `OP_ROLL`, before later key rolls. -/
def rolledRegion (n : Nat) : List Cell :=
  match reachableRegion[n]? with
  | some x => x :: reachableRegion.eraseIdx n
  | none => []

/-- With the canonical first eight selections, revisiting any of the eight
gathered signatures, the fixed nonce signature, or the zero dummy shifts a
nonempty generated dummy signature into the prospective NULLDUMMY slot. The
later key rolls must still be shown to preserve this slot for arbitrary
witnesses; the Core boundary probes provide separate concrete evidence. -/
theorem nonfresh_shifts_nonzero_into_dummy_slot (n : Fin 10) :
    (rolledRegion n.val)[10]? = some (.atom 1158) := by
  decide +revert

theorem fresh_or_commitment_preserves_zero_dummy (n : Fin 153)
    (h : 10 ≤ n.val) :
    (rolledRegion n.val)[10]? = some (.num 0) := by
  decide +revert

end QSB.Bonus
