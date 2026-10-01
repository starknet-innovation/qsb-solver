import QSB.ByteMachine
import QSB.CoreScriptNum

/-!
A source-shaped `OP_ROLL` relation. Core's stack vector is bottom-first;
`ByteMachine` represents the top at the head of a list. The theorems below
prove that selecting depth `n`, erasing that entry, and appending it to Core's
vector corresponds to selecting, erasing, and prepending in the byte model.
The raw-index theorem includes the four-byte ScriptNum conversion, negative
index rejection, and the byte model's opcode budget. This is a mathematical
translation of one opcode, not an equivalence proof for the compiled Core
interpreter, its transaction context, or an entire script.
-/

namespace QSB.CoreRoll

theorem eraseIdx_reverse_of_lt {α : Type} (xs : List α) (n : Nat)
    (hn : n < xs.length) :
    xs.reverse.eraseIdx (xs.length - 1 - n) = (xs.eraseIdx n).reverse := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [List.reverse_cons, List.eraseIdx_append_of_length_le]
    | succ n =>
      have hn' : n < xs.length := by simpa using hn
      have hidx : (x :: xs).length - 1 - (n + 1) = xs.length - 1 - n := by
        simp only [List.length_cons]
        omega
      rw [hidx, List.reverse_cons]
      rw [List.eraseIdx_append_of_lt_length (by simp only [List.length_reverse]; omega)]
      rw [ih n hn']
      simp

end QSB.CoreRoll

namespace QSB.CoreRoll

theorem getElem_reverse_at_depth {α : Type} (xs : List α) (n : Nat)
    (hn : n < xs.length) :
    xs.reverse[xs.length - 1 - n]? = xs[n]? := by
  have hi : xs.length - 1 - n < xs.length := by omega
  have hidx : xs.length - 1 - (xs.length - 1 - n) = n := by omega
  simpa [hidx] using List.getElem?_reverse (l := xs) (i := xs.length - 1 - n) hi

end QSB.CoreRoll

namespace QSB.CoreRoll
open QSB.ByteMachine

/-- Bottom-first list translation of Core's `stacktop(-n-1); erase; push_back`. -/
def coreRoll (stack : List Bytes) (n : Nat) : Option (List Bytes) := do
  if n ≥ stack.length then none else
    let offset := stack.length - 1 - n
    let x ← stack[offset]?
    some (stack.eraseIdx offset ++ [x])

def topRoll (stack : List Bytes) (n : Nat) : Option (List Bytes) := do
  let x ← stack[n]?
  some (x :: stack.eraseIdx n)

theorem coreRoll_reverse (stack : List Bytes) (n : Nat) :
    coreRoll stack.reverse n = (topRoll stack n).map List.reverse := by
  by_cases hn : n < stack.length
  · have hnot : ¬ stack.length ≤ n := Nat.not_le_of_gt hn
    simp only [coreRoll, topRoll, List.length_reverse, if_neg hnot]
    rw [getElem_reverse_at_depth stack n hn, eraseIdx_reverse_of_lt stack n hn]
    cases hget : stack[n]? with
    | none => simp
    | some x => simp [List.reverse_cons]
  · have hge : stack.length ≤ n := Nat.le_of_not_gt hn
    simp [coreRoll, topRoll, List.length_reverse, hge]

end QSB.CoreRoll

namespace QSB.CoreRoll

/-- Source-shaped numeric parsing followed by bottom-first selection. -/
def coreRollWithRaw (raw : List UInt8) (bottomStack : List QSB.ByteMachine.Bytes) :
    Option (List QSB.ByteMachine.Bytes) := do
  let value ← QSB.CoreScriptNum.coreSetVch raw
  if value < 0 then none else coreRoll bottomStack value.toNat

/-- The corresponding top-first byte operation, before accounting for cost. -/
def byteRollTop (raw : List UInt8) (topStack : List QSB.ByteMachine.Bytes) :
    Option (List QSB.ByteMachine.Bytes) := do
  let value ← QSB.ByteIndex.parseScriptNum raw
  if value < 0 then none else topRoll topStack value.toNat

theorem coreRollWithRaw_reverse (raw : List UInt8)
    (topStack : List QSB.ByteMachine.Bytes) :
    coreRollWithRaw raw topStack.reverse =
      (byteRollTop raw topStack).map List.reverse := by
  simp only [coreRollWithRaw, byteRollTop,
    QSB.CoreScriptNum.coreSetVch_eq_parseScriptNum]
  cases decoded : QSB.ByteIndex.parseScriptNum raw with
  | none => simp
  | some value =>
    by_cases neg : value < 0
    · simp [neg]
    · simp [neg, coreRoll_reverse]

end QSB.CoreRoll

namespace QSB.CoreRoll
open QSB.ByteMachine

theorem byteRollTop_eq_step_stack (hashes : Hashes) (raw : Bytes)
    (stack : List Bytes) (outcomes : List Bool) (ops : Nat)
    (budget : ops + 1 ≤ 201) :
    (step hashes .roll (State.mk (raw :: stack) outcomes ops)).map State.stack =
      byteRollTop raw stack := by
  have within : ¬ ops + 1 > 201 := by omega
  unfold step byteRollTop topRoll
  simp only [within, ↓reduceIte]
  cases parsed : ByteIndex.parseScriptNum raw with
  | none => simp
  | some value =>
    by_cases neg : value < 0
    · simp [neg]
    · simp [neg]

end QSB.CoreRoll

namespace QSB.CoreRoll
open QSB.ByteMachine

theorem source_roll_matches_byte_step (hashes : Hashes) (raw : Bytes)
    (stack : List Bytes) (outcomes : List Bool) (ops : Nat)
    (budget : ops + 1 ≤ 201) :
    coreRollWithRaw raw stack.reverse =
      (step hashes .roll (State.mk (raw :: stack) outcomes ops)).map
        (fun next => next.stack.reverse) := by
  rw [coreRollWithRaw_reverse]
  rw [← byteRollTop_eq_step_stack hashes raw stack outcomes ops budget]
  simp [Option.map_map, Function.comp_def]

end QSB.CoreRoll
