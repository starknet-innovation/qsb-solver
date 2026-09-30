import QSB.ByteLayout

/-!
Execution-side extraction of the byte pairs consumed by OP_EQUALVERIFY. This
reads only the public starting stack and the generated locking script; it does
not look at private HORS setup state. A follow-up refinement must tie each
recorded commitment byte string to its locking-script source position and
each signature outcome to Core's byte-level checker.
-/
namespace QSB.ByteTrace
open ByteMachine

structure EqualPair where
  left : Bytes
  right : Bytes
  equal : left = right

structure HashOpening (hashes : Hashes) where
  opening : Bytes
  commitment : Bytes
  matched : hashes.h160 opening = commitment

def extractOpening (hashes : Hashes) (s : State) : Option (HashOpening hashes) :=
  match s.stack with
  | opening :: commitment :: _ =>
      if h : hashes.h160 opening = commitment then
        some { opening, commitment, matched := h }
      else none
  | _ => none

def comparedAt (op : Op) (s : State) : List EqualPair :=
  match op, s.stack with
  | .equalverify, x :: y :: _ =>
      if h : x = y then [{ left := x, right := y, equal := h }] else []
  | _, _ => []

def runCompared (hashes : Hashes) : List Op → State →
    Option (State × List EqualPair)
  | [], s => some (s, [])
  | op :: rest, s => do
      let pair := comparedAt op s
      let s' ← step hashes op s
      if s'.stack.length > 1000 then none else do
        let (final, tail) ← runCompared hashes rest s'
        some (final, pair ++ tail)

theorem forget_trace (hashes : Hashes) (ops : List Op) (s : State) :
    (runCompared hashes ops s).map Prod.fst = run hashes ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      simp only [runCompared, run]
      cases hstep : step hashes op s with
      | none => simp
      | some next =>
          by_cases large : next.stack.length > 1000
          · simp [large]
          · cases htail : runCompared hashes rest next with
            | none => simp [htail, ← ih]
            | some value =>
                rcases value with ⟨final, pairs⟩
                simp [large, htail, ← ih]

end QSB.ByteTrace
