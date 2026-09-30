import Mathlib.Data.List.Basic

/-!
A symbolic execution model for the opcodes emitted by Config A.

Terms represent byte strings and hash applications. Matching hash terms imply
matching bytes under any interpretation; the model does not assert that distinct
terms have distinct real hashes. Cryptographic signature outcomes are supplied
as a trace, not invented cryptographic axioms. A positive execution is conditional
on those outcomes being realizable. This model is used to check control/stack
behavior, NOT to declare a real SHA-256 puzzle solved.

ScriptNum byte parsing, signature encoding errors, pubkey parsing, element-byte
limits, and exact CHECKMULTISIG/F&D cryptographic evaluation are external to this
model. Its numeric constructors describe a canonical, well-formed witness.
-/
namespace QSB.StackMachine

inductive Cell where
  | num : Int → Cell
  | atom : Nat → Cell
  | hash160 : Cell → Cell
  | sha256 : Cell → Cell
  deriving DecidableEq, Repr

inductive Op where
  | push : Cell → Op
  | dup | over | swap | roll | min | add | hash160 | sha256 | equalverify
  | checksigverify | checkmultisig
  deriving DecidableEq, Repr

structure State where
  stack : List Cell
  outcomes : List Bool
  ops : Nat := 0
  deriving DecidableEq, Repr

def boolCell (b : Bool) : Cell := .num (if b then 1 else 0)

/-- Top-first stack. A failed precondition produces none. -/
def step (op : Op) (s : State) : Option State := do
  let cost := match op with | .push _ => 0 | _ => 1
  let s := { s with ops := s.ops + cost }
  if s.ops > 201 then none else
  match op, s.stack with
  | .push x, xs => some { s with stack := x :: xs }
  | .dup, x :: xs => some { s with stack := x :: x :: xs }
  | .over, x :: y :: xs => some { s with stack := y :: x :: y :: xs }
  | .swap, x :: y :: xs => some { s with stack := y :: x :: xs }
  | .roll, .num n :: xs =>
      if n < 0 then none else do
        let x ← xs[n.toNat]?
        some { s with stack := x :: xs.eraseIdx n.toNat }
  | .min, .num a :: .num b :: xs =>
      some { s with stack := .num (min a b) :: xs }
  | .add, .num a :: .num b :: xs =>
      some { s with stack := .num (a + b) :: xs }
  | .hash160, x :: xs => some { s with stack := .hash160 x :: xs }
  | .sha256, x :: xs => some { s with stack := .sha256 x :: xs }
  | .equalverify, x :: y :: xs =>
      if x = y then some { s with stack := xs } else none
  | .checksigverify, _pub :: _sig :: xs =>
      match s.outcomes with
      | true :: rest => some { s with stack := xs, outcomes := rest }
      | _ => none
  | .checkmultisig, .num n :: xs => do
      if n < 0 ∨ n > 20 ∨ s.ops + n.toNat > 201 then none else do
        let .num m ← xs[n.toNat]? | none
        if m < 0 ∨ m > n then none else do
          let .num 0 ← xs[n.toNat + 1 + m.toNat]? | none
          let b :: rest := s.outcomes | none
          some { stack := boolCell b :: xs.drop (n.toNat + m.toNat + 2),
                 outcomes := rest, ops := s.ops + n.toNat }
  | _, _ => none

def run : List Op → State → Option State
  | [], s => some s
  | op :: rest, s => do
      let s' ← step op s
      if s'.stack.length > 1000 then none else run rest s'

/-- Only applied to final stacks whose top is a Boolean from CHECKMULTISIG.
No CLEANSTACK policy assumption is added to this bare legacy script model. -/
def finalTruth (s : State) : Bool :=
  match s.stack with
  | .num n :: _ => n != 0
  | _ => false

end QSB.StackMachine
