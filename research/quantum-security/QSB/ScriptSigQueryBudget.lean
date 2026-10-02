import Mathlib

/-!
Source-shaped hash-call accounting for a successful BASE `scriptSig` run in
Bitcoin Core 27.2. This is an event-trace theorem, not an extraction of such a
trace from compiled Core. In particular, a caller must justify that each
executed opcode and each reached multisignature key check is represented once.

`checksig` and `checkmultisig` charge the maximum two SHA-256 calls of a
legacy `SignatureHash` computation, even when an invalid signature or the
SIGHASH_SINGLE out-of-range case makes the actual cost smaller. SHA1 is an
unmodeled auxiliary primitive, not an H/R oracle call.
-/
namespace QSB.ScriptSigQueryBudget

/-- The relevant source-level cases in a successful BASE `EvalScript` trace.
`other` also covers counted opcodes in unexecuted conditional branches, if
those are included in a whole-script accounting trace. -/
inductive Event where
  | uncounted
  | other
  | sha1
  | sha256
  | ripemd160
  | hash160
  | hash256
  | checksig
  | checkmultisig (keys checks : Nat)
  deriving DecidableEq, Repr

/-- Core counts one opcode above `OP_16`; a reached CHECKMULTISIG also counts
its declared public keys. -/
def opCost : Event → Nat
  | .uncounted => 0
  | .checkmultisig keys _ => 1 + keys
  | _ => 1

/-- Maximum idealized SHA-256 oracle calls made by this event. -/
def hCost : Event → Nat
  | .sha256 | .hash160 => 1
  | .hash256 | .checksig => 2
  | .checkmultisig _ checks => 2 * checks
  | _ => 0

/-- Maximum idealized RIPEMD-160 oracle calls made by this event. -/
def rCost : Event → Nat
  | .ripemd160 | .hash160 => 1
  | _ => 0

/-- Each CHECKMULTISIG loop iteration advances one key cursor. -/
def valid : Event → Prop
  | .checkmultisig keys checks => checks ≤ keys
  | _ => True

theorem event_joint_le_twice_op (e : Event) (he : valid e) :
    hCost e + rCost e ≤ 2 * opCost e := by
  cases e <;> simp_all [valid, hCost, rCost, opCost]; omega

theorem trace_joint_le_twice_ops (events : List Event)
    (hv : ∀ e ∈ events, valid e) :
    (events.map hCost).sum + (events.map rCost).sum ≤
      2 * (events.map opCost).sum := by
  induction events with
  | nil => simp
  | cons e es ih =>
      have he : valid e := hv e (by simp)
      have hes : ∀ x ∈ es, valid x := by
        intro x hx
        exact hv x (by simp [hx])
      have head := event_joint_le_twice_op e he
      have tail := ih hes
      simp only [List.map_cons, List.sum_cons]
      omega

/-- With Core's independent 201-opcode cap for `scriptSig`, a successful
source-shaped trace costs at most 402 combined H/R calls. -/
theorem trace_joint_le_402 (events : List Event)
    (hv : ∀ e ∈ events, valid e)
    (hop : (events.map opCost).sum ≤ 201) :
    (events.map hCost).sum + (events.map rCost).sum ≤ 402 := by
  have h := trace_joint_le_twice_ops events hv
  omega

end QSB.ScriptSigQueryBudget
