import QSB.FinalBonusIndices

/-!
An opcode-level model of legacy signature-push removal from the literal
generated lock. Core's FindAndDelete operates on serialized script bytes at
opcode boundaries; a byte-faithful refinement to this model is still open.
The model records which final dummy-signature positions change scriptCode and
proves the result does not depend on the order of their ten deletions.
-/
namespace QSB.ScriptCodeSelection
open ByteMachine
open FinalSignedLoop

def stripSignaturePushes (signatures : List Bytes)
    (ops : List Op) : List Op :=
  ops.filter fun op =>
    match op with
    | .push bytes => if bytes ∈ signatures then false else true
    | _ => true

theorem stripSignaturePushes_perm (ops : List Op)
    {left right : List Bytes} (same : left.Perm right) :
    stripSignaturePushes left ops = stripSignaturePushes right ops := by
  unfold stripSignaturePushes
  congr 1
  funext op
  cases op <;> simp [same.mem_iff]

theorem stripSignaturePushes_cons (sig : Bytes)
    (rest : List Bytes) (ops : List Op) :
    stripSignaturePushes (sig :: rest) ops =
      stripSignaturePushes rest (stripSignaturePushes [sig] ops) := by
  unfold stripSignaturePushes
  rw [List.filter_filter]
  apply List.filter_congr
  intro op _
  cases op <;> simp [Bool.and_comm]

def finalSignatureBytes (ids : List (Fin 150)) : List Bytes :=
  ids.map generatedDummyAt ++ [PoolRollInvariant.finalNonce]

def finalScriptCode (ids : List (Fin 150)) : List Op :=
  stripSignaturePushes (finalSignatureBytes ids) ByteLayout.program

/-- In this opcode-level abstraction, permuting the selected original HORS
positions does not change the legacy scriptCode. This theorem does not assert
that Core's byte-level FindAndDelete equals `stripSignaturePushes`. -/
theorem finalScriptCode_perm {left right : List (Fin 150)}
    (same : left.Perm right) :
    finalScriptCode left = finalScriptCode right := by
  apply stripSignaturePushes_perm
  exact (same.map generatedDummyAt).append_right _

end QSB.ScriptCodeSelection
