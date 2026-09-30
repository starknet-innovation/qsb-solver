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
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

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

/-- In the literal generated lock, every final dummy ends with the legacy
SIGHASH_SINGLE flag. This says nothing about whether a particular transaction
triggers the out-of-range SINGLE behavior. -/
theorem generatedDummyAt_sighash_single (i : Fin 150) :
    (generatedDummyAt i).getLast? = some 0x03 := by
  have all : ∀ j : Fin 150,
      (generatedDummyAt j).getLast? = some 0x03 := by decide
  exact all i

/-- The fixed final nonce signature uses SIGHASH_ALL. -/
theorem finalNonce_sighash_all :
    PoolRollInvariant.finalNonce.getLast? = some 0x01 := by
  decide

theorem selected_final_signature_flags (ids : List (Fin 150)) :
    (ids.map generatedDummyAt).all
      (fun sig => sig.getLast? == some 0x03) = true ∧
    PoolRollInvariant.finalNonce.getLast? = some 0x01 := by
  constructor
  · simp [List.all_eq_true, generatedDummyAt_sighash_single]
  · exact finalNonce_sighash_all

def finalScriptCode (ids : List (Fin 150)) : List Op :=
  stripSignaturePushes (finalSignatureBytes ids) ByteLayout.program

/-- The exact byte pattern Core constructs for a signature shorter than 76
bytes. The direct-push size condition is a caller obligation. -/
def directPushPattern (sig : Bytes) : Bytes :=
  UInt8.ofNat sig.length :: sig

/-- A pattern match at an opcode boundary cannot extend into the following
opcode when the parsed opcode has the pattern's length. In the literal fixture,
all 151 selected patterns are direct pushes, so the length equality is checked
for every matching opcode by the source-fixture inventory. -/
theorem boundary_match_consumes_chunk (sig chunk suffix : Bytes)
    (sameLength : chunk.length = (directPushPattern sig).length)
    (isMatch : (chunk ++ suffix).take (directPushPattern sig).length =
      directPushPattern sig) :
    chunk = directPushPattern sig := by
  rw [← sameLength] at isMatch
  simpa using isMatch

/-- The byte-level output after filtering complete serialized opcodes. This
is not itself the Core parser; relating its chunks to Core's GetOp remains a
source-refinement obligation. -/
def stripEncodedChunks (patterns : List Bytes) (chunks : List Bytes) : Bytes :=
  (chunks.filter (fun chunk => chunk ∉ patterns)).flatten

theorem stripEncodedChunks_perm (chunks : List Bytes)
    {left right : List Bytes} (same : left.Perm right) :
    stripEncodedChunks left chunks = stripEncodedChunks right chunks := by
  unfold stripEncodedChunks
  congr 1
  apply List.filter_congr
  intro chunk _
  simp [same.mem_iff]

/-- In this opcode-level abstraction, permuting the selected original HORS
positions does not change the legacy scriptCode. This theorem does not assert
that Core's byte-level FindAndDelete equals `stripSignaturePushes`. -/
theorem finalScriptCode_perm {left right : List (Fin 150)}
    (same : left.Perm right) :
    finalScriptCode left = finalScriptCode right := by
  apply stripSignaturePushes_perm
  exact (same.map generatedDummyAt).append_right _

end QSB.ScriptCodeSelection
