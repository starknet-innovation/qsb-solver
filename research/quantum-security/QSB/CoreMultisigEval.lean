import QSB.CoreMultisigStack
import QSB.CoreFindAndDelete
import QSB.CoreDEREncoding

/-!
A source-shaped final CHECKMULTISIG model for the generated BASE script under
the pinned VERIFY_ALL flags. The encoding gate may abort before ECDSA; an empty
signature passes that gate but cannot pass the ECDSA checker. All ten reached
signatures are deleted from one scriptCode before any pair is checked. This is
not a refinement of compiled Bitcoin Core or a real ECDSA implementation.
-/
namespace QSB.CoreMultisigEval
open ByteMachine

/-- Core's loop advances both cursors on a pair success and only the key
cursor on failure. If more signatures than keys remain, Core returns false
*before* attempting another encoding check. A failed encoding gate on an
actually attempted pair aborts the script. -/
def scan (encoding : Bytes → Bool) (verify : Bytes → Bytes → Bool) :
    List Bytes → List Bytes → Option Bool
  | [], _ => some true
  | _ :: _, [] => some false
  | sig :: sigs, key :: keys =>
      if (sig :: sigs).length > (key :: keys).length then some false
      else if encoding sig then
        if verify sig key then scan encoding verify sigs keys
        else scan encoding verify (sig :: sigs) keys
      else none

/-- A loop-internal state with too few keys exits without touching the next
signature. Core's initial `nSigsCount ≤ nKeysCount` check is separate. -/
theorem scan_early_failure (encoding : Bytes → Bool)
    (verify : Bytes → Bytes → Bool) (sigs keys : List Bytes)
    (more : keys.length < sigs.length) :
    scan encoding verify sigs keys = some false := by
  cases sigs with
  | nil => simp at more
  | cons sig rest =>
      cases keys with
      | nil => rfl
      | cons key tail =>
          have guard : tail.length < rest.length := by simpa using more
          simp [scan, guard]

/-- A malformed signature not reached after the first failed pair cannot
abort the script. The first signature is well-encoded but never verifies;
the second one would fail the encoding gate if Core attempted it. -/
theorem scan_skips_unreachable_malformed :
    scan (fun sig => sig == [1]) (fun _ _ => false)
      [[1], [2]] [[3], [4]] = some false := by decide

theorem scan_rejects_attempted_malformed :
    scan (fun sig => sig == [1]) (fun _ _ => false)
      [[2], [1]] [[3], [4]] = none := by decide

/-- A successful scan is a successful abstract Core key scan with the encoding
gate included in each attempted pair. -/
theorem scan_success_match (encoding : Bytes → Bool)
    (verify : Bytes → Bytes → Bool) (sigs keys : List Bytes)
    (success : scan encoding verify sigs keys = some true) :
    Multisig.matchSigs
      (fun sig key => encoding sig && verify sig key) sigs keys = true := by
  induction keys generalizing sigs with
  | nil =>
      cases sigs with
      | nil => rfl
      | cons sig rest => simp [scan] at success
  | cons key keys ih =>
      cases sigs with
      | nil => rfl
      | cons sig rest =>
          by_cases impossible : (sig :: rest).length > (key :: keys).length
          · have guard : keys.length < rest.length := by
              simpa using impossible
            simp [scan, guard] at success
          · by_cases encoded : encoding sig
            · by_cases verified : verify sig key
              · have next : scan encoding verify rest keys = some true := by
                  have guard : ¬ keys.length < rest.length := by
                    simpa using impossible
                  simpa [scan, guard, encoded, verified] using success
                simpa [Multisig.matchSigs, encoded, verified] using ih rest next
              · have next : scan encoding verify (sig :: rest) keys =
                    some true := by
                  have guard : ¬ keys.length < rest.length := by
                    simpa using impossible
                  simpa [scan, guard, encoded, verified] using success
                simpa [Multisig.matchSigs, encoded, verified] using
                  ih (sig :: rest) next
            · have guard : ¬ keys.length < rest.length := by
                simpa using impossible
              simp [scan, guard, encoded] at success

/-- The source transaction checker rejects an empty signature even though
`CheckSignatureEncoding` permits it as an invalid-check placeholder. -/
def nonemptyVerify (checker : Bytes → Bytes → Bytes → Bool)
    (scriptCode sig key : Bytes) : Bool :=
  !sig.isEmpty && checker sig key scriptCode

theorem nonemptyVerify_sound (checker : Bytes → Bytes → Bytes → Bool)
    (scriptCode sig key : Bytes)
    (success : nonemptyVerify checker scriptCode sig key = true) :
    sig ≠ [] ∧ checker sig key scriptCode = true := by
  cases sig with
  | nil => simp [nonemptyVerify] at success
  | cons b rest => simpa [nonemptyVerify] using success

/-- The source-shaped FindAndDelete loop removes each reached signature's
canonical direct-push pattern, in stack order, from the common scriptCode. -/
def deletedScript (script : Bytes) (top : List Bytes) : Bytes :=
  CoreFindAndDelete.runMany 880 script
    ((FinalScriptCode.reachedSignatures top).map
      ScriptCodeSelection.directPushPattern)

/-- This ten-pair source boundary checks the generated count cells and
argument-stack capacity, then the gated scan, then NULLDUMMY as in Core's
source order. Opcode budget and byte-run reachability are premises of the
surrounding generated-script theorems. -/
def finalTenEval (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool)
    (top : List Bytes) : Option Bool :=
  if top[0]? = some [0x0a] ∧ top[11]? = some [0x0a] ∧
      23 ≤ top.length then
    (scan DERSyntax.verifyAllEncoding
      (nonemptyVerify checker (deletedScript script top))
      (FinalScriptCode.reachedSignatures top) ((top.drop 1).take 10)).bind
        (fun result => if top[22]? = some [] then some result else none)
  else none

theorem finalTenEval_success_layout (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (success : finalTenEval script checker top = some true) :
    top[0]? = some [0x0a] ∧ top[11]? = some [0x0a] ∧
      top[22]? = some [] ∧ 23 ≤ top.length := by
  by_cases gate : top[0]? = some [0x0a] ∧
      top[11]? = some [0x0a] ∧ 23 ≤ top.length
  · by_cases dummy : top[22]? = some []
    · exact ⟨gate.1, gate.2.1, dummy, gate.2.2⟩
    · simp [finalTenEval, gate, dummy] at success
  · simp [finalTenEval, gate] at success

theorem finalTenEval_success_match (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (success : finalTenEval script checker top = some true) :
    Multisig.matchSigs
      (fun sig key => DERSyntax.verifyAllEncoding sig &&
        nonemptyVerify checker (deletedScript script top) sig key)
      (FinalScriptCode.reachedSignatures top)
      ((top.drop 1).take 10) = true := by
  by_cases gate : top[0]? = some [0x0a] ∧
      top[11]? = some [0x0a] ∧ 23 ≤ top.length
  · have dummy := (finalTenEval_success_layout script checker top success).2.2.1
    exact scan_success_match _ _ _ _
      (by simpa [finalTenEval, gate, dummy] using success)
  · simp [finalTenEval, gate] at success

/-- A successful pair in the source-shaped final scan has a nonempty strict-DER
signature. The arbitrary checker is responsible for the ECDSA result. -/
theorem checkedPair_der (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (sig key : Bytes)
    (success : (DERSyntax.verifyAllEncoding sig &&
      nonemptyVerify checker (deletedScript script top) sig key) = true) :
    CoreDEREncoding.valid sig = true ∧
      checker sig key (deletedScript script top) = true := by
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true] at success
  have parts := success
  obtain ⟨nonempty, verified⟩ :=
    nonemptyVerify_sound checker (deletedScript script top) sig key parts.2
  have strict := parts.1
  rw [DERSyntax.verifyAllEncoding_nonempty sig nonempty] at strict
  exact ⟨by rw [CoreDEREncoding.valid_eq_model]; exact strict, verified⟩

/-- Successful source-shaped final evaluation gives strict DER and a successful
checker result at every actual Core stack address, all against one deleted
scriptCode. This does not identify the checker with Core's compiled ECDSA. -/
theorem finalTenEval_success_pairs (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (success : finalTenEval script checker top = some true)
    (j : Fin 10) :
    ∃ sig key,
      CoreMultisigStack.signatureAt top.reverse 10 j.val = some sig ∧
      CoreMultisigStack.keyAt top.reverse j.val = some key ∧
      CoreDEREncoding.valid sig = true ∧
      checker sig key (deletedScript script top) = true := by
  have layout := finalTenEval_success_layout script checker top success
  obtain ⟨sig, key, sigAt, keyAt, pair⟩ :=
    CoreMultisigStack.matched_source_pair top layout.2.2.2
      (fun sig key => DERSyntax.verifyAllEncoding sig &&
        nonemptyVerify checker (deletedScript script top) sig key)
      (finalTenEval_success_match script checker top success) j
  obtain ⟨strict, verified⟩ :=
    checkedPair_der script checker top sig key pair
  exact ⟨sig, key, sigAt, keyAt, strict, verified⟩

/-- The source-shaped deletion loop equals the previously checked selected
scriptCode whenever the reached slots are those of a seven-plus-two trace. -/
theorem deletedScript_selected (top : List Bytes)
    (trace : List (Fin 150 × Bytes)) (a b : Fin 150)
    (h12 : top[12]? = some (FinalSignedLoop.generatedDummyAt b))
    (h13 : top[13]? = some (FinalSignedLoop.generatedDummyAt a))
    (signed : ∀ j : Nat, j < 7 → top[j + 14]? =
      (trace.map (fun p => FinalSignedLoop.generatedDummyAt p.1)).reverse[j]?)
    (h21 : top[21]? = some PoolRollInvariant.finalNonce)
    (seven : trace.length = 7) :
    deletedScript EncodedLayout.chunks.flatten top =
      EncodedScript.finalEncodedScriptCode (a :: b :: trace.map Prod.fst) := by
  unfold deletedScript
  rw [CoreFindAndDelete.runMany_eq_model_scanMany]
  exact FinalScriptCode.reached_scriptCode top trace a b
    h12 h13 signed h21 seven

/-- For an arbitrary initial byte stack, a successful generated byte run whose
reached final state passes the source-shaped ten-pair checker has seven actual
opening matches, two distinct bonus positions, the selected common scriptCode,
and ten nonempty DER-valid successful source-addressed pairs. Actual Core
acceptance must still be refined to the byte run and `finalTenEval`. -/
theorem successful_byte_run_source_check (hashes : Hashes)
    (initial final : State)
    (checker : Bytes → Bytes → Bytes → Bool)
    (accepted : run hashes ByteLayout.program initial = some final)
    (source : ∃ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      finalTenEval EncodedLayout.chunks.flatten checker
        beforeCheck.stack = some true) :
    ∃ (beforeCheck : State) (trace : List (Fin 150 × Bytes))
      (a b : Fin 150),
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck ∧
      trace.length = 7 ∧
      (∀ p ∈ trace,
        hashes.h160 p.2 = FinalSignedLoop.generatedCommitmentAt p.1) ∧
      (a :: b :: trace.map Prod.fst).Nodup ∧
      deletedScript EncodedLayout.chunks.flatten beforeCheck.stack =
        EncodedScript.finalEncodedScriptCode
          (a :: b :: trace.map Prod.fst) ∧
      (∀ j : Fin 10, ∃ sig key,
        CoreMultisigStack.signatureAt beforeCheck.stack.reverse 10 j.val =
          some sig ∧
        CoreMultisigStack.keyAt beforeCheck.stack.reverse j.val = some key ∧
        CoreDEREncoding.valid sig = true ∧
        checker sig key
          (deletedScript EncodedLayout.chunks.flatten beforeCheck.stack) =
            true) := by
  obtain ⟨pre, reached, checked⟩ := source
  let verify : Bytes → Bytes → Bool := fun sig key =>
    DERSyntax.verifyAllEncoding sig &&
      nonemptyVerify checker
        (deletedScript EncodedLayout.chunks.flatten pre.stack) sig key
  have sound : ∀ sig key, verify sig key = true →
      DERSyntax.valid sig = true := by
    intro sig key pair
    have der := (checkedPair_der EncodedLayout.chunks.flatten checker
      pre.stack sig key pair).1
    rwa [CoreDEREncoding.valid_eq_model] at der
  have matched : ∀ beforeCheck : State,
      run hashes (ByteLayout.program.take 879) initial = some beforeCheck →
      Multisig.matchSigs verify
        ((beforeCheck.stack.drop 12).take 10)
        ((beforeCheck.stack.drop 1).take 10) = true := by
    intro beforeCheck runBefore
    have same : beforeCheck = pre :=
      Option.some.inj (runBefore.symm.trans reached)
    subst beforeCheck
    exact finalTenEval_success_match EncodedLayout.chunks.flatten
      checker pre.stack checked
  obtain ⟨trace, a, b, beforeCheck, runBefore, h13, h12,
    signed, h21, _dummy, seven, hits, _different,
    _aAbsent, _bAbsent, distinct, _nine⟩ :=
    FinalBonusIndices.matched_full_run_nine_positions_der
      hashes initial final accepted verify sound matched
  have same : beforeCheck = pre :=
    Option.some.inj (runBefore.symm.trans reached)
  subst beforeCheck
  have code := deletedScript_selected pre.stack trace a b
    h12 h13 signed h21 seven
  exact ⟨pre, trace, a, b, reached, seven, hits, distinct, code,
    fun j => finalTenEval_success_pairs EncodedLayout.chunks.flatten
      checker pre.stack checked j⟩

end QSB.CoreMultisigEval
