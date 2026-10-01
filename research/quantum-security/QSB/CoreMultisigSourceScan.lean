import QSB.CoreMultisigCleanup
import QSB.CorePushSerialize
import QSB.CorePushFindAndDelete

/-!
The source-shaped pair scan at an arbitrary reached `OP_CHECKMULTISIG` stack.
Core reads the count cells from its bottom-first stack, constructs one
`scriptCode` by deleting *all* reached signatures before attempting any
ECDSA pairs, then scans signatures and keys in top-first order. A scan may
return `some false`; a fatal encoding failure returns `none`. This is a Lean
model of the pinned source path, not a refinement of compiled Bitcoin Core.
The deletion-loop fuel is 880 for the literal 880-opcode QSB lock supplied by
the extraction certificate; this definition does not claim complete deletion
for unrelated scripts with more than 880 opcodes.
-/
namespace QSB.CoreMultisigSourceScan
open ByteMachine
set_option maxRecDepth 5000
set_option maxHeartbeats 10000000

def reachedKeys (top : List Bytes) (nKeys : Nat) : List Bytes :=
  (top.drop 1).take nKeys

def reachedSignatures (top : List Bytes) (nKeys nSigs : Nat) :
    List Bytes :=
  (top.drop (nKeys + 2)).take nSigs

def deletedScript (script : Bytes) (top : List Bytes)
    (nKeys nSigs : Nat) : Bytes :=
  CoreFindAndDelete.runMany 880 script
    ((reachedSignatures top nKeys nSigs).map
      CorePushSerialize.pushPattern)

/-- On the literal lock, 880 iterations suffice for any reached signature
list: every canonical push pattern removes whole original opcode chunks, so
the resulting scriptCode is the corresponding chunk filter. -/
theorem deletedScript_literal (top : List Bytes) (nKeys nSigs : Nat) :
    deletedScript EncodedLayout.chunks.flatten top nKeys nSigs =
      ScriptCodeSelection.stripEncodedChunks
        ((reachedSignatures top nKeys nSigs).map
          CorePushSerialize.pushPattern) EncodedLayout.chunks := by
  exact CorePushFindAndDelete.literal_many_pushes
    (reachedSignatures top nKeys nSigs)

/-- The generic source deletion specializes to the existing final model if
each reached signature is short enough for a direct push. This premise must
not be assumed for the non-enforcing first round. -/
theorem deletedScript_ten (script : Bytes) (top : List Bytes)
    (short : ∀ sig ∈ reachedSignatures top 10 10, sig.length < 76) :
    deletedScript script top 10 10 =
      CoreMultisigEval.deletedScript script top := by
  have patterns :
      (reachedSignatures top 10 10).map CorePushSerialize.pushPattern =
        (reachedSignatures top 10 10).map
          ScriptCodeSelection.directPushPattern := by
    apply List.map_congr_left
    intro sig present
    exact CorePushSerialize.pushPattern_direct sig (short sig present)
  simpa [deletedScript, CoreMultisigEval.deletedScript,
    reachedSignatures, FinalScriptCode.reachedSignatures] using
    congrArg (CoreFindAndDelete.runMany 880 script) patterns

/-- The pair-scan component of the Core source path. Count bounds and
argument capacity precede the scan; opcode budget and NULLDUMMY belong to
the surrounding structural transition. -/
def scanAtStack (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool)
    (bottom : List Bytes) : Option Bool := do
  let n ← CoreMultisigCleanup.parseSourceCount bottom 1
  if n < 0 ∨ n > 20 then none else
  let m ← CoreMultisigCleanup.parseSourceCount bottom (n.toNat + 2)
  if m < 0 ∨ m > n then none else
  let top := bottom.reverse
  if n.toNat + m.toNat + 3 > top.length then none else
  CoreMultisigEval.scan DERSyntax.verifyAllEncoding
    (CoreMultisigEval.nonemptyVerify checker
      (deletedScript script top n.toNat m.toNat))
    (reachedSignatures top n.toNat m.toNat)
    (reachedKeys top n.toNat)

/-- Any nonfatal source-scan result has parsed, bounded counts and enough
actual stack cells. Its Boolean is exactly the scan over the reached byte
lists, using one scriptCode after deletion of *all* reached signatures,
whether or not the pair loop later inspects their encodings. -/
theorem scanAtStack_some (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool)
    (bottom : List Bytes) (result : Bool)
    (success : scanAtStack script checker bottom = some result) :
    ∃ n m : Int,
      CoreMultisigCleanup.parseSourceCount bottom 1 = some n ∧
      ¬(n < 0 ∨ n > 20) ∧
      CoreMultisigCleanup.parseSourceCount bottom (n.toNat + 2) = some m ∧
      ¬(m < 0 ∨ m > n) ∧
      n.toNat + m.toNat + 3 ≤ bottom.length ∧
      CoreMultisigEval.scan DERSyntax.verifyAllEncoding
        (CoreMultisigEval.nonemptyVerify checker
          (deletedScript script bottom.reverse n.toNat m.toNat))
        (reachedSignatures bottom.reverse n.toNat m.toNat)
        (reachedKeys bottom.reverse n.toNat) = some result := by
  unfold scanAtStack at success
  cases keys : CoreMultisigCleanup.parseSourceCount bottom 1 with
  | none => simp [keys] at success
  | some n =>
      by_cases badN : n < 0 ∨ n > 20
      · simp [keys, badN] at success
      · cases sigs : CoreMultisigCleanup.parseSourceCount bottom
            (n.toNat + 2) with
        | none => simp [keys, badN, sigs] at success
        | some m =>
            by_cases badM : m < 0 ∨ m > n
            · simp [keys, badN, sigs, badM] at success
            · by_cases short : n.toNat + m.toNat + 3 > bottom.reverse.length
              · have short' : n.toNat + m.toNat + 3 > bottom.length := by
                  simpa using short
                simp [keys, badN, sigs, badM, short'] at success
              · have facts : n.toNat + m.toNat + 3 ≤ bottom.length ∧
                    CoreMultisigEval.scan DERSyntax.verifyAllEncoding
                      (CoreMultisigEval.nonemptyVerify checker
                        (deletedScript script bottom.reverse
                          n.toNat m.toNat))
                      (reachedSignatures bottom.reverse n.toNat m.toNat)
                      (reachedKeys bottom.reverse n.toNat) =
                        some result := by
                  simpa [keys, badN, sigs, badM] using success
                exact ⟨n, m, rfl, badN, sigs, badM,
                  facts.1, facts.2⟩

/-- At the generated final count and dummy cells, the generic source scan
agrees with the specialized ten-pair final evaluator, including fatal
encoding failures and a false scan result. -/
theorem scanAtStack_finalTen (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (keys : top[0]? = some [0x0a])
    (sigs : top[11]? = some [0x0a])
    (dummy : top[22]? = some [])
    (enough : 23 ≤ top.length)
    (short : ∀ sig ∈ reachedSignatures top 10 10, sig.length < 76) :
    scanAtStack script checker top.reverse =
      CoreMultisigEval.finalTenEval script checker top := by
  obtain ⟨keyAddress, sigAddress, _dummyAddress, _pairs⟩ :=
    CoreMultisigStack.final_source_layout top enough
  have parsed : CoreScriptNum.coreSetVch [0x0a] = some 10 := by decide
  have parsedKeys : CoreMultisigCleanup.parseSourceCount top.reverse 1 =
      some 10 := by
    simp [CoreMultisigCleanup.parseSourceCount, keyAddress, keys, parsed]
  have parsedSigs : CoreMultisigCleanup.parseSourceCount top.reverse 12 =
      some 10 := by
    simp [CoreMultisigCleanup.parseSourceCount, sigAddress, sigs, parsed]
  simp [scanAtStack, parsedKeys, parsedSigs,
    CoreMultisigEval.finalTenEval, keys, sigs, enough, dummy,
    deletedScript_ten script top short, reachedSignatures, reachedKeys,
    FinalScriptCode.reachedSignatures]

/-- A true ten-of-ten generic scan necessarily attempts every signature.
Each reached signature is nonempty and strict DER, so its Core push pattern
is short; this is derived from the scan rather than assumed from the stack. -/
theorem scanAtStack_finalTen_true_all_short (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (keys : top[0]? = some [0x0a])
    (sigs : top[11]? = some [0x0a])
    (enough : 23 ≤ top.length)
    (success : scanAtStack script checker top.reverse = some true) :
    ∀ sig ∈ reachedSignatures top 10 10, sig.length < 76 := by
  obtain ⟨keyAddress, sigAddress, _, _⟩ :=
    CoreMultisigStack.final_source_layout top enough
  have parsed : CoreScriptNum.coreSetVch [0x0a] = some 10 := by decide
  have parsedKeys : CoreMultisigCleanup.parseSourceCount top.reverse 1 =
      some 10 := by
    simp [CoreMultisigCleanup.parseSourceCount, keyAddress, keys, parsed]
  have parsedSigs : CoreMultisigCleanup.parseSourceCount top.reverse 12 =
      some 10 := by
    simp [CoreMultisigCleanup.parseSourceCount, sigAddress, sigs, parsed]
  have capacity : ¬ 10 + 10 + 3 > top.length := by omega
  have scanTrue : CoreMultisigEval.scan DERSyntax.verifyAllEncoding
      (CoreMultisigEval.nonemptyVerify checker
        (deletedScript script top 10 10))
      (reachedSignatures top 10 10) (reachedKeys top 10) =
        some true := by
    simpa [scanAtStack, parsedKeys, parsedSigs, capacity] using success
  have sigLength : (reachedSignatures top 10 10).length = 10 := by
    simp [reachedSignatures, List.length_take, List.length_drop]
    omega
  have keyLength : (reachedKeys top 10).length = 10 := by
    simp [reachedKeys, List.length_take]
    omega
  have matched := CoreMultisigEval.scan_success_match
    DERSyntax.verifyAllEncoding
    (CoreMultisigEval.nonemptyVerify checker
      (deletedScript script top 10 10))
    (reachedSignatures top 10 10) (reachedKeys top 10) scanTrue
  have pairs := (Multisig.equal_counts_success_iff_pairs
    (fun sig key => DERSyntax.verifyAllEncoding sig &&
      CoreMultisigEval.nonemptyVerify checker
        (deletedScript script top 10 10) sig key)
    (by omega : (reachedSignatures top 10 10).length =
      (reachedKeys top 10).length)).mp matched
  have allShort (ss ks : List Bytes)
      (joined : List.Forall₂ (fun sig key =>
        (DERSyntax.verifyAllEncoding sig &&
          CoreMultisigEval.nonemptyVerify checker
            (deletedScript script top 10 10) sig key) = true) ss ks) :
      ∀ target ∈ ss, target.length < 76 := by
    induction joined with
    | nil => simp
    | @cons sig key restSigs restKeys pair more ih =>
        intro target member
        simp only [List.mem_cons] at member
        rcases member with rfl | remaining
        · have flags : DERSyntax.verifyAllEncoding target = true ∧
              CoreMultisigEval.nonemptyVerify checker
                (deletedScript script top 10 10) target key = true := by
            simpa only [Bool.and_eq_true_eq_eq_true_and_eq_true] using pair
          have nonempty := (CoreMultisigEval.nonemptyVerify_sound
            checker (deletedScript script top 10 10) target key flags.2).1
          have valid : DERSyntax.valid target = true := by
            rw [← DERSyntax.verifyAllEncoding_nonempty target nonempty]
            exact flags.1
          exact DERSyntax.valid_direct_push_width target valid
        · exact ih target remaining
  exact allShort _ _ pairs

/-- The specialized final evaluator's true result is also a true result of
the generic scanner using Core's full push serialization. The short-pattern
premise follows from strict DER; it is not assumed for an arbitrary stack. -/
theorem finalTenEval_success_generic_scan (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (success : CoreMultisigEval.finalTenEval script checker top = some true) :
    scanAtStack script checker top.reverse = some true := by
  obtain ⟨keys, sigs, dummy, enough⟩ :=
    CoreMultisigEval.finalTenEval_success_layout script checker top success
  have short : ∀ sig ∈ reachedSignatures top 10 10,
      sig.length < 76 := by
    simpa [reachedSignatures, FinalScriptCode.reachedSignatures] using
      CoreMultisigEval.finalTenEval_success_all_short script checker top success
  rw [scanAtStack_finalTen script checker top keys sigs dummy enough short]
  exact success

/-- The generic source scanner addresses Core's key and signature slots
for every reached pair index, including signatures deleted before the scan
but skipped by the key-matching loop. -/
theorem reached_slots (top : List Bytes) (nKeys nSigs j : Nat)
    (capacity : nKeys + nSigs + 3 ≤ top.length)
    (keyIndex : j < nKeys) (sigIndex : j < nSigs) :
    CoreMultisigStack.keyAt top.reverse j =
        (reachedKeys top nKeys)[j]? ∧
      CoreMultisigStack.signatureAt top.reverse nKeys j =
        (reachedSignatures top nKeys nSigs)[j]? := by
  have keyValid : 2 + j ≤ top.length := by omega
  have sigValid : nKeys + 3 + j ≤ top.length := by omega
  constructor
  · rw [CoreMultisigStack.keyAt_reverse top j keyValid]
    simp [reachedKeys, keyIndex, Nat.add_comm]
  · rw [CoreMultisigStack.signatureAt_reverse top nKeys j sigValid]
    simp [reachedSignatures, List.getElem?_drop, sigIndex]

/-- With two required signatures and two keys, an empty first signature is
well-encoded but cannot verify. The resulting impossible-to-match state
returns false before attempting the malformed second signature. -/
theorem skipped_malformed_returns_false :
    scanAtStack [] (fun _ _ _ => false)
      ([[2], [3], [4], [2], [], [1], []] : List Bytes).reverse =
        some false := by decide

/-- Moving the malformed signature to the first attempted slot is fatal. -/
theorem attempted_malformed_is_fatal :
    scanAtStack [] (fun _ _ _ => false)
      ([[2], [3], [4], [2], [1], [], []] : List Bytes).reverse =
        none := by decide

/-- On an isolated script containing a 76-byte push followed by DROP, the
full Core pattern deletes that push while the former direct-only pattern
does not. This is a concrete source-model witness to the repaired gap. -/
theorem long_push_deletion_counterexample :
    let longSig : Bytes := List.replicate 76 0x01
    let script := CorePushSerialize.pushPattern longSig ++ [0x75]
    CoreFindAndDelete.run 880 script
        (CorePushSerialize.pushPattern longSig) = [0x75] ∧
      CoreFindAndDelete.run 880 script
        (ScriptCodeSelection.directPushPattern longSig) = script := by
  decide

end QSB.CoreMultisigSourceScan
