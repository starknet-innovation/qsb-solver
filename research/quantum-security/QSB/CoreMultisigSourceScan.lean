import QSB.CoreMultisigCleanup

/-!
The source-shaped pair scan at an arbitrary reached `OP_CHECKMULTISIG` stack.
Core reads the count cells from its bottom-first stack, constructs one
`scriptCode` by deleting *all* reached signatures before attempting any
ECDSA pairs, then scans signatures and keys in top-first order. A scan may
return `some false`; a fatal encoding failure returns `none`. This is a Lean
model of the pinned source path, not a refinement of compiled Bitcoin Core.
-/
namespace QSB.CoreMultisigSourceScan
open ByteMachine

def reachedKeys (top : List Bytes) (nKeys : Nat) : List Bytes :=
  (top.drop 1).take nKeys

def reachedSignatures (top : List Bytes) (nKeys nSigs : Nat) :
    List Bytes :=
  (top.drop (nKeys + 2)).take nSigs

def deletedScript (script : Bytes) (top : List Bytes)
    (nKeys nSigs : Nat) : Bytes :=
  CoreFindAndDelete.runMany 880 script
    ((reachedSignatures top nKeys nSigs).map
      ScriptCodeSelection.directPushPattern)

/-- The generic source deletion specializes to the previously proved final
ten-signature scriptCode without changing the signature ordering. -/
theorem deletedScript_ten (script : Bytes) (top : List Bytes) :
    deletedScript script top 10 10 =
      CoreMultisigEval.deletedScript script top := by
  rfl

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

/-- At the generated final count and dummy cells, the generic source scan
agrees with the specialized ten-pair final evaluator, including fatal
encoding failures and a false scan result. -/
theorem scanAtStack_finalTen (script : Bytes)
    (checker : Bytes → Bytes → Bytes → Bool) (top : List Bytes)
    (keys : top[0]? = some [0x0a])
    (sigs : top[11]? = some [0x0a])
    (dummy : top[22]? = some [])
    (enough : 23 ≤ top.length) :
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
    deletedScript_ten, reachedSignatures, reachedKeys,
    FinalScriptCode.reachedSignatures]

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

end QSB.CoreMultisigSourceScan
