import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
Core v27.2's legacy CHECKMULTISIG loop scans keys in order. A successful
signature advances both cursors; a failed comparison advances only the key
cursor. In the QSB final round the intended call is 10 signatures against
10 keys. If those counts and the final success are established from the real
stack, no key can have been skipped: each corresponding pair must verify.

`verify` can include DER and pubkey parsing plus ECDSA against the one
FindAndDelete scriptCode computed before Core's matching loop. This theorem is
about that loop only; it does not prove the real stack has the stated counts,
that the supplied predicate equals Core's checker, or that the scriptCode binds
the intended transaction fields.
-/
namespace QSB.Multisig

/-- Core's key-scanning success Boolean, abstracting the one-pair verifier. -/
def matchSigs {Sig Key : Type*} (verify : Sig → Key → Bool)
    (sigs : List Sig) : List Key → Bool
  | [] => sigs.isEmpty
  | key :: keys =>
      match sigs with
      | [] => true
      | sig :: rest =>
          if verify sig key then matchSigs verify rest keys
          else matchSigs verify sigs keys

theorem too_many_signatures_fail {Sig Key : Type*}
    (verify : Sig → Key → Bool) {sigs : List Sig} {keys : List Key}
    (more : keys.length < sigs.length) :
    matchSigs verify sigs keys = false := by
  induction keys generalizing sigs with
  | nil =>
      cases sigs with
      | nil => simp at more
      | cons sig rest => simp [matchSigs]
  | cons key keys ih =>
      cases sigs with
      | nil => simp at more
      | cons sig rest =>
          by_cases ok : verify sig key
          · have smaller : keys.length < rest.length := by simpa using more
            simp [matchSigs, ok, ih smaller]
          · have smaller : keys.length < (sig :: rest).length := by
              simp at more ⊢
              omega
            simp [matchSigs, ok, ih smaller]

/-- With equal counts, success entails verification of every corresponding
signature/key pair. A failed comparison cannot be repaired by skipping a key. -/
theorem equal_counts_success_iff_pairs {Sig Key : Type*}
    (verify : Sig → Key → Bool) {sigs : List Sig} {keys : List Key}
    (counts : sigs.length = keys.length) :
    matchSigs verify sigs keys = true ↔
      List.Forall₂ (fun sig key => verify sig key = true) sigs keys := by
  induction keys generalizing sigs with
  | nil =>
      cases sigs with
      | nil => simp [matchSigs]
      | cons sig rest => simp at counts
  | cons key keys ih =>
      cases sigs with
      | nil => simp at counts
      | cons sig rest =>
          have tailCounts : rest.length = keys.length := by simpa using counts
          by_cases ok : verify sig key
          · simp [matchSigs, ok, ih tailCounts]
          · have fail : matchSigs verify (sig :: rest) keys = false :=
              too_many_signatures_fail verify (by simp [tailCounts])
            simp [matchSigs, ok, fail]

end QSB.Multisig
