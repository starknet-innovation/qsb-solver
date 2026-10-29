import QSB.CertificateCandidateCausality

/-!
An eager dependency inventory for the two Boolean trials in the source-model
certificate search. The true trial is included even when the false trial
succeeds and search short-circuits. Each candidate inventory itself may list
work in a different order from the source evaluator. These are analytic
result-dependency theorems, not an effectful oracle machine or an operational
query transcript.

The lock, transaction, initial stack, key validator, and ECDSA predicate are
fixed across worlds. Oracle work hidden in those external values and compiled
Bitcoin Core remain outside this inventory.
-/
namespace QSB.CertificateSearchCausality
open ByteMachine
open CausalQueryAlgorithm (Query answer)

/-- Potential dependencies of both first-round candidates. -/
def searchDependencies (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) : List Query :=
  CertificateCandidateCausality.candidateDependencies functions tx selected
      lock stack false validKey ecdsa ++
    CertificateCandidateCausality.candidateDependencies functions tx selected
      lock stack true validKey ecdsa

/-- At most two 299-entry candidate inventories are needed. This count does
not bound hidden oracle calls in externally supplied functions. -/
theorem searchDependencies_length_le_598
    (functions : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool) :
    (searchDependencies functions tx selected lock stack validKey
      ecdsa).length ≤ 598 := by
  have hFalse := CertificateCandidateCausality.candidateDependencies_length_le_299
    functions tx selected lock stack false validKey ecdsa
  have hTrue := CertificateCandidateCausality.candidateDependencies_length_le_299
    functions tx selected lock stack true validKey ecdsa
  simp only [searchDependencies, List.length_append]
  omega

/-- Agreement on the eager inventory fixes the optional certificate chosen by
search, including its preference for the false first-round candidate. -/
theorem search_congr
    (functions functions' : JointSourceChecks.Functions)
    (tx : SighashAllWire.TxFields) (selected : Nat)
    (lock : DynamicCheckedCertificate.Lock) (stack : List Bytes)
    (validKey : Bytes → Bool)
    (ecdsa : Bytes → Bytes → Bytes → Bool)
    (agree : ∀ q ∈ searchDependencies functions tx selected lock stack
      validKey ecdsa, answer functions' q = answer functions q) :
    DynamicCheckedCertificate.search (JointSourceChecks.hashes functions')
      lock stack validKey
      (JointSourceChecks.checker functions' tx selected ecdsa) =
    DynamicCheckedCertificate.search (JointSourceChecks.hashes functions)
      lock stack validKey
      (JointSourceChecks.checker functions tx selected ecdsa) := by
  have falseAgree : ∀ q ∈
      CertificateCandidateCausality.candidateDependencies functions tx selected
        lock stack false validKey ecdsa,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [searchDependencies, mem])
  have trueAgree : ∀ q ∈
      CertificateCandidateCausality.candidateDependencies functions tx selected
        lock stack true validKey ecdsa,
      answer functions' q = answer functions q := by
    intro q mem
    exact agree q (by simp [searchDependencies, mem])
  have falseEq := CertificateCandidateCausality.candidate_congr
    functions functions' tx selected lock stack false validKey ecdsa falseAgree
  have trueEq := CertificateCandidateCausality.candidate_congr
    functions functions' tx selected lock stack true validKey ecdsa trueAgree
  unfold DynamicCheckedCertificate.search
  rw [falseEq, trueEq]

end QSB.CertificateSearchCausality
