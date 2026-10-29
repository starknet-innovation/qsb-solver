import QSB.FiniteBranchingInputBound

/-!
For a fixed raw-cache machine input, every query actually issued in its
1697-fuel run can be represented in one finite tagged bit register. The
register width is existential because the finite-branching proof supplies no
numeric input-byte bound. The encoding retains the H/R tag and exact bytes.

The bound can depend on the complete fixed machine input, including its
scriptSig contract and any oracle advice there. It is not uniform over
adversarially varying raw inputs, does not cover eager dependency-list entries
that the machine did not request, and is not an efficient coherent circuit.
-/
namespace QSB.ActualQueryBitEncoding
open ByteMachine
open CausalQueryAlgorithm (Query Machine run)

/-- A tagged H/R request whose byte input fits a fixed cap. -/
abbrev BoundedQuery (bound : Nat) :=
  {query : Query // query.input.length ≤ bound}

/-- Restricting both H and R input domains to bounded bytes is exactly the
same as restricting the tagged query type. -/
def boundedQueryEquiv (bound : Nat) :
    BoundedQuery bound ≃
      Sum (BoundedInputEncoding.BoundedBytes bound)
        (BoundedInputEncoding.BoundedBytes bound) where
  toFun
    | ⟨.H bytes, bounded⟩ => .inl ⟨bytes, bounded⟩
    | ⟨.R bytes, bounded⟩ => .inr ⟨bytes, bounded⟩
  invFun input :=
    match input with
    | .inl bytes => ⟨.H bytes.1, bytes.2⟩
    | .inr bytes => ⟨.R bytes.1, bytes.2⟩
  left_inv := by
    intro ⟨query, bounded⟩
    cases query <;> rfl
  right_inv := by
    intro input
    cases input <;> rfl

/-- One tag bit, one-hot byte length, then the padded byte payload. -/
def encode {bound : Nat} (query : BoundedQuery bound) :
    TaggedOracle.Bits (1 + ((bound + 1) + bound * 8)) :=
  BoundedInputEncoding.taggedEncode (boundedQueryEquiv bound query)

theorem encode_injective {bound : Nat} :
    Function.Injective (encode (bound := bound)) := by
  intro left right same
  apply (boundedQueryEquiv bound).injective
  exact BoundedInputEncoding.taggedEncode_injective same

theorem encode_eq_iff {bound : Nat}
    (left right : BoundedQuery bound) :
    encode left = encode right ↔ left.1 = right.1 := by
  constructor
  · intro same
    exact congrArg Subtype.val (encode_injective same)
  · intro same
    exact congrArg encode (Subtype.ext same)

/-- For one fixed raw-cache input, choose the finite bound guaranteed for
every actual query in every oracle world. -/
structure FixedRawEncoding (p : WorldIndexedRawCacheMachine.FixedInput) where
  bound : Nat
  covers : ∀ functions : JointSourceChecks.Functions,
    ∀ entry ∈
      (run (WorldIndexedRawCacheMachine.machine p) functions 1697
        ([] : CheckedRunCacheMachine.Cache)).2,
      entry.1.input.length ≤ bound

noncomputable def fixedRawEncoding
    (p : WorldIndexedRawCacheMachine.FixedInput) : FixedRawEncoding p :=
  { bound := Classical.choose
      (FiniteBranchingInputBound.fixed_raw_machine_input_bound p)
    covers := Classical.choose_spec
      (FiniteBranchingInputBound.fixed_raw_machine_input_bound p) }

/-- Encode one actually requested query using the common bound for this
fixed raw-cache input. -/
noncomputable def encodeActual
    (p : WorldIndexedRawCacheMachine.FixedInput)
    (functions : JointSourceChecks.Functions)
    (entry : Query × Bytes)
    (member : entry ∈
      (run (WorldIndexedRawCacheMachine.machine p) functions 1697
        ([] : CheckedRunCacheMachine.Cache)).2) :
    TaggedOracle.Bits
      (1 + (((fixedRawEncoding p).bound + 1) +
        (fixedRawEncoding p).bound * 8)) :=
  encode ⟨entry.1, (fixedRawEncoding p).covers functions entry member⟩

/-- Across all oracle worlds, equal encodings of actual requests mean equal
tagged queries, and equal tagged queries have equal encodings. In particular,
an H request never aliases an R request in the finite register. -/
theorem encodeActual_eq_iff
    (p : WorldIndexedRawCacheMachine.FixedInput)
    (functions functions' : JointSourceChecks.Functions)
    (entry entry' : Query × Bytes)
    (member : entry ∈
      (run (WorldIndexedRawCacheMachine.machine p) functions 1697
        ([] : CheckedRunCacheMachine.Cache)).2)
    (member' : entry' ∈
      (run (WorldIndexedRawCacheMachine.machine p) functions' 1697
        ([] : CheckedRunCacheMachine.Cache)).2) :
    encodeActual p functions entry member =
      encodeActual p functions' entry' member' ↔ entry.1 = entry'.1 := by
  simp only [encodeActual, encode_eq_iff]

end QSB.ActualQueryBitEncoding
