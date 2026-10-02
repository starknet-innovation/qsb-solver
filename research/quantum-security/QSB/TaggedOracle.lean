import Mathlib

/-!
The two ideal hash functions can be represented by disjoint tags into one
uniform product-valued function. The unused output coordinate at each tag is
explicit: forgetting it has constant-size fibers, so it does not bias the
observed H/R pair. This is a finite-domain sampling fact, not a quantum-query
bound or a claim about concrete SHA-256 and RIPEMD-160.
-/
namespace QSB.TaggedOracle

variable {X Y Z : Type*}

/-- H sees the first coordinate of the left tag; R sees the second coordinate
of the right tag. The remaining coordinates are independent filler. -/
def observed (oracle : Sum X X → Y × Z) : (X → Y) × (X → Z) :=
  ((fun x => (oracle (.inl x)).1), (fun x => (oracle (.inr x)).2))

/-- Splitting a tagged oracle exposes both observed functions and the two
unused coordinates, without changing any response or identifying distinct
inputs from the two tags. -/
def splitEquiv : (Sum X X → Y × Z) ≃
    ((X → Y) × (X → Z)) × ((X → Z) × (X → Y)) where
  toFun oracle :=
    (observed oracle,
      ((fun x => (oracle (.inl x)).2),
       (fun x => (oracle (.inr x)).1)))
  invFun functions := fun input =>
    match input with
    | .inl x => (functions.1.1 x, functions.2.1 x)
    | .inr x => (functions.2.2 x, functions.1.2 x)
  left_inv := by
    intro oracle
    funext input
    cases input <;> simp [observed]
  right_inv := by
    intro functions
    rcases functions with ⟨⟨h, r⟩, ⟨fillerLeft, fillerRight⟩⟩
    rfl

theorem split_observed (oracle : Sum X X → Y × Z) :
    (splitEquiv oracle).1 = observed oracle := rfl

/-- Every prescribed H/R pair has exactly the same family of tagged-oracle
preimages, indexed by the two unused coordinate functions. -/
def observedFiberEquiv (functions : (X → Y) × (X → Z)) :
    {oracle : Sum X X → Y × Z // observed oracle = functions} ≃
      (X → Z) × (X → Y) where
  toFun oracle := (splitEquiv oracle.1).2
  invFun filler :=
    ⟨splitEquiv.symm (functions, filler), by
      change (splitEquiv (splitEquiv.symm (functions, filler))).1 = functions
      simp⟩
  left_inv := by
    intro oracle
    apply Subtype.ext
    change splitEquiv.symm (functions, (splitEquiv oracle.1).2) = oracle.1
    have observedEq : (splitEquiv oracle.1).1 = functions := oracle.property
    have pairEq : (functions, (splitEquiv oracle.1).2) =
        splitEquiv oracle.1 := Prod.ext observedEq.symm rfl
    calc
      splitEquiv.symm (functions, (splitEquiv oracle.1).2) =
          splitEquiv.symm (splitEquiv oracle.1) := congrArg splitEquiv.symm pairEq
      _ = oracle.1 := splitEquiv.symm_apply_apply oracle.1
  right_inv := by
    intro filler
    change (splitEquiv (splitEquiv.symm (functions, filler))).2 = filler
    simp

theorem observed_fiber_card [Fintype X] [Fintype Y] [Fintype Z]
    (functions : (X → Y) × (X → Z)) :
    Nat.card {oracle : Sum X X → Y × Z // observed oracle = functions} =
      Nat.card ((X → Z) × (X → Y)) :=
  Nat.card_congr (observedFiberEquiv functions)

/-- The equal fiber count multiplies by the number of observable pairs to
give the complete tagged-oracle count. Thus a uniformly sampled tagged
function induces the uniform law on H/R pairs in this finite ideal model. -/
theorem observed_fiber_times_pair_card [Fintype X] [Fintype Y] [Fintype Z]
    (functions : (X → Y) × (X → Z)) :
    Nat.card {oracle : Sum X X → Y × Z // observed oracle = functions} *
        Nat.card ((X → Y) × (X → Z)) =
      Nat.card (Sum X X → Y × Z) := by
  rw [observed_fiber_card]
  rw [Nat.card_congr splitEquiv]
  simp only [Nat.card_prod]
  ring

section QuerySimulation

/-- Fixed-width bit registers for the two ideal hash outputs. -/
abbrev Bits (width : Nat) := Fin width → Bool

def zeroBits (width : Nat) : Bits width := fun _ => false

def xorBits {width : Nat} (left right : Bits width) : Bits width :=
  fun i => left i != right i

theorem xorBits_zero_right {width : Nat} (value : Bits width) :
    xorBits value (zeroBits width) = value := by
  funext i
  simp [xorBits, zeroBits]

theorem xorBits_zero_left {width : Nat} (value : Bits width) :
    xorBits (zeroBits width) value = value := by
  funext i
  simp [xorBits, zeroBits]

theorem xorBits_self {width : Nat} (value : Bits width) :
    xorBits value value = zeroBits width := by
  funext i
  simp [xorBits, zeroBits]

theorem xorBits_twice {width : Nat} (value mask : Bits width) :
    xorBits (xorBits value mask) mask = value := by
  funext i
  cases valueBit : value i <;> cases maskBit : mask i <;>
    simp [xorBits, valueBit, maskBit]

/-- The standard XOR query to the product-valued tagged function. -/
def fullQuery {widthH widthR : Nat}
    (oracle : Sum X X → Bits widthH × Bits widthR)
    (input : Sum X X) (target : Bits widthH × Bits widthR) :
    Bits widthH × Bits widthR :=
  (xorBits target.1 (oracle input).1,
   xorBits target.2 (oracle input).2)

theorem fullQuery_twice {widthH widthR : Nat}
    (oracle : Sum X X → Bits widthH × Bits widthR)
    (input : Sum X X) (target : Bits widthH × Bits widthR) :
    fullQuery oracle input (fullQuery oracle input target) = target := by
  simp only [fullQuery, xorBits_twice]

/-- Query the product oracle into zero scratch, copy only the H-tag output
to the adversary's target, and query again to erase both scratch coordinates.
This is a computational-basis identity for the two-query circuit. -/
def simulateH {widthH widthR : Nat}
    (oracle : Sum X X → Bits widthH × Bits widthR)
    (input : X) (target : Bits widthH) :
    Bits widthH × (Bits widthH × Bits widthR) :=
  let scratch := fullQuery oracle (.inl input)
    (zeroBits widthH, zeroBits widthR)
  (xorBits target scratch.1, fullQuery oracle (.inl input) scratch)

theorem simulateH_correct {widthH widthR : Nat}
    (oracle : Sum X X → Bits widthH × Bits widthR)
    (input : X) (target : Bits widthH) :
    simulateH oracle input target =
      (xorBits target ((observed oracle).1 input),
        (zeroBits widthH, zeroBits widthR)) := by
  simp [simulateH, fullQuery, observed, xorBits_zero_left,
    xorBits_self]

/-- The corresponding R-tag circuit uses the same product oracle. -/
def simulateR {widthH widthR : Nat}
    (oracle : Sum X X → Bits widthH × Bits widthR)
    (input : X) (target : Bits widthR) :
    Bits widthR × (Bits widthH × Bits widthR) :=
  let scratch := fullQuery oracle (.inr input)
    (zeroBits widthH, zeroBits widthR)
  (xorBits target scratch.2, fullQuery oracle (.inr input) scratch)

theorem simulateR_correct {widthH widthR : Nat}
    (oracle : Sum X X → Bits widthH × Bits widthR)
    (input : X) (target : Bits widthR) :
    simulateR oracle input target =
      (xorBits target ((observed oracle).2 input),
        (zeroBits widthH, zeroBits widthR)) := by
  simp [simulateR, fullQuery, observed, xorBits_zero_left,
    xorBits_self]

end QuerySimulation

end QSB.TaggedOracle
