import QSB.TaggedOracle

/-!
Linear lifting of the fixed-table tagged XOR query circuit to finite-support
complex amplitude states. The input, target, and scratch registers may be in
an arbitrary superposition, provided the scratch starts at zero. The circuit
uses a full tagged query, copies the observed coordinate, and uses the same
full tagged query to erase scratch. Each of its H and R programs contains two
full tagged queries.

This is a finite register circuit identity with a fixed oracle table. It does
not formalize oracle sampling inside a quantum experiment, adversarial
queries, compressed-oracle transitions, or a security reduction.
-/
namespace QSB.TaggedOracleLinearCircuit
open TaggedOracle

variable {X : Type*} {widthH widthR : Nat}

abbrev Scratch (widthH widthR : Nat) := Bits widthH × Bits widthR
abbrev HInput (X : Type*) (widthH : Nat) := X × Bits widthH
abbrev RInput (X : Type*) (widthR : Nat) := X × Bits widthR
abbrev HConfig (X : Type*) (widthH widthR : Nat) :=
  HInput X widthH × Scratch widthH widthR
abbrev RConfig (X : Type*) (widthH widthR : Nat) :=
  RInput X widthR × Scratch widthH widthR

/-- Put zero scratch next to an input/target basis state. -/
def initHBasis (basis : HInput X widthH) :
    HConfig X widthH widthR :=
  (basis, (zeroBits widthH, zeroBits widthR))

def initRBasis (basis : RInput X widthR) :
    RConfig X widthH widthR :=
  (basis, (zeroBits widthH, zeroBits widthR))

/-- One full tagged XOR query on the H-tag input and both scratch outputs. -/
def fullHBasis
    (oracle : Sum X X → Scratch widthH widthR)
    (basis : HConfig X widthH widthR) : HConfig X widthH widthR :=
  (basis.1, fullQuery oracle (.inl basis.1.1) basis.2)

/-- Copy the first scratch coordinate by XOR into the H target. -/
def copyHBasis (basis : HConfig X widthH widthR) :
    HConfig X widthH widthR :=
  ((basis.1.1, xorBits basis.1.2 basis.2.1), basis.2)

def fullRBasis
    (oracle : Sum X X → Scratch widthH widthR)
    (basis : RConfig X widthH widthR) : RConfig X widthH widthR :=
  (basis.1, fullQuery oracle (.inr basis.1.1) basis.2)

/-- Copy the second scratch coordinate by XOR into the R target. -/
def copyRBasis (basis : RConfig X widthH widthR) :
    RConfig X widthH widthR :=
  ((basis.1.1, xorBits basis.1.2 basis.2.2), basis.2)

def idealHBasis (oracle : Sum X X → Scratch widthH widthR)
    (basis : HInput X widthH) : HInput X widthH :=
  (basis.1, xorBits basis.2 ((observed oracle).1 basis.1))

def idealRBasis (oracle : Sum X X → Scratch widthH widthR)
    (basis : RInput X widthR) : RInput X widthR :=
  (basis.1, xorBits basis.2 ((observed oracle).2 basis.1))

/-- The basis circuit restores scratch and applies exactly the observed H
XOR query, even when the unused tagged response coordinate is nonzero. -/
theorem h_basis_circuit (oracle : Sum X X → Scratch widthH widthR)
    (basis : HInput X widthH) :
    fullHBasis oracle
      (copyHBasis (fullHBasis oracle (initHBasis basis))) =
      initHBasis (idealHBasis oracle basis) := by
  rcases basis with ⟨input, target⟩
  simp [fullHBasis, copyHBasis, initHBasis, idealHBasis,
    fullQuery, observed, xorBits_zero_left, xorBits_self]

theorem r_basis_circuit (oracle : Sum X X → Scratch widthH widthR)
    (basis : RInput X widthR) :
    fullRBasis oracle
      (copyRBasis (fullRBasis oracle (initRBasis basis))) =
      initRBasis (idealRBasis oracle basis) := by
  rcases basis with ⟨input, target⟩
  simp [fullRBasis, copyRBasis, initRBasis, idealRBasis,
    fullQuery, observed, xorBits_zero_left, xorBits_self]

noncomputable section

/-- Push amplitudes through a basis map. This is linear even if the basis map
is not injective; in the circuit below each actual gate is a permutation. -/
def lift {A B : Type*} (basisMap : A → B) :
    (A →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ basisMap

inductive Instruction where
  | fullQuery
  | copyObserved
  deriving DecidableEq

/-- Both projected-query simulations have this three-gate shape. -/
def program : List Instruction :=
  [.fullQuery, .copyObserved, .fullQuery]

theorem program_full_query_count :
    (program.filter (· == .fullQuery)).length = 2 := by decide

def hInstruction
    (oracle : Sum X X → Scratch widthH widthR) :
    Instruction →
      ((HConfig X widthH widthR →₀ ℂ) →ₗ[ℂ]
        (HConfig X widthH widthR →₀ ℂ))
  | .fullQuery => lift (fullHBasis oracle)
  | .copyObserved => lift copyHBasis

def rInstruction
    (oracle : Sum X X → Scratch widthH widthR) :
    Instruction →
      ((RConfig X widthH widthR →₀ ℂ) →ₗ[ℂ]
        (RConfig X widthH widthR →₀ ℂ))
  | .fullQuery => lift (fullRBasis oracle)
  | .copyObserved => lift copyRBasis

def runProgram {A : Type*}
    (gate : Instruction → (A →₀ ℂ) →ₗ[ℂ] (A →₀ ℂ)) :
    List Instruction → (A →₀ ℂ) →ₗ[ℂ] (A →₀ ℂ)
  | [] => LinearMap.id
  | first :: rest => (runProgram gate rest).comp (gate first)

/-- Linear operator for the three-gate H circuit. -/
def hCircuit (oracle : Sum X X → Scratch widthH widthR) :
    (HConfig X widthH widthR →₀ ℂ) →ₗ[ℂ]
      (HConfig X widthH widthR →₀ ℂ) :=
  runProgram (hInstruction oracle) program

def rCircuit (oracle : Sum X X → Scratch widthH widthR) :
    (RConfig X widthH widthR →₀ ℂ) →ₗ[ℂ]
      (RConfig X widthH widthR →₀ ℂ) :=
  runProgram (rInstruction oracle) program

def initHLinear : (HInput X widthH →₀ ℂ) →ₗ[ℂ]
    (HConfig X widthH widthR →₀ ℂ) :=
  lift initHBasis

def initRLinear : (RInput X widthR →₀ ℂ) →ₗ[ℂ]
    (RConfig X widthH widthR →₀ ℂ) :=
  lift initRBasis

def idealHLinear (oracle : Sum X X → Scratch widthH widthR) :
    (HInput X widthH →₀ ℂ) →ₗ[ℂ] (HInput X widthH →₀ ℂ) :=
  lift (idealHBasis oracle)

def idealRLinear (oracle : Sum X X → Scratch widthH widthR) :
    (RInput X widthR →₀ ℂ) →ₗ[ℂ] (RInput X widthR →₀ ℂ) :=
  lift (idealRBasis oracle)

/-- Exact coherent H simulation for arbitrary finite-support complex
amplitudes over input and target basis registers, with zero initial scratch. -/
theorem h_linear_circuit (oracle : Sum X X → Scratch widthH widthR)
    (amplitudes : HInput X widthH →₀ ℂ) :
    hCircuit oracle (initHLinear amplitudes) =
      initHLinear (idealHLinear oracle amplitudes) := by
  simp only [hCircuit, initHLinear, idealHLinear, program,
    runProgram, hInstruction, lift, LinearMap.comp_apply,
    LinearMap.id_apply, Finsupp.lmapDomain_apply]
  repeat rw [← Finsupp.mapDomain_comp]
  congr 1
  funext basis
  exact h_basis_circuit oracle basis

theorem r_linear_circuit (oracle : Sum X X → Scratch widthH widthR)
    (amplitudes : RInput X widthR →₀ ℂ) :
    rCircuit oracle (initRLinear amplitudes) =
      initRLinear (idealRLinear oracle amplitudes) := by
  simp only [rCircuit, initRLinear, idealRLinear, program,
    runProgram, rInstruction, lift, LinearMap.comp_apply,
    LinearMap.id_apply, Finsupp.lmapDomain_apply]
  repeat rw [← Finsupp.mapDomain_comp]
  congr 1
  funext basis
  exact r_basis_circuit oracle basis

/-- Equality of linear operators, not merely agreement on individual basis
states: H's full/copy/full circuit is the ideal projected H query on the
zero-scratch subspace. -/
theorem h_operator_eq (oracle : Sum X X → Scratch widthH widthR) :
    (hCircuit oracle).comp initHLinear =
      initHLinear.comp (idealHLinear oracle) := by
  apply LinearMap.ext
  intro amplitudes
  exact h_linear_circuit oracle amplitudes

theorem r_operator_eq (oracle : Sum X X → Scratch widthH widthR) :
    (rCircuit oracle).comp initRLinear =
      initRLinear.comp (idealRLinear oracle) := by
  apply LinearMap.ext
  intro amplitudes
  exact r_linear_circuit oracle amplitudes

end
end QSB.TaggedOracleLinearCircuit
