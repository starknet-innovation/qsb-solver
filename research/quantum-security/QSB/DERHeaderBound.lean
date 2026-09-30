import QSB.DERSyntax
import QSB.RandomOracleSetup
import Mathlib

/-!
A conservative, fully counted subset of the strict DER setup analysis.
Uniform twenty-byte outputs are modeled as `Fin 20 → UInt8`. A valid DER
encoding fixes its first three bytes and restricts the fourth to 12 values.
The remaining 16 bytes are unrestricted in this bound. It deliberately leaves
the stricter S-tag/length and integer-leading-byte constraints for later work.
-/
namespace QSB.DERHeaderBound
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def Target : Finset (Fin 20 → UInt8) :=
  Finset.univ.filter (fun f => DERSyntax.valid (List.ofFn f) = true)

def Header (f : Fin 20 → UInt8) : Prop :=
  f ⟨0, by decide⟩ = 0x30 ∧
  f ⟨1, by decide⟩ = 0x11 ∧
  f ⟨2, by decide⟩ = 0x02 ∧
  1 ≤ (f ⟨3, by decide⟩).toNat ∧
  (f ⟨3, by decide⟩).toNat ≤ 12

theorem byte_ofFn (f : Fin 20 → UInt8) (i : Nat) (within : i < 20) :
    DERSyntax.byte (List.ofFn f) i = (f ⟨i, within⟩).toNat := by
  unfold DERSyntax.byte
  rw [List.getElem?_ofFn]
  simp [within]

theorem target_header {f : Fin 20 → UInt8} (hit : f ∈ Target) :
    Header f := by
  have valid : DERSyntax.valid (List.ofFn f) = true :=
    (Finset.mem_filter.mp (show f ∈ Finset.univ.filter
      (fun f => DERSyntax.valid (List.ofFn f) = true) from hit)).2
  obtain ⟨tag, total, rTag, pos, small, _, _⟩ :=
    DERSyntax.valid_twenty_byte_header (List.ofFn f)
      (by simp) valid
  unfold Header
  constructor
  · apply UInt8.toNat_inj.mp
    simpa [byte_ofFn] using tag
  constructor
  · apply UInt8.toNat_inj.mp
    simpa [byte_ofFn] using total
  constructor
  · apply UInt8.toNat_inj.mp
    simpa [byte_ofFn] using rTag
  constructor
  · simpa [byte_ofFn] using pos
  · simpa [byte_ofFn] using small

abbrev rChoices := {b : UInt8 // 1 ≤ b.toNat ∧ b.toNat ≤ 12}

def encode (f : {f : Fin 20 → UInt8 // f ∈ Target}) :
    rChoices × (Fin 16 → UInt8) :=
  (⟨f.val ⟨3, by decide⟩, (target_header f.property).2.2.2⟩,
    fun i => f.val ⟨i.val + 4, by omega⟩)

theorem encode_injective : Function.Injective encode := by
  intro f g same
  apply Subtype.ext
  funext i
  have fh := target_header f.property
  have gh := target_header g.property
  have rEq : f.val ⟨3, by decide⟩ = g.val ⟨3, by decide⟩ :=
    congrArg Subtype.val (congrArg Prod.fst same)
  have tailEq : (fun j : Fin 16 => f.val ⟨j.val + 4, by omega⟩) =
      (fun j : Fin 16 => g.val ⟨j.val + 4, by omega⟩) :=
    congrArg Prod.snd same
  by_cases low : i.val < 4
  · have cases : i.val = 0 ∨ i.val = 1 ∨
        i.val = 2 ∨ i.val = 3 := by omega
    rcases cases with h | h | h | h
    · have idx : i = ⟨0, by decide⟩ := Fin.ext h
      simpa [idx] using fh.1.trans gh.1.symm
    · have idx : i = ⟨1, by decide⟩ := Fin.ext h
      simpa [idx] using fh.2.1.trans gh.2.1.symm
    · have idx : i = ⟨2, by decide⟩ := Fin.ext h
      simpa [idx] using fh.2.2.1.trans gh.2.2.1.symm
    · have idx : i = ⟨3, by decide⟩ := Fin.ext h
      simpa [idx] using rEq
  · let j : Fin 16 := ⟨i.val - 4, by omega⟩
    have index : i = ⟨j.val + 4, by omega⟩ := by
      apply Fin.ext
      dsimp [j]
      omega
    rw [index]
    exact congrFun tailEq j

theorem rChoices_card : Fintype.card rChoices = 12 := by decide

/-- A mechanically proved conservative count: at most 12 choices for the
R-length byte and 256 choices for each of the remaining 16 bytes. -/
theorem target_card_le : Target.card ≤ 12 * 256 ^ 16 := by
  classical
  have bound := Fintype.card_le_of_injective encode encode_injective
  rw [Fintype.card_subtype] at bound
  simpa [Target, Fintype.card_prod, Fintype.card_fun,
    rChoices_card, Fintype.card_fin] using bound

theorem output_space_card : Fintype.card (Fin 20 → UInt8) = 256 ^ 20 := by
  have byteCard : Fintype.card UInt8 = 256 := by decide
  simp [byteCard]

/-- The target density is at most `12 / 256^4`. This is deliberately weaker
than the unproved exact DER-20 count correspondence. -/
theorem target_density_scaled :
    Target.card * 256 ^ 4 ≤
      12 * Fintype.card (Fin 20 → UInt8) := by
  calc
    _ ≤ (12 * 256 ^ 16) * 256 ^ 4 :=
      Nat.mul_le_mul_right _ target_card_le
    _ = 12 * Fintype.card (Fin 20 → UInt8) := by
      rw [output_space_card]
      ring

/-- Generic composition with the independently sampled random-function
theorem. This keeps the output type abstract so Lean does not materialize the
astronomical function space for twenty-byte strings. Instantiating its target
cardinality with `target_card_le` gives the conservative DER setup estimate;
it does not model adaptive or quantum oracle access. -/
theorem bounded_target_setup_union_count {I Ξ X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ξ] [DecidableEq Ξ]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (source : I → Ξ → X) (target : Finset Y) (bound : Nat)
    (targetBound : target.card ≤ bound) :
    ((Finset.univ.filter fun p : Ξ × (X → Y) =>
      ∃ i : I, p.2 (source i p.1) ∈ target).card) * Fintype.card Y ≤
      Fintype.card I *
        (Fintype.card (Ξ × (X → Y)) * bound) := by
  calc
    _ ≤ Fintype.card I *
          (Fintype.card (Ξ × (X → Y)) * target.card) :=
      RandomOracleSetup.shared_function_union_hit_count source target
    _ ≤ _ := by gcongr

end QSB.DERHeaderBound
