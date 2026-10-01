import QSB.Parameters
import QSB.DERSyntax
import Mathlib

/-!
Count the minimally encoded nonnegative integer byte strings that can occupy
one DER R or S field. This is a component of the still-open equivalence
between `Parameters.der20Count` and the full `DERSyntax.valid` target set.
It does not count signatures or identify compiled Bitcoin Core behavior.
-/
namespace QSB.DERIntegerCount
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def splitTwo (n : Nat) :
    (Fin (n + 2) → UInt8) ≃ UInt8 × UInt8 × (Fin n → UInt8) where
  toFun f := (f 0, f 1, fun i => f i.succ.succ)
  invFun p := Fin.cons p.1 (Fin.cons p.2.1 p.2.2)
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp
    · simp
    · simp
  right_inv p := by
    rcases p with ⟨a, b, rest⟩
    simp

/-- Core's positive/minimal integer rule for a field of length `n+2`:
the first byte must be nonnegative, and a leading zero is allowed only to
protect a high-bit-set second byte. -/
def validLong (n : Nat) (f : Fin (n + 2) → UInt8) : Prop :=
  (f 0).toNat < 128 ∧
    ((f 0).toNat = 0 → 128 ≤ (f 1).toNat)

abbrev PositiveHead := {b : UInt8 // 1 ≤ b.toNat ∧ b.toNat < 128}
abbrev ProtectedHead := {b : UInt8 // 128 ≤ b.toNat}

theorem positiveHead_card : Fintype.card PositiveHead = 127 := by decide
theorem protectedHead_card : Fintype.card ProtectedHead = 128 := by decide

abbrev ShortCode :=
  {f : Fin 1 → UInt8 // (f 0).toNat < 128}

noncomputable instance : Fintype ShortCode := Fintype.ofFinite _

def shortEquiv : ShortCode ≃ {b : UInt8 // b.toNat < 128} where
  toFun f := ⟨f.val 0, f.property⟩
  invFun b := ⟨fun _ => b.val, b.property⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    have atZero : i = 0 := Fin.eq_zero i
    simp [atZero]
  right_inv b := by
    apply Subtype.ext
    rfl

theorem validShort_card : Fintype.card ShortCode =
    QSB.derIntegerCount 1 := by
  classical
  rw [Fintype.card_congr shortEquiv]
  decide

abbrev LongCode (n : Nat) :=
  {f : Fin (n + 2) → UInt8 // validLong n f}

noncomputable instance (n : Nat) : Fintype (LongCode n) :=
  Fintype.ofFinite _

abbrev CodeCases (n : Nat) :=
  (PositiveHead × (Fin (n + 1) → UInt8)) ⊕
    (ProtectedHead × (Fin n → UInt8))

def classify (n : Nat) (f : LongCode n) : CodeCases n :=
  if zero : (f.val 0).toNat = 0 then
    Sum.inr (⟨f.val 1, f.property.2 zero⟩,
      fun i => f.val i.succ.succ)
  else
    Sum.inl (⟨f.val 0, by
      have upper := f.property.1
      constructor <;> omega⟩,
      fun i => f.val i.succ)

def assemble (n : Nat) : CodeCases n → LongCode n
  | Sum.inl p =>
      ⟨Fin.cons p.1.val p.2, by
        dsimp [validLong]
        constructor
        · simpa using p.1.property.2
        · intro impossible
          have positive := p.1.property.1
          have zero : p.1.val.toNat = 0 := by
            simpa only [Fin.cons_zero] using impossible
          omega⟩
  | Sum.inr p =>
      ⟨Fin.cons 0 (Fin.cons p.1.val p.2), by
        dsimp [validLong]
        constructor
        · change (0 : UInt8).toNat < 128
          decide
        · intro _
          simpa using p.1.property⟩

theorem assemble_classify (n : Nat) (f : LongCode n) :
    assemble n (classify n f) = f := by
  unfold classify
  split_ifs with zero
  · apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · have h : f.val 0 = 0 := UInt8.toNat_inj.mp (by simpa using zero)
      simp [assemble, h]
    · simp [assemble]
    · simp [assemble]
  · apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [assemble]
    · simp [assemble]

theorem classify_assemble (n : Nat) (p : CodeCases n) :
    classify n (assemble n p) = p := by
  cases p with
  | inl p =>
      rcases p with ⟨head, tail⟩
      have notZero : head.val.toNat ≠ 0 := by
        have positive := head.property.1
        omega
      simp [classify, assemble, notZero]
  | inr p =>
      rcases p with ⟨head, tail⟩
      simp [classify, assemble]

def validLongEquiv (n : Nat) : LongCode n ≃ CodeCases n where
  toFun := classify n
  invFun := assemble n
  left_inv := assemble_classify n
  right_inv := classify_assemble n

theorem validLong_card (n : Nat) :
    Fintype.card {f : Fin (n + 2) → UInt8 // validLong n f} =
      QSB.derIntegerCount (n + 2) := by
  classical
  have byteCard : Fintype.card UInt8 = 256 := by decide
  rw [Fintype.card_congr (validLongEquiv n)]
  simp [QSB.derIntegerCount, positiveHead_card,
    protectedHead_card, byteCard, Fintype.card_fin]

theorem valid_der_r_short (sig : DERSyntax.Bytes)
    (accepted : DERSyntax.valid sig = true) :
    ∃ code : ShortCode,
      code.val = (fun _ : Fin 1 => sig[4]?.getD 0) := by
  unfold DERSyntax.valid at accepted
  simp only [decide_eq_true_eq] at accepted
  obtain ⟨_, _, _, _, _, _, _, _, first, _, _, _, _, _⟩ := accepted
  exact ⟨⟨_, by simpa [DERSyntax.byte] using first⟩, rfl⟩

theorem valid_der_s_short (sig : DERSyntax.Bytes)
    (accepted : DERSyntax.valid sig = true) :
    ∃ code : ShortCode,
      code.val = (fun _ : Fin 1 =>
        sig[DERSyntax.byte sig 3 + 6]?.getD 0) := by
  unfold DERSyntax.valid at accepted
  simp only [decide_eq_true_eq] at accepted
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, first, _⟩ := accepted
  exact ⟨⟨_, by simpa [DERSyntax.byte] using first⟩, rfl⟩

/-- Any DER-valid R integer of length at least two satisfies precisely the
long-integer prefix predicate whose full finite count was proved above. -/
theorem valid_der_r_long (sig : DERSyntax.Bytes) (n : Nat)
    (accepted : DERSyntax.valid sig = true)
    (lengthR : DERSyntax.byte sig 3 = n + 2) :
    validLong n (fun i => sig[4 + i.val]?.getD 0) := by
  unfold DERSyntax.valid at accepted
  simp only [decide_eq_true_eq] at accepted
  obtain ⟨_, _, _, _, _, _, _, _, first, minimal, _, _, _, _⟩ := accepted
  change DERSyntax.byte sig 4 < 128 ∧
    (DERSyntax.byte sig 4 = 0 → 128 ≤ DERSyntax.byte sig 5)
  constructor
  · exact first
  · intro zero
    rcases minimal with short | nonzero | pad
    · omega
    · exact False.elim (nonzero zero)
    · exact pad

/-- The analogous fact for the variable-position S integer. -/
theorem valid_der_s_long (sig : DERSyntax.Bytes) (n : Nat)
    (accepted : DERSyntax.valid sig = true)
    (lengthS : DERSyntax.byte sig (5 + DERSyntax.byte sig 3) = n + 2) :
    validLong n (fun i =>
      sig[DERSyntax.byte sig 3 + 6 + i.val]?.getD 0) := by
  unfold DERSyntax.valid at accepted
  simp only [decide_eq_true_eq] at accepted
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, first, minimal⟩ := accepted
  change DERSyntax.byte sig (DERSyntax.byte sig 3 + 6) < 128 ∧
    (DERSyntax.byte sig (DERSyntax.byte sig 3 + 6) = 0 →
      128 ≤ DERSyntax.byte sig (DERSyntax.byte sig 3 + 7))
  constructor
  · exact first
  · intro zero
    rcases minimal with short | nonzero | pad
    · omega
    · exact False.elim (nonzero zero)
    · exact pad

end QSB.DERIntegerCount
