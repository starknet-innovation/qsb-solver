import QSB.TaggedOracle

/-!
Local response sets for the generalized collision relation of
Chung–Fehr–Huang–Liao, Theorem 5.30. For a fixed function `f` of the query
input and the oracle response, a fresh query `x` against a recorded database
`db` can newly create an `f`-collision only if its response lies in the union,
over recorded entries `(x', y')`, of the fibers `{y | f x y = f x' y'}`. With
every fiber of size at most `Γ`, that union has at most `|db|·Γ` elements, so
its uniform-response probability is at most `|db|·Γ / M`.

For the tagged product oracle the two coordinate projections have exact
fibers of `2^160` and `2^256` responses inside the `2^416`-element response
space, uniformly over all input pairs, including equal inputs and mixed tags.
These are classical counting facts about one additional query. The quantum
transition-capacity theorem, a causal query algorithm, the honest transcript
budget, and the bit encoding of the source byte oracles remain external.
-/
namespace QSB.TaggedLocalResponses
open Finset

section General

variable {I Resp T : Type*} [Fintype Resp] [DecidableEq T]

/-- Responses to a query at `x` that make `f` agree with the recorded pair
`(x', y')`. This is the paper's local property `CL_{i,j}` restricted to the
response register of `x`. -/
def pairResponses (f : I → Resp → T) (x x' : I) (y' : Resp) : Finset Resp :=
  univ.filter fun y => f x y = f x' y'

/-- Responses to a query at `x` that collide with at least one recorded
database entry. This is the paper's local property `CL_i`. -/
def databaseResponses [DecidableEq I] [DecidableEq Resp]
    (f : I → Resp → T) (x : I) (db : List (I × Resp)) : Finset Resp :=
  db.toFinset.biUnion fun entry => pairResponses f x entry.1 entry.2

/-- The paper's `Γ` hypothesis, stated for every input pair rather than only
for distinct inputs; a bound for all pairs implies the paper's maximum. -/
def FiberBound (f : I → Resp → T) (Γ : ℕ) : Prop :=
  ∀ x x' y', (pairResponses f x x' y').card ≤ Γ

/-- Uniform-response probability of a response set, as the paper's
`P[U ∈ L] = |L| / M`. -/
noncomputable def localProbability (s : Finset Resp) : ℚ :=
  (s.card : ℚ) / Nat.card Resp

theorem mem_pairResponses (f : I → Resp → T) (x x' : I) (y' y : Resp) :
    y ∈ pairResponses f x x' y' ↔ f x y = f x' y' := by
  simp [pairResponses]

theorem mem_databaseResponses [DecidableEq I] [DecidableEq Resp]
    (f : I → Resp → T) (x : I) (db : List (I × Resp)) (y : Resp) :
    y ∈ databaseResponses f x db ↔
      ∃ entry ∈ db, f x y = f entry.1 entry.2 := by
  simp [databaseResponses, pairResponses]

/-- A response that produces a collision with a recorded entry lies in the
database response set. The converse direction is the membership lemma. -/
theorem collision_mem_databaseResponses [DecidableEq I] [DecidableEq Resp]
    (f : I → Resp → T) (x : I) (db : List (I × Resp)) (y : Resp)
    (entry : I × Resp) (recorded : entry ∈ db)
    (same : f x y = f entry.1 entry.2) :
    y ∈ databaseResponses f x db :=
  (mem_databaseResponses f x db y).2 ⟨entry, recorded, same⟩

/-- The union over recorded entries has at most `|db|·Γ` responses. -/
theorem databaseResponses_card_le [DecidableEq I] [DecidableEq Resp]
    (f : I → Resp → T) (Γ : ℕ) (bound : FiberBound f Γ) (x : I)
    (db : List (I × Resp)) :
    (databaseResponses f x db).card ≤ db.length * Γ := by
  calc (databaseResponses f x db).card
      ≤ ∑ entry ∈ db.toFinset, (pairResponses f x entry.1 entry.2).card :=
        card_biUnion_le
    _ ≤ ∑ _entry ∈ db.toFinset, Γ :=
        sum_le_sum fun entry _ => bound x entry.1 entry.2
    _ = db.toFinset.card * Γ := by simp
    _ ≤ db.length * Γ := Nat.mul_le_mul_right Γ db.toFinset_card_le

theorem localProbability_pairResponses_le (f : I → Resp → T) (Γ : ℕ)
    (bound : FiberBound f Γ) (x x' : I) (y' : Resp) :
    localProbability (pairResponses f x x' y') ≤
      (Γ : ℚ) / Nat.card Resp := by
  unfold localProbability
  gcongr
  exact_mod_cast bound x x' y'

/-- The paper's `k(q−1)Γ / M` estimate for one query against a database of
at most `|db|` recorded entries. -/
theorem localProbability_databaseResponses_le [DecidableEq I]
    [DecidableEq Resp] (f : I → Resp → T) (Γ : ℕ) (bound : FiberBound f Γ)
    (x : I) (db : List (I × Resp)) :
    localProbability (databaseResponses f x db) ≤
      ((db.length : ℚ) * Γ) / Nat.card Resp := by
  unfold localProbability
  gcongr
  exact_mod_cast databaseResponses_card_le f Γ bound x db

end General

section Tagged
open TaggedOracle

variable {X : Type*}

theorem filter_first_card (target : Bits 256) :
    (univ.filter fun y : Bits 256 × Bits 160 => y.1 = target).card =
      2 ^ 160 := by
  have h := h256_projection_fiber_card target
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

theorem filter_second_card (target : Bits 160) :
    (univ.filter fun y : Bits 256 × Bits 160 => y.2 = target).card =
      2 ^ 256 := by
  have h := r160_projection_fiber_card target
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

/-- Every projected-H pair fiber has exactly `2^160` responses, for every
input pair of the tagged domain. -/
theorem projectedH_pairResponses_card (x x' : Sum X X)
    (y' : Bits 256 × Bits 160) :
    (pairResponses (projectedH (X := X)) x x' y').card = 2 ^ 160 := by
  unfold pairResponses projectedH
  exact filter_first_card y'.1

theorem projectedR_pairResponses_card (x x' : Sum X X)
    (y' : Bits 256 × Bits 160) :
    (pairResponses (projectedR (X := X)) x x' y').card = 2 ^ 256 := by
  unfold pairResponses projectedR
  exact filter_second_card y'.2

theorem projectedH_fiberBound :
    FiberBound (projectedH (X := X)) (2 ^ 160) :=
  fun x x' y' => (projectedH_pairResponses_card x x' y').le

theorem projectedR_fiberBound :
    FiberBound (projectedR (X := X)) (2 ^ 256) :=
  fun x x' y' => (projectedR_pairResponses_card x x' y').le

/-- One further H-tag query against a recorded database newly matches a
recorded first coordinate for at most `|db|·2^160` of the `2^416`
responses. -/
theorem projectedH_databaseResponses_card_le [DecidableEq X]
    (x : Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160))) :
    (databaseResponses (projectedH (X := X)) x db).card ≤
      db.length * 2 ^ 160 :=
  databaseResponses_card_le _ _ projectedH_fiberBound x db

theorem projectedR_databaseResponses_card_le [DecidableEq X]
    (x : Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160))) :
    (databaseResponses (projectedR (X := X)) x db).card ≤
      db.length * 2 ^ 256 :=
  databaseResponses_card_le _ _ projectedR_fiberBound x db

theorem projectedH_pair_localProbability (x x' : Sum X X)
    (y' : Bits 256 × Bits 160) :
    localProbability (pairResponses (projectedH (X := X)) x x' y') =
      1 / 2 ^ 256 := by
  unfold localProbability
  rw [projectedH_pairResponses_card, joint_response_card, Nat.cast_pow,
    Nat.cast_pow, Nat.cast_ofNat, show (416 : ℕ) = 160 + 256 from rfl,
    pow_add, div_mul_eq_div_div, div_self (by positivity)]

theorem projectedR_pair_localProbability (x x' : Sum X X)
    (y' : Bits 256 × Bits 160) :
    localProbability (pairResponses (projectedR (X := X)) x x' y') =
      1 / 2 ^ 160 := by
  unfold localProbability
  rw [projectedR_pairResponses_card, joint_response_card, Nat.cast_pow,
    Nat.cast_pow, Nat.cast_ofNat, show (416 : ℕ) = 256 + 160 from rfl,
    pow_add, div_mul_eq_div_div, div_self (by positivity)]

/-- The paper's `Γ/M` ratio for the H route is `2^-256`; the database
union for one more query is at most `|db|·2^-256`. -/
theorem projectedH_database_localProbability_le [DecidableEq X]
    (x : Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160))) :
    localProbability (databaseResponses (projectedH (X := X)) x db) ≤
      (db.length : ℚ) / 2 ^ 256 := by
  refine (localProbability_databaseResponses_le _ _
    projectedH_fiberBound x db).trans (le_of_eq ?_)
  rw [joint_response_card, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show (416 : ℕ) = 160 + 256 from rfl, pow_add,
    mul_comm ((2 : ℚ) ^ 160) (2 ^ 256),
    mul_div_mul_right _ _ (by positivity)]

/-- The paper's `Γ/M` ratio for the R route is `2^-160`; the database
union for one more query is at most `|db|·2^-160`. -/
theorem projectedR_database_localProbability_le [DecidableEq X]
    (x : Sum X X)
    (db : List (Sum X X × (Bits 256 × Bits 160))) :
    localProbability (databaseResponses (projectedR (X := X)) x db) ≤
      (db.length : ℚ) / 2 ^ 160 := by
  refine (localProbability_databaseResponses_le _ _
    projectedR_fiberBound x db).trans (le_of_eq ?_)
  rw [joint_response_card, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show (416 : ℕ) = 256 + 160 from rfl, pow_add,
    mul_comm ((2 : ℚ) ^ 256) (2 ^ 160),
    mul_div_mul_right _ _ (by positivity)]

end Tagged

end QSB.TaggedLocalResponses
