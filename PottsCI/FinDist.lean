import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite distributions, couplings, and optimal transport cost

Foundations for the Wasserstein–Hamming machinery of the note
"A Self-Contained Hamming-CI Proof for the Antiferromagnetic Potts Model on the
Whole Interval" (Section 1 and Section 5).

We work with probability distributions on finite types, represented by real
weight functions.  `W d μ ν` is the optimal transport cost between `μ` and `ν`
for a cost function `d`, defined as an infimum over couplings; for `d` the
Hamming distance this is the quantity `W_Ham` of the paper.

Main results:

* `PottsCI.FinDist.W_le_cost`, `le_W`: the defining bounds of the infimum;
* `PottsCI.FinDist.W_triangle`: the triangle inequality, via the gluing
  construction `Coupling.glue`;
* `PottsCI.FinDist.W_bind_le`: transport between two one-step laws is bounded
  by the coupled average of pointwise transports;
* `PottsCI.FinDist.W_bind_contract`: a pointwise one-step contraction
  estimate lifts to arbitrary starting distributions;
* `PottsCI.FinDist.stationary_comparison`: Lemma 5.1 of the paper.
-/

namespace PottsCI

open Finset

variable {S : Type*} {T : Type*} {U : Type*} {S' : Type*} {T' : Type*}
variable [Fintype S] [Fintype T] [Fintype U] [Fintype S'] [Fintype T']

/-- A probability distribution on a finite type, with real weights. -/
@[ext]
structure FinDist (S : Type*) [Fintype S] where
  /-- The weight (probability mass) function. -/
  w : S → ℝ
  nonneg : ∀ x, 0 ≤ w x
  sum_one : ∑ x, w x = 1

namespace FinDist

lemma le_one (μ : FinDist S) (x : S) : μ.w x ≤ 1 := by
  have h := Finset.single_le_sum (f := μ.w) (fun i _ => μ.nonneg i) (Finset.mem_univ x)
  simpa [μ.sum_one] using h

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform (S : Type*) [Fintype S] [Nonempty S] : FinDist S where
  w := fun _ => (Fintype.card S : ℝ)⁻¹
  nonneg := fun _ => by positivity
  sum_one := by
    have hcard : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]

/-- Point mass at `x₀`. -/
def pure [DecidableEq S] (x₀ : S) : FinDist S where
  w := fun x => if x = x₀ then 1 else 0
  nonneg := fun x => by split <;> norm_num
  sum_one := by simp

/-- Push a distribution through a probability kernel: the law after one step of
the kernel `K` started from `μ`.  This is `μ P` in matrix notation. -/
def bind (μ : FinDist S) (K : S → FinDist T) : FinDist T where
  w := fun y => ∑ x, μ.w x * (K x).w y
  nonneg := fun y => Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) ((K x).nonneg y)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinDist.sum_one, mul_one]
    exact μ.sum_one

@[simp] lemma bind_w (μ : FinDist S) (K : S → FinDist T) (y : T) :
    (μ.bind K).w y = ∑ x, μ.w x * (K x).w y := rfl

/-- Mix a finite family of distributions with the given weights. -/
def mix {ι : Type*} (s : Finset ι) (p : ι → ℝ) (f : ι → FinDist S)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) : FinDist S where
  w := fun x => ∑ i ∈ s, p i * (f i).w x
  nonneg := fun x => Finset.sum_nonneg fun i hi => mul_nonneg (hp0 i hi) ((f i).nonneg x)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinDist.sum_one, mul_one]
    exact hp1

@[simp] lemma mix_w {ι : Type*} (s : Finset ι) (p : ι → ℝ) (f : ι → FinDist S)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) (x : S) :
    (mix s p f hp0 hp1).w x = ∑ i ∈ s, p i * (f i).w x := rfl

/-- A coupling of two finite distributions: a joint distribution with the
prescribed marginals. -/
structure Coupling (μ : FinDist S) (ν : FinDist T) where
  /-- The joint weight function. -/
  w : S → T → ℝ
  nonneg : ∀ x y, 0 ≤ w x y
  sum_row : ∀ x, ∑ y, w x y = μ.w x
  sum_col : ∀ y, ∑ x, w x y = ν.w y

namespace Coupling

variable {μ : FinDist S} {ν : FinDist T} {ρ : FinDist U}

/-- The product (independent) coupling. -/
def prod (μ : FinDist S) (ν : FinDist T) : Coupling μ ν where
  w := fun x y => μ.w x * ν.w y
  nonneg := fun x y => mul_nonneg (μ.nonneg x) (ν.nonneg y)
  sum_row := fun x => by rw [← Finset.mul_sum, ν.sum_one, mul_one]
  sum_col := fun y => by rw [← Finset.sum_mul, μ.sum_one, one_mul]

instance : Nonempty (Coupling μ ν) := ⟨prod μ ν⟩

/-- The diagonal coupling of a distribution with itself. -/
def diag [DecidableEq S] (α : FinDist S) : Coupling α α where
  w := fun x y => if y = x then α.w x else 0
  nonneg := fun x y => by
    split
    · exact α.nonneg x
    · exact le_rfl
  sum_row := fun x => by simp
  sum_col := fun y => by
    rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hxy
      exact if_neg fun h => hxy h.symm
    · intro h
      exact absurd (Finset.mem_univ y) h

/-- Total mass of a coupling is `1`. -/
lemma total_mass (γ : Coupling μ ν) : ∑ x, ∑ y, γ.w x y = 1 := by
  simp_rw [γ.sum_row]; exact μ.sum_one

/-- If a column has zero marginal then the whole column vanishes. -/
lemma eq_zero_of_col (γ : Coupling μ ν) {y : T} (hy : ν.w y = 0) (x : S) : γ.w x y = 0 := by
  have h0 : ∑ x, γ.w x y = 0 := by rw [γ.sum_col y, hy]
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => γ.nonneg i y)).mp h0 x (Finset.mem_univ x)

/-- If a row has zero marginal then the whole row vanishes. -/
lemma eq_zero_of_row (γ : Coupling μ ν) {x : S} (hx : μ.w x = 0) (y : T) : γ.w x y = 0 := by
  have h0 : ∑ y, γ.w x y = 0 := by rw [γ.sum_row x, hx]
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => γ.nonneg x j)).mp h0 y (Finset.mem_univ y)

/-- Transportation cost of a coupling against a cost function. -/
def cost (γ : Coupling μ ν) (d : S → T → ℝ) : ℝ := ∑ x, ∑ y, γ.w x y * d x y

lemma cost_nonneg (γ : Coupling μ ν) {d : S → T → ℝ} (hd : ∀ x y, 0 ≤ d x y) :
    0 ≤ γ.cost d :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (γ.nonneg x y) (hd x y)

lemma cost_le_bound (γ : Coupling μ ν) {d : S → T → ℝ} {B : ℝ} (hd : ∀ x y, d x y ≤ B) :
    γ.cost d ≤ B := by
  have h : γ.cost d ≤ ∑ x, ∑ y, γ.w x y * B := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    exact mul_le_mul_of_nonneg_left (hd x y) (γ.nonneg x y)
  calc γ.cost d ≤ ∑ x, ∑ y, γ.w x y * B := h
    _ = (∑ x, ∑ y, γ.w x y) * B := by simp_rw [← Finset.sum_mul]
    _ = B := by rw [γ.total_mass, one_mul]

private lemma glue_sum_z (γ₁ : Coupling μ ν) (γ₂ : Coupling ν ρ) (x : S) (y : T) :
    ∑ z, γ₁.w x y * γ₂.w y z / ν.w y = γ₁.w x y := by
  by_cases hy : ν.w y = 0
  · simp [γ₁.eq_zero_of_col hy]
  · have hstep : ∑ z, γ₁.w x y * γ₂.w y z / ν.w y
        = γ₁.w x y * (∑ z, γ₂.w y z) / ν.w y := by
      rw [Finset.mul_sum, Finset.sum_div]
    rw [hstep, γ₂.sum_row y, mul_div_assoc, div_self hy, mul_one]

private lemma glue_sum_x (γ₁ : Coupling μ ν) (γ₂ : Coupling ν ρ) (y : T) (z : U) :
    ∑ x, γ₁.w x y * γ₂.w y z / ν.w y = γ₂.w y z := by
  by_cases hy : ν.w y = 0
  · simp [γ₂.eq_zero_of_row hy]
  · have hstep : ∑ x, γ₁.w x y * γ₂.w y z / ν.w y
        = (∑ x, γ₁.w x y) * γ₂.w y z / ν.w y := by
      rw [Finset.sum_mul, Finset.sum_div]
    rw [hstep, γ₁.sum_col y, mul_comm, mul_div_assoc, div_self hy, mul_one]

/-- The glued coupling: transport `μ → ν` by `γ₁` and then `ν → ρ` by `γ₂`,
disintegrating through the middle marginal. -/
noncomputable def glue (γ₁ : Coupling μ ν) (γ₂ : Coupling ν ρ) : Coupling μ ρ where
  w := fun x z => ∑ y, γ₁.w x y * γ₂.w y z / ν.w y
  nonneg := fun x z => Finset.sum_nonneg fun y _ =>
    div_nonneg (mul_nonneg (γ₁.nonneg x y) (γ₂.nonneg y z)) (ν.nonneg y)
  sum_row := fun x => by
    rw [Finset.sum_comm]
    simp_rw [glue_sum_z γ₁ γ₂ x]
    exact γ₁.sum_row x
  sum_col := fun z => by
    rw [Finset.sum_comm]
    simp_rw [glue_sum_x γ₁ γ₂ (z := z)]
    exact γ₂.sum_col z

/-- Cost of the glued coupling obeys the triangle inequality. -/
lemma glue_cost_le (γ₁ : Coupling μ ν) (γ₂ : Coupling ν ρ)
    {d₁ : S → T → ℝ} {d₂ : T → U → ℝ} {d₃ : S → U → ℝ}
    (htri : ∀ x y z, d₃ x z ≤ d₁ x y + d₂ y z) :
    (γ₁.glue γ₂).cost d₃ ≤ γ₁.cost d₁ + γ₂.cost d₂ := by
  have ht0 : ∀ (x : S) (y : T) (z : U), 0 ≤ γ₁.w x y * γ₂.w y z / ν.w y := fun x y z =>
    div_nonneg (mul_nonneg (γ₁.nonneg x y) (γ₂.nonneg y z)) (ν.nonneg y)
  have hexpand : (γ₁.glue γ₂).cost d₃
      = ∑ x, ∑ z, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * d₃ x z := by
    unfold cost glue
    simp_rw [Finset.sum_mul]
  have hbound : ∑ x, ∑ z, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * d₃ x z
      ≤ ∑ x, ∑ z, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * (d₁ x y + d₂ y z) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ =>
      Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (htri x y z) (ht0 x y z)
  have h1 : ∑ x, ∑ z, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * d₁ x y = γ₁.cost d₁ := by
    unfold cost
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, glue_sum_z γ₁ γ₂ x y]
  have h2 : ∑ x, ∑ z, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * d₂ y z = γ₂.cost d₂ := by
    unfold cost
    calc ∑ x, ∑ z, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * d₂ y z
        = ∑ z, ∑ x, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * d₂ y z := Finset.sum_comm
      _ = ∑ z, ∑ y, ∑ x, γ₁.w x y * γ₂.w y z / ν.w y * d₂ y z :=
          Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ z, ∑ y, γ₂.w y z * d₂ y z := by
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_mul, glue_sum_x γ₁ γ₂ y z]
      _ = ∑ y, ∑ z, γ₂.w y z * d₂ y z := Finset.sum_comm
  have hsplit : ∑ x, ∑ z, ∑ y, γ₁.w x y * γ₂.w y z / ν.w y * (d₁ x y + d₂ y z)
      = γ₁.cost d₁ + γ₂.cost d₂ := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [h1, h2]
  rw [hexpand]
  exact hbound.trans_eq hsplit

/-- Componentwise coupling of two one-step laws given a coupling of the
starting distributions and couplings of the kernels. -/
def mixBind {α : FinDist S} {β : FinDist T} (γ : Coupling α β)
    (K : S → FinDist S') (L : T → FinDist T')
    (κ : ∀ x y, Coupling (K x) (L y)) : Coupling (α.bind K) (β.bind L) where
  w := fun s' t' => ∑ x, ∑ y, γ.w x y * (κ x y).w s' t'
  nonneg := fun s' t' => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (γ.nonneg x y) ((κ x y).nonneg s' t')
  sum_row := fun s' => by
    calc ∑ t', ∑ x, ∑ y, γ.w x y * (κ x y).w s' t'
        = ∑ x, ∑ t', ∑ y, γ.w x y * (κ x y).w s' t' := Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ t', γ.w x y * (κ x y).w s' t' :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ x, ∑ y, γ.w x y * (K x).w s' := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.mul_sum, (κ x y).sum_row s']
      _ = ∑ x, α.w x * (K x).w s' := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_mul, γ.sum_row x]
      _ = (α.bind K).w s' := rfl
  sum_col := fun t' => by
    calc ∑ s', ∑ x, ∑ y, γ.w x y * (κ x y).w s' t'
        = ∑ x, ∑ s', ∑ y, γ.w x y * (κ x y).w s' t' := Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ s', γ.w x y * (κ x y).w s' t' :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ x, ∑ y, γ.w x y * (L y).w t' := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.mul_sum, (κ x y).sum_col t']
      _ = ∑ y, ∑ x, γ.w x y * (L y).w t' := Finset.sum_comm
      _ = ∑ y, β.w y * (L y).w t' := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_mul, γ.sum_col y]
      _ = (β.bind L).w t' := rfl

lemma mixBind_cost {α : FinDist S} {β : FinDist T} (γ : Coupling α β)
    (K : S → FinDist S') (L : T → FinDist T') (κ : ∀ x y, Coupling (K x) (L y))
    (d : S' → T' → ℝ) :
    (γ.mixBind K L κ).cost d = ∑ x, ∑ y, γ.w x y * (κ x y).cost d := by
  unfold cost mixBind
  calc ∑ s', ∑ t', (∑ x, ∑ y, γ.w x y * (κ x y).w s' t') * d s' t'
      = ∑ s', ∑ t', ∑ x, ∑ y, γ.w x y * (κ x y).w s' t' * d s' t' := by
        refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t' _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
    _ = ∑ s', ∑ x, ∑ t', ∑ y, γ.w x y * (κ x y).w s' t' * d s' t' :=
        Finset.sum_congr rfl fun s' _ => Finset.sum_comm
    _ = ∑ x, ∑ s', ∑ t', ∑ y, γ.w x y * (κ x y).w s' t' * d s' t' := Finset.sum_comm
    _ = ∑ x, ∑ s', ∑ y, ∑ t', γ.w x y * (κ x y).w s' t' * d s' t' :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s' _ => Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ s', ∑ t', γ.w x y * (κ x y).w s' t' * d s' t' :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ y, γ.w x y * (κ x y).cost d := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        unfold cost
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t' _ => ?_
        rw [mul_assoc]

end Coupling

/-! ## The optimal transport cost -/

/-- The set of achievable transport costs between `μ` and `ν`. -/
def costSet (d : S → T → ℝ) (μ : FinDist S) (ν : FinDist T) : Set ℝ :=
  Set.range fun γ : Coupling μ ν => γ.cost d

lemma costSet_nonempty (d : S → T → ℝ) (μ : FinDist S) (ν : FinDist T) :
    (costSet d μ ν).Nonempty := ⟨_, ⟨Coupling.prod μ ν, rfl⟩⟩

lemma costSet_bddBelow {d : S → T → ℝ} (hd : ∀ x y, 0 ≤ d x y) (μ : FinDist S) (ν : FinDist T) :
    BddBelow (costSet d μ ν) := by
  refine ⟨0, ?_⟩
  rintro r ⟨γ, rfl⟩
  exact γ.cost_nonneg hd

/-- Optimal transport cost between two finite distributions for cost `d`:
the infimum of `γ.cost d` over all couplings `γ`.  For `d = ham` this is the
`W_Ham` of the paper. -/
noncomputable def W (d : S → T → ℝ) (μ : FinDist S) (ν : FinDist T) : ℝ :=
  sInf (costSet d μ ν)

section Wlemmas

variable {d : S → T → ℝ} {μ : FinDist S} {ν : FinDist T}

lemma W_le_cost (hd : ∀ x y, 0 ≤ d x y) (γ : Coupling μ ν) :
    W d μ ν ≤ γ.cost d :=
  csInf_le (costSet_bddBelow hd μ ν) ⟨γ, rfl⟩

lemma W_nonneg (hd : ∀ x y, 0 ≤ d x y) : 0 ≤ W d μ ν := by
  refine le_csInf (costSet_nonempty d μ ν) ?_
  rintro r ⟨γ, rfl⟩
  exact γ.cost_nonneg hd

lemma le_W {c : ℝ} (h : ∀ γ : Coupling μ ν, c ≤ γ.cost d) : c ≤ W d μ ν := by
  refine le_csInf (costSet_nonempty d μ ν) ?_
  rintro r ⟨γ, rfl⟩
  exact h γ

lemma W_le_bound {B : ℝ} (hd : ∀ x y, 0 ≤ d x y) (hB : ∀ x y, d x y ≤ B) :
    W d μ ν ≤ B :=
  (W_le_cost hd (Coupling.prod μ ν)).trans ((Coupling.prod μ ν).cost_le_bound hB)

/-- Near-optimal couplings exist. -/
lemma exists_coupling_lt (_hd : ∀ x y, 0 ≤ d x y) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Coupling μ ν, γ.cost d < W d μ ν + ε := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (costSet_nonempty d μ ν)
    (lt_add_of_pos_right (W d μ ν) hε)
  obtain ⟨γ, rfl⟩ := hr
  exact ⟨γ, hlt⟩

end Wlemmas

/-- The transport cost from a distribution to itself vanishes (for a cost
vanishing on the diagonal). -/
lemma W_self [DecidableEq S] {d : S → S → ℝ} (hd : ∀ x y, 0 ≤ d x y)
    (hd0 : ∀ x, d x x = 0) (μ : FinDist S) : W d μ μ = 0 := by
  refine le_antisymm ?_ (W_nonneg hd)
  have hcost : (Coupling.diag μ).cost d = 0 := by
    unfold Coupling.cost
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    show (if y = x then μ.w x else 0) * d x y = 0
    rcases eq_or_ne y x with h | h
    · subst h; rw [if_pos rfl, hd0, mul_zero]
    · rw [if_neg h, zero_mul]
  calc W d μ μ ≤ (Coupling.diag μ).cost d := W_le_cost hd _
    _ = 0 := hcost

/-- Triangle inequality for the optimal transport cost, via gluing. -/
lemma W_triangle {d₁ : S → T → ℝ} {d₂ : T → U → ℝ} {d₃ : S → U → ℝ}
    (hd₁ : ∀ x y, 0 ≤ d₁ x y) (hd₂ : ∀ x y, 0 ≤ d₂ x y) (hd₃ : ∀ x y, 0 ≤ d₃ x y)
    (htri : ∀ x y z, d₃ x z ≤ d₁ x y + d₂ y z)
    (μ : FinDist S) (ν : FinDist T) (ρ : FinDist U) :
    W d₃ μ ρ ≤ W d₁ μ ν + W d₂ ν ρ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨γ₁, h₁⟩ := exists_coupling_lt (μ := μ) (ν := ν) hd₁ (half_pos hε)
  obtain ⟨γ₂, h₂⟩ := exists_coupling_lt (μ := ν) (ν := ρ) hd₂ (half_pos hε)
  have hglue := γ₁.glue_cost_le γ₂ htri
  have hW := W_le_cost hd₃ (γ₁.glue γ₂)
  linarith

/-- Transport between two one-step laws is bounded by the coupled average of
the pointwise transports. -/
lemma W_bind_le {d' : S' → T' → ℝ} (hd' : ∀ x y, 0 ≤ d' x y)
    {α : FinDist S} {β : FinDist T} (γ : Coupling α β)
    (K : S → FinDist S') (L : T → FinDist T') :
    W d' (α.bind K) (β.bind L) ≤ ∑ x, ∑ y, γ.w x y * W d' (K x) (L y) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hκ : ∀ x : S, ∀ y : T, ∃ κ : Coupling (K x) (L y),
      κ.cost d' < W d' (K x) (L y) + ε := fun x y => exists_coupling_lt hd' hε
  choose κ hκ using hκ
  have h1 : W d' (α.bind K) (β.bind L) ≤ (γ.mixBind K L κ).cost d' := W_le_cost hd' _
  rw [γ.mixBind_cost K L κ d'] at h1
  have h2 : ∑ x, ∑ y, γ.w x y * (κ x y).cost d'
      ≤ ∑ x, ∑ y, γ.w x y * (W d' (K x) (L y) + ε) := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    exact mul_le_mul_of_nonneg_left (hκ x y).le (γ.nonneg x y)
  have h3 : ∑ x, ∑ y, γ.w x y * (W d' (K x) (L y) + ε)
      = (∑ x, ∑ y, γ.w x y * W d' (K x) (L y)) + ε := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [γ.total_mass, one_mul]
  linarith

/-- Averaged perturbation bound: same starting law, two kernels. -/
lemma W_bind_diag [DecidableEq S] {d' : S' → T' → ℝ} (hd' : ∀ x y, 0 ≤ d' x y)
    (α : FinDist S) (K : S → FinDist S') (L : S → FinDist T') :
    W d' (α.bind K) (α.bind L) ≤ ∑ x, α.w x * W d' (K x) (L x) := by
  refine (W_bind_le hd' (Coupling.diag α) K L).trans_eq ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  have hterm : ∀ y, (Coupling.diag α).w x y * W d' (K x) (L y)
      = if y = x then α.w x * W d' (K x) (L y) else 0 := by
    intro y
    show (if y = x then α.w x else 0) * W d' (K x) (L y) = _
    rcases eq_or_ne y x with h | h
    · simp [h]
    · simp [h]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' Finset.univ x fun y => α.w x * W d' (K x) (L y)]
  simp

/-- A pointwise contraction estimate for a kernel lifts to arbitrary starting
distributions. -/
lemma W_bind_contract {d : S → S → ℝ} {d' : S' → S' → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd' : ∀ x y, 0 ≤ d' x y)
    {c : ℝ} (hc : 0 ≤ c) (K : S → FinDist S')
    (hK : ∀ x y, W d' (K x) (K y) ≤ c * d x y) (α β : FinDist S) :
    W d' (α.bind K) (β.bind K) ≤ c * W d α β := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεc : 0 < ε / (c + 1) := by positivity
  obtain ⟨γ, hγ⟩ := exists_coupling_lt (μ := α) (ν := β) hd hεc
  have h1 := W_bind_le hd' γ K K
  have h2 : ∑ x, ∑ y, γ.w x y * W d' (K x) (K y) ≤ ∑ x, ∑ y, γ.w x y * (c * d x y) := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    exact mul_le_mul_of_nonneg_left (hK x y) (γ.nonneg x y)
  have h3 : ∑ x, ∑ y, γ.w x y * (c * d x y) = c * γ.cost d := by
    unfold Coupling.cost
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h4 : c * γ.cost d ≤ c * (W d α β + ε / (c + 1)) :=
    mul_le_mul_of_nonneg_left hγ.le hc
  have h5 : c * (ε / (c + 1)) ≤ ε := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by linarith : (0:ℝ) < c + 1)]
    nlinarith
  nlinarith

/-! ## Stationary comparison (Lemma 5.1 of the paper) -/

/-- A distribution is stationary for a kernel if one step leaves it unchanged. -/
def IsStationary (K : S → FinDist S) (π : FinDist S) : Prop := π.bind K = π

/-- **Lemma 5.1 (Stationary comparison).**  If `P` contracts the transport
cost at rate `c < 1` from arbitrary starting laws, and `Q` is a one-step
perturbation of `P` of size `D`, then the stationary laws of `P` and `Q` are
within `D / (1 - c)`. -/
theorem stationary_comparison [DecidableEq S] {d : S → S → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (P Q : S → FinDist S) (πP πQ : FinDist S)
    (hπP : IsStationary P πP) (hπQ : IsStationary Q πQ)
    {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcontr : ∀ α β : FinDist S, W d (α.bind P) (β.bind P) ≤ c * W d α β)
    {D : ℝ} (hD : ∀ x, W d (P x) (Q x) ≤ D) :
    W d πP πQ ≤ D / (1 - c) := by
  have key : W d πP πQ ≤ c * W d πP πQ + D := by
    have hstep : W d πP πQ = W d (πP.bind P) (πQ.bind Q) := by
      rw [hπP, hπQ]
    have htriW := W_triangle hd hd hd htri (πP.bind P) (πQ.bind P) (πQ.bind Q)
    have hleft : W d (πP.bind P) (πQ.bind P) ≤ c * W d πP πQ := hcontr πP πQ
    have hright : W d (πQ.bind P) (πQ.bind Q) ≤ D := by
      refine (W_bind_diag hd πQ P Q).trans ?_
      have hsum : ∑ x, πQ.w x * W d (P x) (Q x) ≤ ∑ x, πQ.w x * D :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hD x) (πQ.nonneg x)
      have htot : ∑ x, πQ.w x * D = D := by rw [← Finset.sum_mul, πQ.sum_one, one_mul]
      linarith
    linarith [hstep ▸ htriW]
  have h1c : (0:ℝ) < 1 - c := by linarith
  rw [le_div_iff₀ h1c]
  nlinarith

end FinDist

end PottsCI
