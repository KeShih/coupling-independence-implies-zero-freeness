import ZeroFreeness.Coupling.Foundations.FinDist
import ZeroFreeness.Coupling.Foundations.PathCoupling
import ZeroFreeness.Analysis.ComplexAverage
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Finite coupling interfaces for the zero-free argument

The finite transport foundations are reused from `PottsCI.FinDist`. This file
connects their coupling matrices to expectations of real and complex
observables. It also records the averaging argument which selects a shell
of low expected disagreement cost.
-/

namespace ZeroFreeness

open scoped BigOperators
open PottsCI PottsCI.FinDist

noncomputable section

variable {S T : Type*} [Fintype S] [Fintype T]
variable {μ : FinDist S} {ν : FinDist T}

/-- Finite expectation of a real observable. -/
def expectReal (μ : FinDist S) (f : S → ℝ) : ℝ := ∑ x, μ.w x * f x

/-- Finite expectation of a complex observable. -/
def expectComplex (μ : FinDist S) (f : S → ℂ) : ℂ := ∑ x, (μ.w x : ℂ) * f x

@[simp] theorem expectReal_const (μ : FinDist S) (c : ℝ) :
    expectReal μ (fun _ => c) = c := by
  simp only [expectReal, ← Finset.sum_mul, μ.sum_one, one_mul]

@[simp] theorem expectComplex_const (μ : FinDist S) (c : ℂ) :
    expectComplex μ (fun _ => c) = c := by
  simp only [expectComplex, ← Finset.sum_mul, ← Complex.ofReal_sum, μ.sum_one,
    Complex.ofReal_one, one_mul]

theorem expectReal_mono (μ : FinDist S) {f g : S → ℝ}
    (h : ∀ x, f x ≤ g x) : expectReal μ f ≤ expectReal μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x)

theorem coupling_real_left (π : Coupling μ ν) (f : S → ℝ) :
    (∑ x, ∑ y, π.w x y * f x) = expectReal μ f := by
  simp only [expectReal, ← Finset.sum_mul, π.sum_row]

theorem coupling_real_right (π : Coupling μ ν) (g : T → ℝ) :
    (∑ x, ∑ y, π.w x y * g y) = expectReal ν g := by
  rw [Finset.sum_comm]
  simp only [expectReal, ← Finset.sum_mul, π.sum_col]

theorem coupling_complex_left (π : Coupling μ ν) (f : S → ℂ) :
    (∑ x, ∑ y, (π.w x y : ℂ) * f x) = expectComplex μ f := by
  simp only [expectComplex, ← Finset.sum_mul, ← Complex.ofReal_sum, π.sum_row]

theorem coupling_complex_right (π : Coupling μ ν) (g : T → ℂ) :
    (∑ x, ∑ y, (π.w x y : ℂ) * g y) = expectComplex ν g := by
  rw [Finset.sum_comm]
  simp only [expectComplex, ← Finset.sum_mul, ← Complex.ofReal_sum, π.sum_col]

theorem expectComplex_sub_eq_coupling (π : Coupling μ ν)
    (f : S → ℂ) (g : T → ℂ) :
    expectComplex μ f - expectComplex ν g =
      ∑ x, ∑ y, (π.w x y : ℂ) * (f x - g y) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [coupling_complex_left, coupling_complex_right]

/-- A coupling matrix regarded as a probability law on the product type. -/
def couplingLaw (π : Coupling μ ν) : FinDist (S × T) where
  w p := π.w p.1 p.2
  nonneg p := π.nonneg p.1 p.2
  sum_one := by
    rw [Fintype.sum_prod_type]
    exact π.total_mass

theorem expectComplex_couplingLaw_left (π : Coupling μ ν) (f : S → ℂ) :
    expectComplex (couplingLaw π) (fun p => f p.1) = expectComplex μ f := by
  simp only [expectComplex, couplingLaw, Fintype.sum_prod_type]
  exact coupling_complex_left π f

theorem expectComplex_couplingLaw_right (π : Coupling μ ν) (g : T → ℂ) :
    expectComplex (couplingLaw π) (fun p => g p.2) = expectComplex ν g := by
  simp only [expectComplex, couplingLaw, Fintype.sum_prod_type]
  exact coupling_complex_right π g

theorem expectReal_couplingLaw_cost (π : Coupling μ ν) (d : S → T → ℝ) :
    expectReal (couplingLaw π) (fun p => d p.1 p.2) = π.cost d := by
  simp only [expectReal, couplingLaw, Fintype.sum_prod_type, Coupling.cost]

/-- The expectation difference is bounded by the expected pointwise norm
difference under any coupling. -/
theorem norm_expectComplex_sub_le_cost (π : Coupling μ ν)
    (f : S → ℂ) (g : T → ℂ) :
    ‖expectComplex μ f - expectComplex ν g‖ ≤
      π.cost (fun x y => ‖f x - g y‖) := by
  rw [expectComplex_sub_eq_coupling π]
  calc
    ‖∑ x, ∑ y, (π.w x y : ℂ) * (f x - g y)‖ ≤
        ∑ x, ‖∑ y, (π.w x y : ℂ) * (f x - g y)‖ := norm_sum_le _ _
    _ ≤ ∑ x, ∑ y, ‖(π.w x y : ℂ) * (f x - g y)‖ := by
      exact Finset.sum_le_sum fun x _ => norm_sum_le _ _
    _ = π.cost (fun x y => ‖f x - g y‖) := by
      unfold Coupling.cost
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (π.nonneg x y)]

theorem cost_le_cost (π : Coupling μ ν) {d e : S → T → ℝ}
    (h : ∀ x y, d x y ≤ e x y) : π.cost d ≤ π.cost e :=
  Finset.sum_le_sum fun x _ =>
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h x y) (π.nonneg x y)

theorem cost_mul_left (π : Coupling μ ν) (L : ℝ) (d : S → T → ℝ) :
    π.cost (fun x y => L * d x y) = L * π.cost d := by
  simp only [Coupling.cost, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem norm_expectComplex_sub_le_cost_of_lipschitz (π : Coupling μ ν)
    (f : S → ℂ) (g : T → ℂ) (L : ℝ) (d : S → T → ℝ)
    (hfg : ∀ x y, ‖f x - g y‖ ≤ L * d x y) :
    ‖expectComplex μ f - expectComplex ν g‖ ≤ L * π.cost d := by
  calc
    ‖expectComplex μ f - expectComplex ν g‖ ≤
        π.cost (fun x y => ‖f x - g y‖) := norm_expectComplex_sub_le_cost π f g
    _ ≤ π.cost (fun x y => L * d x y) := cost_le_cost π hfg
    _ = L * π.cost d := cost_mul_left π L d

/-- The complex-observable transport bound uses the defining infimum of `W`;
it does not assume the existence of an optimal coupling. -/
theorem norm_expectComplex_sub_le_W_of_lipschitz
    (f : S → ℂ) (g : T → ℂ) {L : ℝ} (hL : 0 ≤ L) (d : S → T → ℝ)
    (hfg : ∀ x y, ‖f x - g y‖ ≤ L * d x y) :
    ‖expectComplex μ f - expectComplex ν g‖ ≤ L * W d μ ν := by
  rcases eq_or_lt_of_le hL with hL | hL
  · have h := norm_expectComplex_sub_le_cost_of_lipschitz (Coupling.prod μ ν) f g L d hfg
    simpa [← hL] using h
  · have hW : ‖expectComplex μ f - expectComplex ν g‖ / L ≤ W d μ ν := by
      apply le_W
      intro π
      apply (div_le_iff₀ hL).2
      simpa [mul_comm] using norm_expectComplex_sub_le_cost_of_lipschitz π f g L d hfg
    exact (div_le_iff₀ hL).1 hW |>.trans_eq (mul_comm _ _)

/-- Sum of the expected shell costs equals the expected sum of shell costs. -/
theorem sum_cost_eq_cost_sum {ι : Type*} [Fintype ι]
    (π : Coupling μ ν) (d : ι → S → T → ℝ) :
    (∑ i, π.cost (d i)) = π.cost (fun x y => ∑ i, d i x y) := by
  unfold Coupling.cost
  simp only [Finset.mul_sum]
  calc
    (∑ i, ∑ x, ∑ y, π.w x y * d i x y) =
        ∑ x, ∑ i, ∑ y, π.w x y * d i x y := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i, π.w x y * d i x y := by
      exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem sum_cost_le_cost {ι : Type*} [Fintype ι]
    (π : Coupling μ ν) (d : ι → S → T → ℝ) (D : S → T → ℝ)
    (h : ∀ x y, ∑ i, d i x y ≤ D x y) :
    (∑ i, π.cost (d i)) ≤ π.cost D := by
  rw [sum_cost_eq_cost_sum]
  exact cost_le_cost π h

/-- If disjoint shell costs have total expected cost at most `B`, some shell
has expected cost at most `B / number_of_shells`. -/
theorem exists_low_cost_shell {ι : Type*} [Fintype ι] [Nonempty ι]
    (π : Coupling μ ν) (d : ι → S → T → ℝ) {B : ℝ}
    (hbudget : (∑ i, π.cost (d i)) ≤ B) :
    ∃ i, π.cost (d i) ≤ B / Fintype.card ι := by
  classical
  by_contra h
  push Not at h
  have hsum : ∑ i : ι, B / (Fintype.card ι : ℝ) < ∑ i, π.cost (d i) := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h i)
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hconst : (∑ _ : ι, B / (Fintype.card ι : ℝ)) = B := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  linarith

/-- A family of nonnegative shell costs dominated by a total cost is also
dominated after taking optimal transport costs. The same coupling may be used
to bound every shell, before taking the infimum for the total cost. -/
theorem sum_W_le_W {ι : Type*} [Fintype ι]
    (d : ι → S → T → ℝ) (D : S → T → ℝ)
    (hd : ∀ i x y, 0 ≤ d i x y)
    (h : ∀ x y, ∑ i, d i x y ≤ D x y) :
    (∑ i, W (d i) μ ν) ≤ W D μ ν := by
  apply le_W
  intro π
  calc
    (∑ i, W (d i) μ ν) ≤ ∑ i, π.cost (d i) :=
      Finset.sum_le_sum fun i _ => W_le_cost (hd i) π
    _ ≤ π.cost D := sum_cost_le_cost π d D h

/-- A total CI budget selects a low-cost shell directly at the transport
level. No minimizing coupling or limiting choice of a shell is assumed. -/
theorem exists_low_W_shell {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → S → T → ℝ) (D : S → T → ℝ)
    (hd : ∀ i x y, 0 ≤ d i x y)
    (h : ∀ x y, ∑ i, d i x y ≤ D x y) {B : ℝ}
    (hbudget : W D μ ν ≤ B) :
    ∃ i, W (d i) μ ν ≤ B / Fintype.card ι := by
  classical
  have htotal : (∑ i, W (d i) μ ν) ≤ B := (sum_W_le_W d D hd h).trans hbudget
  by_contra hnone
  push Not at hnone
  have hsum : ∑ i : ι, B / (Fintype.card ι : ℝ) < ∑ i, W (d i) μ ν := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hnone i)
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hconst : (∑ _ : ι, B / (Fintype.card ι : ℝ)) = B := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  linarith

/-- The complex-average comparison rewritten in terms of its two marginal
laws and the cost of their coupling. -/
theorem complex_average_comparison_coupling (π : Coupling μ ν)
    (h₀ η₀ : S → ℂ) (h₁ η₁ : T → ℂ) (d : S → T → ℝ) (A δ : ℝ)
    (hδ : δ ≤ 1 / 8)
    (hh₀ : ∀ x, ‖h₀ x‖ ≤ 1 / 8) (hh₁ : ∀ y, ‖h₁ y‖ ≤ 1 / 8)
    (hη₀ : ∀ x, ‖η₀ x‖ ≤ δ) (hη₁ : ∀ y, ‖η₁ y‖ ≤ δ)
    (hlip : ∀ x y, ‖h₀ x - h₁ y‖ ≤ A * d x y) :
    ‖Complex.log (expectComplex μ (fun x => Complex.exp (h₀ x + η₀ x))) -
      Complex.log (expectComplex ν (fun y => Complex.exp (h₁ y + η₁ y)))‖ ≤
      2 * A * π.cost d + 4 * δ := by
  have hcomp := complex_average_comparison (couplingLaw π).w
    (couplingLaw π).nonneg (couplingLaw π).sum_one
    (fun p => h₀ p.1) (fun p => h₁ p.2)
    (fun p => η₀ p.1) (fun p => η₁ p.2)
    (fun p => d p.1 p.2) A δ hδ
    (fun p => hh₀ p.1) (fun p => hh₁ p.2)
    (fun p => hη₀ p.1) (fun p => hη₁ p.2)
    (fun p => hlip p.1 p.2)
  change ‖Complex.log (expectComplex (couplingLaw π) (fun p => Complex.exp (h₀ p.1 + η₀ p.1))) -
      Complex.log (expectComplex (couplingLaw π) (fun p => Complex.exp (h₁ p.2 + η₁ p.2)))‖ ≤
      2 * A * expectReal (couplingLaw π) (fun p => d p.1 p.2) + 4 * δ at hcomp
  rw [expectComplex_couplingLaw_left π (fun x => Complex.exp (h₀ x + η₀ x)),
    expectComplex_couplingLaw_right π (fun y => Complex.exp (h₁ y + η₁ y)),
    expectReal_couplingLaw_cost π d] at hcomp
  exact hcomp

/-- The marginal complex-average comparison with optimal transport cost.
The infimum argument also covers `A = 0`. -/
theorem complex_average_comparison_W
    (h₀ η₀ : S → ℂ) (h₁ η₁ : T → ℂ) (d : S → T → ℝ) {A : ℝ} (hA : 0 ≤ A) (δ : ℝ)
    (hδ : δ ≤ 1 / 8)
    (hh₀ : ∀ x, ‖h₀ x‖ ≤ 1 / 8) (hh₁ : ∀ y, ‖h₁ y‖ ≤ 1 / 8)
    (hη₀ : ∀ x, ‖η₀ x‖ ≤ δ) (hη₁ : ∀ y, ‖η₁ y‖ ≤ δ)
    (hlip : ∀ x y, ‖h₀ x - h₁ y‖ ≤ A * d x y) :
    ‖Complex.log (expectComplex μ (fun x => Complex.exp (h₀ x + η₀ x))) -
      Complex.log (expectComplex ν (fun y => Complex.exp (h₁ y + η₁ y)))‖ ≤
      2 * A * W d μ ν + 4 * δ := by
  let C := ‖Complex.log (expectComplex μ (fun x => Complex.exp (h₀ x + η₀ x))) -
      Complex.log (expectComplex ν (fun y => Complex.exp (h₁ y + η₁ y)))‖
  have hcost : ∀ π : Coupling μ ν, C ≤ 2 * A * π.cost d + 4 * δ := fun π =>
    complex_average_comparison_coupling π h₀ η₀ h₁ η₁ d A δ hδ hh₀ hh₁ hη₀ hη₁ hlip
  rcases eq_or_lt_of_le hA with hA | hA
  · simpa [← hA] using hcost (Coupling.prod μ ν)
  · have h2A : 0 < 2 * A := by positivity
    have hW : (C - 4 * δ) / (2 * A) ≤ W d μ ν := by
      apply le_W
      intro π
      apply (div_le_iff₀ h2A).2
      have hπ := hcost π
      nlinarith
    have h := (div_le_iff₀ h2A).1 hW
    change C ≤ _
    nlinarith

/-- A pushforward through a deterministic map, built from the existing
finite kernel operation. -/
def mapLaw (μ : FinDist S) (f : S → T) : FinDist T := by
  classical
  exact μ.bind (fun x => FinDist.pure (f x))

/-- Apply deterministic maps to the two coordinates of a coupling. -/
def mapCoupling {S' T' : Type*} [Fintype S'] [Fintype T']
    (π : Coupling μ ν) (f : S → S') (g : T → T') :
    Coupling (mapLaw μ f) (mapLaw ν g) := by
  classical
  exact π.mixBind (fun x => FinDist.pure (f x)) (fun y => FinDist.pure (g y))
    (fun x y => Coupling.prod (FinDist.pure (f x)) (FinDist.pure (g y)))

theorem cost_mapCoupling {S' T' : Type*} [Fintype S'] [Fintype T']
    (π : Coupling μ ν) (f : S → S') (g : T → T') (d : S' → T' → ℝ) :
    (mapCoupling π f g).cost d = π.cost (fun x y => d (f x) (g y)) := by
  classical
  change (π.mixBind (fun x => FinDist.pure (f x)) (fun y => FinDist.pure (g y))
    (fun x y => Coupling.prod (FinDist.pure (f x)) (FinDist.pure (g y)))).cost d = _
  rw [Coupling.mixBind_cost]
  simp only [Coupling.cost, Coupling.prod, FinDist.pure]
  simp

/-- Projection cannot increase transport beyond the pulled-back cost. -/
theorem W_mapLaw_le {S' T' : Type*} [Fintype S'] [Fintype T']
    (f : S → S') (g : T → T') (d : S' → T' → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) :
    W d (mapLaw μ f) (mapLaw ν g) ≤ W (fun x y => d (f x) (g y)) μ ν := by
  apply le_W
  intro π
  calc
    W d (mapLaw μ f) (mapLaw ν g) ≤ (mapCoupling π f g).cost d := W_le_cost hd _
    _ = π.cost (fun x y => d (f x) (g y)) := cost_mapCoupling π f g d

section HammingShells

variable {V C ι : Type*} [Fintype V]
variable [DecidableEq C] [DecidableEq ι]

/-- Each vertex belongs to at most one shell. `none` labels vertices outside
the selected shell family. This represents disjoint graph-distance spheres
without imposing additional graph hypotheses on the averaging lemma. -/
def shellHam (shellOf : V → Option ι) (i : ι) (σ τ : V → C) : ℝ :=
  ∑ v, if shellOf v = some i then (if σ v = τ v then 0 else 1) else 0

theorem shellHam_nonneg (shellOf : V → Option ι) (i : ι) (σ τ : V → C) :
    0 ≤ shellHam shellOf i σ τ := by
  unfold shellHam
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> norm_num

theorem sum_shellHam_le_ham [Fintype ι] (shellOf : V → Option ι) (σ τ : V → C) :
    (∑ i, shellHam shellOf i σ τ) ≤ PottsCI.ham σ τ := by
  classical
  have hham : PottsCI.ham σ τ = ∑ v, if σ v = τ v then (0 : ℝ) else 1 := by
    unfold PottsCI.ham PottsCI.hamCard
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp_all
  rw [hham]
  unfold shellHam
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _
  cases shellOf v with
  | none =>
      simp only [reduceCtorEq, ↓reduceIte, Finset.sum_const_zero]
      split_ifs <;> norm_num
  | some i => simp

/-- Coupling independence gives one shell whose transport cost is reduced
by the number of shells. This is a full finite Hamming statement, rather
than a hypothesis about a preselected shell. -/
theorem exists_low_hamming_shell [Fintype C] [Fintype ι] [DecidableEq V] [Nonempty ι]
    (μ ν : FinDist (V → C)) (shellOf : V → Option ι) {B : ℝ}
    (hCI : W PottsCI.ham μ ν ≤ B) :
    ∃ i, W (shellHam shellOf i) μ ν ≤ B / Fintype.card ι := by
  exact exists_low_W_shell (μ := μ) (ν := ν) (shellHam shellOf) PottsCI.ham
    (shellHam_nonneg shellOf) (sum_shellHam_le_ham shellOf) hCI

end HammingShells

end

end ZeroFreeness
