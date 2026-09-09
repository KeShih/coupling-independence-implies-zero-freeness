import CI2ZF.Coupling.Girth.Spectral.Hoeffding
import CI2ZF.Coupling.Foundations.CommonCoins

/-! Exact finite disintegration algebra for the insertion residual.
The outer distribution may have arbitrary dependencies. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω Λ C U O : Type*} [Fintype Ω] [Fintype Λ] [Fintype C] [Fintype U] [Fintype O]

theorem expectReal_add (μ : FinDist Ω) (f g : Ω → ℝ) :
    expectReal μ (fun ω => f ω + g ω) = expectReal μ f + expectReal μ g := by
  simp only [expectReal, mul_add, Finset.sum_add_distrib]

theorem expectReal_sub (μ : FinDist Ω) (f g : Ω → ℝ) :
    expectReal μ (fun ω => f ω - g ω) = expectReal μ f - expectReal μ g := by
  simp only [expectReal, mul_sub, Finset.sum_sub_distrib]

theorem expectReal_mul_const (μ : FinDist Ω) (f : Ω → ℝ) (a : ℝ) :
    expectReal μ (fun ω => f ω * a) = expectReal μ f * a := by
  simp only [expectReal, ← mul_assoc, Finset.sum_mul]

theorem expectReal_sum (μ : FinDist Ω) (f : U → Ω → ℝ) :
    expectReal μ (fun ω => ∑ u, f u ω) = ∑ u, expectReal μ (f u) := by
  simp only [expectReal, Finset.mul_sum]
  exact Finset.sum_comm

/-- A joint law assembled from its marginal and its actual conditional
kernel, including zero-mass fibres. -/
def kernelJoint (μ : FinDist Ω) (K : Ω → FinDist Λ) : FinDist (Ω × Λ) where
  w p := μ.w p.1 * (K p.1).w p.2
  nonneg p := mul_nonneg (μ.nonneg p.1) ((K p.1).nonneg p.2)
  sum_one := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, FinDist.sum_one, mul_one]

theorem expectReal_kernelJoint (μ : FinDist Ω) (K : Ω → FinDist Λ) (f : Ω × Λ → ℝ) :
    expectReal (kernelJoint μ K) f = expectReal μ (fun ω => expectReal (K ω) (fun t => f (ω,t))) := by
  simp only [expectReal, kernelJoint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem covariance_kernelJoint (μ : FinDist Ω) (K : Ω → FinDist Λ) (f g : Ω × Λ → ℝ) :
    covariance (kernelJoint μ K) f g =
      expectReal μ (fun ω => covariance (K ω) (fun t => f (ω,t)) (fun t => g (ω,t))) +
      covariance μ (fun ω => expectReal (K ω) (fun t => f (ω,t)))
        (fun ω => expectReal (K ω) (fun t => g (ω,t))) := by
  simp only [covariance_eq_moment, expectReal_kernelJoint, expectReal_sub]
  ring

theorem variance_kernelJoint (μ : FinDist Ω) (K : Ω → FinDist Λ) (f : Ω × Λ → ℝ) :
    variance (kernelJoint μ K) f =
      expectReal μ (fun ω => variance (K ω) (fun t => f (ω,t))) +
      variance μ (fun ω => expectReal (K ω) (fun t => f (ω,t))) := by
  simpa only [covariance_self] using covariance_kernelJoint μ K f f

/-- The second-layer model retains the full conditional exterior law;
only the neighbours become independent after the second layer is fixed. -/
structure InsertionModel (Ω U O C : Type*) [Fintype Ω] [Fintype U] [Fintype O] [Fintype C] where
  shell : FinDist Ω
  cavity : Ω → U → FinDist C
  exterior : Ω → FinDist O

namespace InsertionModel
variable [DecidableEq C] [DecidableEq U]
variable (M : InsertionModel Ω U O C)

def conditionalLaw (ξ : Ω) : FinDist ((U → C) × O) :=
  kernelJoint (CI2ZF.productLaw (M.cavity ξ)) (fun _ => M.exterior ξ)

def law : FinDist (Ω × ((U → C) × O)) := kernelJoint M.shell M.conditionalLaw

def pi (u : U) (c : C) (ξ : Ω) : ℝ := (M.cavity ξ u).w c

def p (u : U) (c : C) : ℝ := expectReal M.shell (M.pi u c)

def F (_M : InsertionModel Ω U O C) (s : ℝ) (c : C) (σ : U → C) : ℝ := ∏ u, (1 - s * colourIndicator c (σ u))

def Y (s : ℝ) (c : C) (ξ : Ω) : ℝ := ∏ u, (1 - s * M.pi u c ξ)

def T (s : ℝ) (c : C) : ℝ := expectReal M.shell (M.Y s c)

def alpha (s : ℝ) (u : U) (c : C) : ℝ := s / (1 - s * M.p u c)

def residual (s : ℝ) (c : C) (σ : U → C) : ℝ :=
  M.F s c σ / M.T s c - 1 + ∑ u, M.alpha s u c * (colourIndicator c (σ u) - M.p u c)

def G (s : ℝ) (c : C) (ξ : Ω) : ℝ :=
  M.Y s c ξ / M.T s c - 1 + ∑ u, M.alpha s u c * (M.pi u c ξ - M.p u c)

def beta (s : ℝ) (u : U) (c : C) (ξ : Ω) : ℝ :=
  M.alpha s u c - (s / M.T s c) * ∏ j ∈ Finset.univ.erase u, (1 - s * M.pi j c ξ)

theorem expect_F (s : ℝ) (c : C) (ξ : Ω) :
    expectReal (CI2ZF.productLaw (M.cavity ξ)) (M.F s c) = M.Y s c ξ := by
  change expectReal (CI2ZF.productLaw (M.cavity ξ))
    (fun σ => ∏ u, (1 - s * colourIndicator c (σ u))) = ∏ u, (1 - s * M.pi u c ξ)
  rw [CI2ZF.expectReal_productLaw (M.cavity ξ) (fun _ t => 1 - s * colourIndicator c t)]
  apply Finset.prod_congr rfl
  intro u _
  rw [expectReal_sub, expectReal_const, expectReal_const_mul, expect_colourIndicator]
  rfl

theorem expect_residual (s : ℝ) (c : C) (ξ : Ω) :
    expectReal (CI2ZF.productLaw (M.cavity ξ)) (M.residual s c) = M.G s c ξ := by
  change expectReal (CI2ZF.productLaw (M.cavity ξ))
    (fun σ => M.F s c σ / M.T s c - 1 + ∑ u, M.alpha s u c * (colourIndicator c (σ u) - M.p u c)) = _
  simp only [div_eq_mul_inv, expectReal_add, expectReal_sub,
    expectReal_mul_const, expectReal_const, expectReal_sum, expectReal_const_mul]
  rw [M.expect_F]
  simp_rw [CI2ZF.expectReal_product_coordinate, expect_colourIndicator]
  rfl

theorem conditional_residual (s : ℝ) (c : C) (ξ : Ω) :
    expectReal (M.conditionalLaw ξ) (fun τ => M.residual s c τ.1) = M.G s c ξ := by
  rw [conditionalLaw, expectReal_kernelJoint]
  simp only [expectReal_const]
  exact M.expect_residual s c ξ

theorem residual_mean (s : ℝ) (c : C) (hT : M.T s c ≠ 0) :
    expectReal M.law (fun σ => M.residual s c σ.2.1) = 0 := by
  rw [law, expectReal_kernelJoint]
  simp_rw [M.conditional_residual]
  simp only [G, div_eq_mul_inv, expectReal_add, expectReal_sub,
    expectReal_mul_const, expectReal_const, expectReal_sum, expectReal_const_mul]
  change M.T s c * (M.T s c)⁻¹ - 1 + ∑ u, M.alpha s u c * (M.p u c - M.p u c) = 0
  simp [hT]

/-- Exact source split. The remaining exterior source stays present in
its conditional expectation and is never discarded. -/
theorem source_decomposition (s : ℝ) (c : C) (f : Ω × ((U → C) × O) → ℝ) :
    covariance M.law f (fun σ => M.residual s c σ.2.1) =
      expectReal M.shell (fun ξ => covariance (M.conditionalLaw ξ)
        (fun τ => f (ξ,τ)) (fun τ => M.residual s c τ.1)) +
      covariance M.shell (fun ξ => expectReal (M.conditionalLaw ξ) (fun τ => f (ξ,τ))) (M.G s c) := by
  rw [law, covariance_kernelJoint]
  simp_rw [M.conditional_residual]

end InsertionModel
end
end CI2ZF.Appendix.Girth
