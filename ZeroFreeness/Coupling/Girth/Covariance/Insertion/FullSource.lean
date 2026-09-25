import ZeroFreeness.Coupling.Girth.Covariance.Insertion.LocalSource

/-! The insertion covariance for the entire additive source.  The
conditional exterior expectation is retained in the shell source. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω U O C : Type*} [Fintype Ω] [Fintype U] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq C]

theorem covariance_add_left (μ : FinDist Ω) (f g h : Ω → ℝ) :
    covariance μ (fun ω => f ω + g ω) h = covariance μ f h + covariance μ g h := by
  rw [covariance_comm, covariance_add_right]
  rw [covariance_comm μ h f, covariance_comm μ h g]

namespace InsertionModel
variable (M : InsertionModel Ω U O C)

def additiveSource (fU : U → C → ℝ) (fS : Ω → ℝ) (fO : O → ℝ)
    (σ : Ω × ((U → C) × O)) : ℝ :=
  (∑ u, fU u (σ.2.1 u)) + fS σ.1 + fO σ.2.2

def shellSource (fU : U → C → ℝ) (fS : Ω → ℝ) (fO : O → ℝ) (ξ : Ω) : ℝ :=
  (∑ u, expectReal (M.cavity ξ u) (fU u)) + fS ξ + expectReal (M.exterior ξ) fO

theorem conditional_source (fU : U → C → ℝ) (fS : Ω → ℝ) (fO : O → ℝ) (ξ : Ω) :
    expectReal (M.conditionalLaw ξ) (fun τ => additiveSource fU fS fO (ξ,τ)) =
      M.shellSource fU fS fO ξ := by
  rw [conditionalLaw, expectReal_kernelJoint]
  simp only [additiveSource, expectReal_add, expectReal_const]
  rw [expectReal_sum]
  simp_rw [ZeroFreeness.expectReal_product_coordinate]
  rfl

theorem conditional_full_covariance (s : ℝ) (c : C)
    (fU : U → C → ℝ) (fS : Ω → ℝ) (fO : O → ℝ) (ξ : Ω) :
    covariance (M.conditionalLaw ξ) (fun τ => additiveSource fU fS fO (ξ,τ))
      (fun τ => M.residual s c τ.1) =
      covariance (ZeroFreeness.productLaw (M.cavity ξ)) (fun α => ∑ u, fU u (α u))
        (M.residual s c) := by
  rw [conditionalLaw, covariance_kernelJoint]
  simp only [additiveSource, covariance_const_right, expectReal_const, zero_add,
    expectReal_add]
  rw [covariance_add_left, covariance_add_left, covariance_const_left,
    covariance_const_left, add_zero, add_zero]

/-- The full outside source contributes through its conditional mean.
Only the first-layer part enters the conditional local covariance. -/
theorem full_source_decomposition (s : ℝ) (c : C)
    (fU : U → C → ℝ) (fS : Ω → ℝ) (fO : O → ℝ) :
    covariance M.law (additiveSource fU fS fO) (fun σ => M.residual s c σ.2.1) =
      expectReal M.shell (fun ξ => covariance (ZeroFreeness.productLaw (M.cavity ξ))
        (fun α => ∑ u, fU u (α u)) (M.residual s c)) +
      covariance M.shell (M.shellSource fU fS fO) (M.G s c) := by
  rw [M.source_decomposition]
  simp_rw [M.conditional_full_covariance, M.conditional_source]

end InsertionModel
end
end ZeroFreeness.Appendix.Girth
