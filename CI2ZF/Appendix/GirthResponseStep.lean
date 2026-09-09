import CI2ZF.Appendix.GirthResponseSourceBounds
import CI2ZF.Appendix.GirthResponseConstants
import CI2ZF.Appendix.GirthResponseInsertion

/-! Assembly of the two exact scalar response recursions. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]

theorem response_step_both (p : CovarianceScale) (s : ℝ) (ρ : FinDist C)
    (μ : FinDist Ω) (G : C → Ω → ℝ) (f : Ω → ℝ) (localSource block h : C → ℝ)
    {r χ A U V : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hρ : ∀ c, ρ.w c ≤ p.B)
    (hχ : 0 ≤ χ) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hG : ColourCovarianceBound μ G (p.g ^ 2))
    (hf : variance μ f ≤ (p.Δ * χ ^ 2 * A * U) ^ 2)
    (hlocal : ∀ c, |localSource c| ≤ (1 + p.ell * χ) * A)
    (hblock2 : colourNorm block ≤ r * χ * U * A)
    (hblockinf : ∀ c, |block c| ≤ r * (Real.sqrt p.B * χ * V * A + Real.sqrt p.B * χ * U * A))
    (heq : h = fun c => block c + scoreSource s ρ (fun d => localSource d + covariance μ f (G d)) c) :
    colourNorm h ≤ (covarianceAU r p.a p.epsilon χ * U + p.a * (1 + p.ell * χ)) * A ∧
    ∀ c, |h c| ≤ Real.sqrt p.B *
      (covarianceAV r χ * V + (covarianceAV r χ + 2 * p.a * p.K * χ ^ 2) * U +
        2 * p.a * (1 + p.ell * χ)) * A := by
  have hB : p.B < 1 := lt_of_le_of_lt p.B_le_half (by norm_num)
  have ha : 0 ≤ (1 + p.ell * χ) * A := by positivity [p.ell_nonneg]
  have hd : 0 ≤ p.Δ * χ ^ 2 * A * U := by positivity [p.Δ_pos]
  have hsources := scoreSource_full_both s ρ localSource μ G f hs hs1 p.B_pos.le hB hρ
    ha hlocal p.g_nonneg hd hG hf
  rw [heq]
  constructor
  · calc
      _ ≤ colourNorm block + colourNorm (scoreSource s ρ (fun d => localSource d + covariance μ f (G d))) :=
        colourNorm_add _ _
      _ ≤ r * χ * U * A + (1 / (1 - p.B)) *
          ((1 + p.ell * χ) * A + Real.sqrt p.B * p.g * (p.Δ * χ ^ 2 * A * U)) :=
        add_le_add hblock2 hsources.1
      _ = _ := by simp only [covarianceAU, CovarianceScale.a, CovarianceScale.epsilon, CovarianceScale.K]; ring
  · intro c
    calc
      _ ≤ |block c| + |scoreSource s ρ (fun d => localSource d + covariance μ f (G d)) c| := abs_add_le _ _
      _ ≤ r * (Real.sqrt p.B * χ * V * A + Real.sqrt p.B * χ * U * A) +
          2 * (1 / (1 - p.B)) * Real.sqrt p.B *
            ((1 + p.ell * χ) * A + p.g * (p.Δ * χ ^ 2 * A * U)) :=
        add_le_add (hblockinf c) (hsources.2 c)
      _ = _ := by simp only [covarianceAV, CovarianceScale.a, CovarianceScale.K]; ring

theorem response_step_supersolution (p : CovarianceScale)
    (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) {A : ℝ} (h : C → ℝ)
    (h2 : colourNorm h ≤
      (covarianceAU p.responseCoefficient p.a p.epsilon (covarianceChi p.δ) * p.responseU +
        p.a * (1 + p.ell * covarianceChi p.δ)) * A)
    (hinf : ∀ c, |h c| ≤ Real.sqrt p.B *
      (covarianceAV p.responseCoefficient (covarianceChi p.δ) * p.responseV +
        (covarianceAV p.responseCoefficient (covarianceChi p.δ) + 2 * p.a * p.K * covarianceChi p.δ ^ 2) *
          p.responseU + 2 * p.a * (1 + p.ell * covarianceChi p.δ)) * A) :
    colourNorm h ≤ p.responseU * A ∧ ∀ c, |h c| ≤ Real.sqrt p.B * p.responseV * A := by
  have hs := p.response_supersolutions hlarge
  exact ⟨by simpa only [hs.2.2.1] using h2, fun c => by simpa only [hs.2.2.2] using hinf c⟩

end
end CI2ZF.Appendix.Girth
