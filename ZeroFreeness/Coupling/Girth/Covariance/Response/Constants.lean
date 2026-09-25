import ZeroFreeness.Coupling.Girth.Covariance.Threshold
import ZeroFreeness.Coupling.Girth.Spectral.Threshold

/-! Explicit final degree threshold and finite simultaneous response
constants, with no asymptotic or contraction hypothesis left over. -/
namespace ZeroFreeness.Appendix.Girth
noncomputable section

def girthFiveCIThreshold (δ : ℝ) : ℕ :=
  max (girthFiveThreshold δ) ⌈covarianceDegreeThreshold δ⌉₊

theorem girthFiveCIThreshold_gap {δ : ℝ} {Δ : ℕ}
    (hΔ : girthFiveCIThreshold δ ≤ Δ) : girthFiveThreshold δ ≤ Δ :=
  (le_max_left _ _).trans hΔ

theorem girthFiveCIThreshold_covariance {δ : ℝ} {Δ : ℕ}
    (hΔ : girthFiveCIThreshold δ ≤ Δ) : covarianceDegreeThreshold δ ≤ (Δ : ℝ) :=
  Nat.ceil_le.mp ((le_max_right _ _).trans hΔ)

def actualCovarianceScale {δ : ℝ} {Δ q : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hΔ : girthFiveThreshold δ ≤ Δ) (hq : (1+δ) * Δ ≤ (q : ℝ)) : CovarianceScale where
  δ := δ
  Δ := Δ
  q := q
  delta_pos := hδ
  degree_one := by
    have hpos : 0 < Δ := by exact_mod_cast (girthFiveThreshold_bounds hδ hδ1 hΔ).1
    exact_mod_cast hpos
  degree_large := (girthFiveThreshold_bounds hδ hδ1 hΔ).2.1
  colour_budget := by nlinarith

namespace CovarianceScale
variable (p : CovarianceScale)

def responseU : ℝ := covarianceUStar p.responseCoefficient p.a p.epsilon (covarianceChi p.δ) p.ell
def responseV : ℝ := covarianceVStar p.responseCoefficient p.a p.epsilon (covarianceChi p.δ) p.ell p.K
def responseM : ℝ := covarianceMStar p.responseCoefficient p.a p.epsilon (covarianceChi p.δ)
  p.ell p.K (p.Δ * p.B)

theorem response_supersolutions (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) :
    0 ≤ p.responseU ∧ 0 ≤ p.responseV ∧
    covarianceAU p.responseCoefficient p.a p.epsilon (covarianceChi p.δ) * p.responseU +
      p.a * (1 + p.ell * covarianceChi p.δ) = p.responseU ∧
    covarianceAV p.responseCoefficient (covarianceChi p.δ) * p.responseV +
      (covarianceAV p.responseCoefficient (covarianceChi p.δ) +
        2 * p.a * p.K * covarianceChi p.δ ^ 2) * p.responseU +
      2 * p.a * (1 + p.ell * covarianceChi p.δ) = p.responseV := by
  have hc := p.covariance_coefficients_contract hlarge
  exact covariance_supersolution p.responseCoefficient_nonneg p.a_pos.le p.epsilon_nonneg
    (Real.exp_pos _).le p.ell_nonneg p.K_nonneg hc.1 hc.2

theorem responseU_nonneg (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) : 0 ≤ p.responseU :=
  (p.response_supersolutions hlarge).1

theorem responseV_nonneg (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) : 0 ≤ p.responseV :=
  (p.response_supersolutions hlarge).2.1

theorem responseM_pos (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) : 0 < p.responseM := by
  have hu := p.responseU_nonneg hlarge
  have hv := p.responseV_nonneg hlarge
  have hk := p.K_nonneg
  have hel := p.ell_nonneg
  have hd := p.Δ_pos
  have hb := p.B_pos
  change 0 < 2 * (1 + p.ell * covarianceChi p.δ + p.K * covarianceChi p.δ ^ 2 * p.responseU) +
    2 * (p.Δ * p.B) * covarianceChi p.δ * p.responseV
  unfold covarianceChi
  positivity

end CovarianceScale
end
end ZeroFreeness.Appendix.Girth
