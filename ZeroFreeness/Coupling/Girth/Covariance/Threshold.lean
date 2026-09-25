import ZeroFreeness.Coupling.Girth.Covariance.Constants
import ZeroFreeness.Coupling.Girth.Covariance.Reference.Marginal

/-! A uniform finite degree threshold closing both covariance recursions.
All thresholds depend only on delta. This supplies an explicit version
of the asymptotic choice of chi in the appendix. -/
namespace ZeroFreeness.Appendix.Girth
noncomputable section

def covarianceT (δ : ℝ) : ℝ := 1 / (1 + δ)
def covarianceLambda (δ : ℝ) : ℝ := (Real.log (1 + δ) + δ / (1 + δ)) / 2
def covarianceChi (δ : ℝ) : ℝ := Real.exp (covarianceLambda δ / 4)
def covarianceHalfRate (δ : ℝ) : ℝ := Real.exp (-covarianceLambda δ / 2)
def covarianceEpsilon0 (δ : ℝ) : ℝ := Real.sqrt (1 / δ) * covarianceK0 δ

def covarianceDegreeThreshold (δ : ℝ) : ℝ :=
  max (4 * (covarianceE0 δ + 3 / δ) / covarianceLambda δ)
    ((4 * covarianceEpsilon0 δ * covarianceChi δ ^ 2 / (1 - covarianceHalfRate δ)) ^ 2)

theorem covarianceT_pos {δ : ℝ} (hδ : 0 < δ) : 0 < covarianceT δ := by
  unfold covarianceT
  positivity

theorem covarianceT_le_one {δ : ℝ} (hδ : 0 < δ) : covarianceT δ ≤ 1 := by
  unfold covarianceT
  exact (div_le_one (by positivity)).mpr (by linarith)

theorem covarianceLambda_pos {δ : ℝ} (hδ : 0 < δ) : 0 < covarianceLambda δ := by
  unfold covarianceLambda
  exact div_pos (add_pos (Real.log_pos (by linarith)) (div_pos hδ (by linarith))) (by norm_num)

theorem covarianceChi_gt_one {δ : ℝ} (hδ : 0 < δ) : 1 < covarianceChi δ := by
  apply Real.one_lt_exp_iff.mpr
  exact div_pos (covarianceLambda_pos hδ) (by norm_num)

theorem covarianceHalfRate_lt_one {δ : ℝ} (hδ : 0 < δ) : covarianceHalfRate δ < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hh := covarianceLambda_pos hδ
  linarith

theorem logChord_le_linear {B : ℝ} (hB0 : 0 < B) (hB : B ≤ 1 / 2) :
    logChord B ≤ 1 + 2 * B := by
  have hB1 : B < 1 := by linarith
  apply (logChord_le hB0 hB1).trans
  apply (div_le_iff₀ (sub_pos.mpr hB1)).mpr
  nlinarith

theorem neg_log_one_sub_le_twice {B : ℝ} (hB0 : 0 < B) (hB : B ≤ 1 / 2) :
    -Real.log (1 - B) ≤ 2 * B := by
  have hh := logChord_le hB0 (by linarith : B < 1)
  have hh' := (div_le_iff₀ hB0).mp hh
  have hb : 1 / (1 - B) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - B)).mpr
    linarith
  exact hh'.trans (mul_le_mul_of_nonneg_right hb hB0.le)

theorem referenceResponseCoefficient_exp {δ E B : ℝ} (hδ : 0 < δ) (hB : B < 1) :
    referenceResponseCoefficient E B (covarianceT δ) =
      Real.exp (-covarianceLambda δ + E + covarianceT δ * (logChord B - 1) / 2 -
        Real.log (1 - B)) := by
  have ht := covarianceT_pos hδ
  have hx : 0 < covarianceT δ * Real.exp (covarianceT δ * logChord B - 1) :=
    mul_pos ht (Real.exp_pos _)
  have hlog : Real.log (covarianceT δ) = -Real.log (1 + δ) := by
    simp only [covarianceT, one_div, Real.log_inv]
  have hratio : covarianceT δ - 1 = -δ / (1 + δ) := by
    unfold covarianceT
    field_simp
    ring
  have he : (Real.log (covarianceT δ) + (covarianceT δ * logChord B - 1)) / 2 =
      -covarianceLambda δ + covarianceT δ * (logChord B - 1) / 2 := by
    rw [hlog]
    unfold covarianceLambda
    simp only [neg_div] at hratio
    nlinarith only [hratio]
  unfold referenceResponseCoefficient
  rw [← Real.exp_log hx, ← Real.exp_half,
    Real.log_mul ht.ne' (Real.exp_pos _).ne', Real.log_exp, he]
  rw [← Real.exp_add, ← Real.exp_log (sub_pos.mpr hB), ← Real.exp_sub]
  simp only [Real.log_exp]
  congr 1
  ring

theorem referenceResponseCoefficient_upper {δ E B : ℝ} (hδ : 0 < δ)
    (hB0 : 0 < B) (hB : B ≤ 1 / 2) :
    referenceResponseCoefficient E B (covarianceT δ) ≤
      Real.exp (-covarianceLambda δ + E + 3 * B) := by
  rw [referenceResponseCoefficient_exp hδ (by linarith : B < 1)]
  apply Real.exp_le_exp.mpr
  have ht0 := (covarianceT_pos hδ).le
  have ht1 := covarianceT_le_one hδ
  have he := logChord_le_linear hB0 hB
  have hh := neg_log_one_sub_le_twice hB0 hB
  have hm := mul_le_mul_of_nonneg_left (show logChord B - 1 ≤ 2 * B by linarith) ht0
  have htB := mul_le_mul_of_nonneg_right ht1 hB0.le
  nlinarith only [hm, htB, hh]

namespace CovarianceScale
variable (p : CovarianceScale)

def responseCoefficient : ℝ := referenceResponseCoefficient p.E p.B (covarianceT p.δ)

theorem responseCoefficient_nonneg : 0 ≤ p.responseCoefficient := by
  unfold responseCoefficient referenceResponseCoefficient
  apply div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  linarith [p.B_le_half]

theorem error_margin (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) :
    p.E + 3 * p.B ≤ covarianceLambda p.δ / 4 := by
  have hlambda := covarianceLambda_pos p.delta_pos
  have hlarge' : 4 * (covarianceE0 p.δ + 3 / p.δ) / covarianceLambda p.δ ≤ p.Δ :=
    (le_max_left _ _).trans hlarge
  have hmul := (div_le_iff₀ hlambda).mp hlarge'
  calc
    _ ≤ covarianceE0 p.δ / p.Δ + 3 * (1 / (p.δ * p.Δ)) :=
      add_le_add p.E_le (mul_le_mul_of_nonneg_left p.B_le (by norm_num))
    _ = (covarianceE0 p.δ + 3 / p.δ) / p.Δ := by ring
    _ ≤ covarianceLambda p.δ / 4 := by
      apply (div_le_iff₀ p.Δ_pos).mpr
      nlinarith only [hmul]

theorem response_chi_le (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) :
    p.responseCoefficient * covarianceChi p.δ ≤ covarianceHalfRate p.δ := by
  calc
    _ ≤ Real.exp (-covarianceLambda p.δ + p.E + 3 * p.B) * covarianceChi p.δ :=
      mul_le_mul_of_nonneg_right (referenceResponseCoefficient_upper p.delta_pos p.B_pos p.B_le_half)
        (Real.exp_pos _).le
    _ = Real.exp (-covarianceLambda p.δ + p.E + 3 * p.B + covarianceLambda p.δ / 4) := by
      unfold covarianceChi
      rw [← Real.exp_add]
    _ ≤ covarianceHalfRate p.δ := by
      apply Real.exp_le_exp.mpr
      have hh := p.error_margin hlarge
      linarith

theorem epsilon_margin (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) :
    p.a * p.epsilon * covarianceChi p.δ ^ 2 ≤ (1 - covarianceHalfRate p.δ) / 2 := by
  have hmargin : 0 < 1 - covarianceHalfRate p.δ := sub_pos.mpr (covarianceHalfRate_lt_one p.delta_pos)
  have he0 : 0 ≤ covarianceEpsilon0 p.δ := by
    unfold covarianceEpsilon0 covarianceK0
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) p.b0_nonneg)
  have hthr : (4 * covarianceEpsilon0 p.δ * covarianceChi p.δ ^ 2 /
      (1 - covarianceHalfRate p.δ)) ^ 2 ≤ p.Δ := (le_max_right _ _).trans hlarge
  have hsqrt : 4 * covarianceEpsilon0 p.δ * covarianceChi p.δ ^ 2 /
      (1 - covarianceHalfRate p.δ) ≤ Real.sqrt p.Δ := by
    exact (Real.le_sqrt (by positivity) p.Δ_pos.le).mpr hthr
  have hmul := (div_le_iff₀ hmargin).mp hsqrt
  have heps : p.epsilon ≤ covarianceEpsilon0 p.δ / Real.sqrt p.Δ := p.epsilon_le
  calc
    _ ≤ 2 * (covarianceEpsilon0 p.δ / Real.sqrt p.Δ) * covarianceChi p.δ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul p.a_le_two heps p.epsilon_nonneg (by norm_num)) (sq_nonneg _)
    _ = (2 * covarianceEpsilon0 p.δ * covarianceChi p.δ ^ 2) / Real.sqrt p.Δ := by ring
    _ ≤ (1 - covarianceHalfRate p.δ) / 2 := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr p.Δ_pos)).mpr
      nlinarith only [hmul]

theorem covariance_coefficients_contract (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) :
    covarianceAU p.responseCoefficient p.a p.epsilon (covarianceChi p.δ) < 1 ∧
      covarianceAV p.responseCoefficient (covarianceChi p.δ) < 1 := by
  have hr := p.response_chi_le hlarge
  have he := p.epsilon_margin hlarge
  have hh := covarianceHalfRate_lt_one p.delta_pos
  constructor
  · unfold covarianceAU
    linarith
  · exact hr.trans_lt hh

end CovarianceScale
end
end ZeroFreeness.Appendix.Girth
