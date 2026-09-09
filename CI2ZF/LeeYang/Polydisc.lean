import CI2ZF.LeeYang.Analytic

/-! A radius uniform in all bounded complex directions gives the full
multivariable field polydisc by one exact affine parametrization. -/
namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def scaledFieldDirection (ℓ : V → C → ℂ) (θ : ℝ) : V → C → ℂ :=
  fun v c => (ℓ v c - 1) / (θ : ℂ)

theorem scaledFieldDirection_bound (ℓ : V → C → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ θ) : DirectionBound (scaledFieldDirection ℓ θ) := by
  intro v c
  simp only [scaledFieldDirection, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hθ]
  exact (div_le_one hθ).mpr (hℓ v c)

theorem fieldLine_scaledFieldDirection (ℓ : V → C → ℂ) {θ : ℝ} (hθ : 0 < θ) :
    fieldLine (scaledFieldDirection ℓ θ) (θ : ℂ) = ℓ := by
  have ht : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ.ne'
  funext v c
  simp only [fieldLine, scaledFieldDirection]
  rw [mul_div_cancel₀ _ ht]
  ring

theorem fieldPartition_ne_zero_of_all_curves (I : PinningData V C)
    {r θ : ℝ} (hθ : 0 < θ) (hθr : θ < r)
    (hNZ : ∀ d, DirectionBound d → CurveNonzeroOn I d r)
    (ℓ : V → C → ℂ) (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ θ) : fieldPartition I ℓ ≠ 0 := by
  have hz : (θ : ℂ) ∈ Metric.ball 0 r := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hθ] using hθr
  have hn := hNZ (scaledFieldDirection ℓ θ) (scaledFieldDirection_bound ℓ hθ hℓ) (θ : ℂ) hz
  simpa only [fieldCurve, fieldLine_scaledFieldDirection ℓ hθ] using hn

theorem field_ne_zero_of_close {ℓ : V → C → ℂ} {θ : ℝ} (hθ : θ < 1)
    (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ θ) (v : V) (c : C) : ℓ v c ≠ 0 := by
  intro hz
  have hh := hℓ v c
  rw [hz] at hh
  norm_num at hh
  exact (hθ.trans_le hh).false

end
end CI2ZF.LeeYang
