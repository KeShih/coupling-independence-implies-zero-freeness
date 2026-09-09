import CI2ZF.Analysis.PaperComplexAverage

/-!
# The analytic estimates in the Holant induction

The shell error is additive. In particular no local coefficient at the
real base point is divided by: that coefficient can vanish at zero edge
activities. These lemmas prove the quantitative analytic step; the graph
separator and recursive coupling must supply their explicitly stated inputs.
-/

namespace CI2ZF.Holant

open PottsCI PottsCI.FinDist
noncomputable section

variable {S : Type*} [Fintype S]

def exponentialAverage (μ : FinDist S) (h : S → ℂ) : ℂ :=
  expectComplex μ (fun s => Complex.exp (h s))

theorem exponentialAverage_center (μ : FinDist S) (h : S → ℂ) (b : S) :
    exponentialAverage μ h = Complex.exp (h b) *
      expectComplex μ (fun s => Complex.exp (h s - h b)) := by
  simpa [exponentialAverage] using expectComplex_exp_center μ h (fun _ => 0) (h b)

theorem exponentialAverage_center_bound (μ : FinDist S) (h : S → ℂ) (b : S)
    (hh : ∀ s, ‖h s - h b‖ ≤ (1 / 8 : ℝ)) :
    ‖exponentialAverage μ h / Complex.exp (h b) - 1‖ ≤ (1 / 3 : ℝ) := by
  rw [exponentialAverage_center μ h b, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  exact norm_complexAverage_exp_sub_one_le μ.w μ.nonneg μ.sum_one _
    (fun s => (hh s).trans (by norm_num))

theorem exponentialAverage_lower (μ : FinDist S) (h : S → ℂ) (b : S)
    (hh : ∀ s, ‖h s - h b‖ ≤ (1 / 8 : ℝ)) :
    (2 / 3 : ℝ) * ‖Complex.exp (h b)‖ ≤ ‖exponentialAverage μ h‖ := by
  have hbound := exponentialAverage_center_bound μ h b hh
  have ht := norm_sub_norm_le (1 : ℂ) (exponentialAverage μ h / Complex.exp (h b))
  rw [norm_one, norm_sub_rev, norm_div] at ht
  have hp : 0 < ‖Complex.exp (h b)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hr : (2 / 3 : ℝ) ≤ ‖exponentialAverage μ h‖ / ‖Complex.exp (h b)‖ := by
    linarith
  exact (le_div_iff₀ hp).mp hr

theorem exponentialAverage_ne_zero (μ : FinDist S) (h : S → ℂ) (b : S)
    (hh : ∀ s, ‖h s - h b‖ ≤ (1 / 8 : ℝ)) : exponentialAverage μ h ≠ 0 := by
  have hp : 0 < ‖Complex.exp (h b)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hl := exponentialAverage_lower μ h b hh
  exact norm_pos_iff.mp (by linarith)

theorem relative_shell_error_le (μ : FinDist S) (h : S → ℂ) (b : S)
    (hh : ∀ s, ‖h s - h b‖ ≤ (1 / 8 : ℝ))
    (E : ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ‖E‖ ≤ δ * ‖Complex.exp (h b)‖) :
    ‖E / exponentialAverage μ h‖ ≤ (3 / 2 : ℝ) * δ := by
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr (exponentialAverage_ne_zero μ h b hh))).mpr
  have hl := mul_le_mul_of_nonneg_left (exponentialAverage_lower μ h b hh)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hδ)
  nlinarith

theorem norm_log_one_add_le (u : ℂ) (hu : ‖u‖ ≤ (1 / 3 : ℝ)) :
    ‖Complex.log (1 + u)‖ ≤ (3 / 2 : ℝ) * ‖u‖ := by
  have h := norm_log_sub_log_le_three_halves (1 + u) 1
    (by simpa using hu) (by norm_num)
  simpa using h

theorem one_add_ne_zero (u : ℂ) (hu : ‖u‖ ≤ (1 / 3 : ℝ)) : 1 + u ≠ 0 := by
  intro hz
  have he : u = -1 := by linear_combination hz
  rw [he] at hu
  norm_num at hu

/-- The explicit corrected branch, with numerator law first. -/
def additiveResponseLog (μ ν : FinDist S) (h : S → ℂ) (b : S) (E F : ℂ) : ℂ :=
  centeredAverageLogRatio μ ν h (fun _ => 0) (fun _ => 0) b +
    Complex.log (1 + E / exponentialAverage μ h) -
    Complex.log (1 + F / exponentialAverage ν h)

/-- Additive local errors preserve both averages and give the response
bound `2 A W + 9 δ / 2`. The reference exponential need not be small. -/
theorem additive_response (μ ν : FinDist S) (h : S → ℂ) (b : S)
    (d : S → S → ℝ) {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ 2 / 9)
    (hlip : ∀ s t, ‖h s - h t‖ ≤ A * d s t)
    (hosc : ∀ s t, ‖h s - h t‖ ≤ (1 / 8 : ℝ))
    (E F : ℂ) (hE : ‖E‖ ≤ δ * ‖Complex.exp (h b)‖)
    (hF : ‖F‖ ≤ δ * ‖Complex.exp (h b)‖) :
    exponentialAverage μ h + E ≠ 0 ∧ exponentialAverage ν h + F ≠ 0 ∧
    Complex.exp (additiveResponseLog μ ν h b E F) =
      (exponentialAverage μ h + E) / (exponentialAverage ν h + F) ∧
    ‖additiveResponseLog μ ν h b E F‖ ≤ 2 * A * W d μ ν + (9 / 2) * δ := by
  have hμ := exponentialAverage_ne_zero μ h b (fun s => hosc s b)
  have hν := exponentialAverage_ne_zero ν h b (fun s => hosc s b)
  have hu := relative_shell_error_le μ h b (fun s => hosc s b) E hδ hE
  have hv := relative_shell_error_le ν h b (fun s => hosc s b) F hδ hF
  have hu' : ‖E / exponentialAverage μ h‖ ≤ (1 / 3 : ℝ) := by linarith
  have hv' : ‖F / exponentialAverage ν h‖ ≤ (1 / 3 : ℝ) := by linarith
  have hmu := one_add_ne_zero _ hu'
  have hnv := one_add_ne_zero _ hv'
  have hfμ : exponentialAverage μ h + E =
      exponentialAverage μ h * (1 + E / exponentialAverage μ h) := by field_simp
  have hfν : exponentialAverage ν h + F =
      exponentialAverage ν h * (1 + F / exponentialAverage ν h) := by field_simp
  have hav := paper_complex_average_with_anchor μ ν h (fun _ => 0) (fun _ => 0) d
    hA (δ := 0) (by norm_num) hlip hosc (by simp) (by simp) b
  refine ⟨by rw [hfμ]; exact mul_ne_zero hμ hmu,
    by rw [hfν]; exact mul_ne_zero hν hnv, ?_, ?_⟩
  · rw [additiveResponseLog, Complex.exp_sub, Complex.exp_add, Complex.exp_log hmu,
      Complex.exp_log hnv, hav.2.2.1]
    simp only [add_zero]
    change exponentialAverage μ h / exponentialAverage ν h * _ / _ = _
    rw [hfμ, hfν]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · have hl := norm_log_one_add_le _ hu'
    have hr := norm_log_one_add_le _ hv'
    have hbase := hav.2.2.2
    have ht := norm_sub_le
      (centeredAverageLogRatio μ ν h (fun _ => 0) (fun _ => 0) b +
        Complex.log (1 + E / exponentialAverage μ h))
      (Complex.log (1 + F / exponentialAverage ν h))
    have ht' := norm_add_le
      (centeredAverageLogRatio μ ν h (fun _ => 0) (fun _ => 0) b)
      (Complex.log (1 + E / exponentialAverage μ h))
    change ‖_ + _ - _‖ ≤ _
    linarith

/-- A concrete budget closes the shell response with strict slack. -/
theorem additive_response_closes (μ ν : FinDist S) (h : S → ℂ) (b : S)
    (d : S → S → ℝ) {α δ : ℝ} (hα : 0 < α) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ 2 / 9) (hδbudget : δ ≤ α / 16)
    (hW : W d μ ν ≤ 1 / 64)
    (hlip : ∀ s t, ‖h s - h t‖ ≤ α * d s t)
    (hosc : ∀ s t, ‖h s - h t‖ ≤ (1 / 8 : ℝ))
    (E F : ℂ) (hE : ‖E‖ ≤ δ * ‖Complex.exp (h b)‖)
    (hF : ‖F‖ ≤ δ * ‖Complex.exp (h b)‖) :
    ‖additiveResponseLog μ ν h b E F‖ < α := by
  have h := (additive_response μ ν h b d hα.le hδ hδsmall hlip hosc E F hE hF).2.2.2
  have hw' := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 2 * α)
  linarith

/-- The final edge recursion is nonzero under the response bound. The
activity may have base value zero, and the two real child values enter
only through their normalized ratio `r ∈ [0,1]`. -/
theorem edge_factor_ne_zero {a x r : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hr : r ∈ Set.Icc 0 1) (z ℓ : ℂ) (hℓ : ‖ℓ‖ ≤ (1 / 4 : ℝ))
    (hsmall : a * ‖z - (x : ℂ)‖ * (4 / 3) < 1) :
    1 + (a : ℂ) * z * r * Complex.exp ℓ ≠ 0 := by
  have he := norm_exp_sub_one_le_third ℓ hℓ
  have hexp : ‖Complex.exp ℓ‖ ≤ (4 / 3 : ℝ) := by
    have ht := norm_sub_norm_le (Complex.exp ℓ) (1 : ℂ)
    norm_num at ht
    linarith
  have hre : 0 ≤ (Complex.exp ℓ).re := by
    have ht := Complex.re_le_norm (1 - Complex.exp ℓ)
    rw [norm_sub_rev] at ht
    simp only [Complex.sub_re, Complex.one_re] at ht
    linarith
  have hbase : 1 ≤ (1 + (a : ℂ) * x * r * Complex.exp ℓ).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (mul_nonneg ha hx) hr.1) hre)
  have herr : ‖(a : ℂ) * (z - (x : ℂ)) * r * Complex.exp ℓ‖ < 1 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha, abs_of_nonneg hr.1]
    calc
      a * ‖z - (x : ℂ)‖ * r * ‖Complex.exp ℓ‖
          ≤ a * ‖z - (x : ℂ)‖ * 1 * (4 / 3) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left hr.2 (mul_nonneg ha (norm_nonneg _)))
              hexp (norm_nonneg _) (by positivity)
      _ < 1 := by simpa using hsmall
  intro hz
  have hid : (1 + (a : ℂ) * x * r * Complex.exp ℓ) +
      (a : ℂ) * (z - (x : ℂ)) * r * Complex.exp ℓ = 0 := by
    linear_combination hz
  have hidre := congrArg Complex.re hid
  have hb := Complex.re_le_norm (-((a : ℂ) * (z - (x : ℂ)) * r * Complex.exp ℓ))
  rw [Complex.neg_re, norm_neg] at hb
  simp only [Complex.add_re, Complex.zero_re, Complex.one_re] at hidre hbase
  linarith

end
end CI2ZF.Holant
