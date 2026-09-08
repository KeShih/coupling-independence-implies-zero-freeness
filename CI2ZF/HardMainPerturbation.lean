import CI2ZF.PaperComplexAverage
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Quantitative control of a hard-feasible main term and its additive
defect. These estimates allow zero-base inside factors. -/
namespace CI2ZF
open PottsCI PottsCI.FinDist
noncomputable section
variable {S : Type*} [Fintype S]

theorem main_average_norm_lower (μ : FinDist S) (h : S → ℂ) (anchor : S)
    (hosc : ∀ i, ‖h i - h anchor‖ ≤ (1 / 4 : ℝ)) :
    (2 / 3 : ℝ) * ‖Complex.exp (h anchor)‖ ≤
      ‖expectComplex μ (fun i => Complex.exp (h i))‖ := by
  let M := expectComplex μ (fun i => Complex.exp (h i - h anchor))
  have hb : ‖M - 1‖ ≤ (1 / 3 : ℝ) :=
    norm_complexAverage_exp_sub_one_le μ.w μ.nonneg μ.sum_one _ hosc
  have hm : (2 / 3 : ℝ) ≤ ‖M‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) M
    rw [norm_sub_rev] at ht
    norm_num at ht
    linarith
  have he := expectComplex_exp_center μ h (fun _ => 0) (h anchor)
  simp only [add_zero] at he
  rw [he, norm_mul]
  change (2 / 3 : ℝ) * ‖Complex.exp (h anchor)‖ ≤ ‖Complex.exp (h anchor)‖ * ‖M‖
  nlinarith [mul_le_mul_of_nonneg_left hm (norm_nonneg (Complex.exp (h anchor)))]

theorem main_average_ne_zero (μ : FinDist S) (h : S → ℂ) (anchor : S)
    (hosc : ∀ i, ‖h i - h anchor‖ ≤ (1 / 4 : ℝ)) :
    expectComplex μ (fun i => Complex.exp (h i)) ≠ 0 := by
  have hb := main_average_norm_lower μ h anchor hosc
  have hp : 0 < ‖Complex.exp (h anchor)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  intro hz
  rw [hz, norm_zero] at hb
  linarith

/-- A defect bound relative to one feasible witness becomes a relative
error bound against the whole hard-feasible main term. -/
theorem defect_div_main_bound (μ : FinDist S) (h : S → ℂ) (anchor : S)
    (hosc : ∀ i, ‖h i - h anchor‖ ≤ (1 / 4 : ℝ))
    (E : ℂ) {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hE : ‖E‖ ≤ K * r * ‖Complex.exp (h anchor)‖) :
    ‖E / expectComplex μ (fun i => Complex.exp (h i))‖ ≤ (3 / 2 : ℝ) * K * r := by
  have hm := main_average_norm_lower μ h anchor hosc
  have hp := norm_pos_iff.mpr (main_average_ne_zero μ h anchor hosc)
  rw [norm_div, div_le_iff₀ hp]
  have hs := mul_le_mul_of_nonneg_left hm (mul_nonneg hK hr)
  nlinarith

/-- Small defects preserve nonvanishing and admit a controlled principal
correction logarithm; its argument stays in the disk around one. -/
theorem hard_main_plus_error (μ : FinDist S) (h : S → ℂ) (anchor : S)
    (hosc : ∀ i, ‖h i - h anchor‖ ≤ (1 / 4 : ℝ))
    (E : ℂ) {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hE : ‖E‖ ≤ K * r * ‖Complex.exp (h anchor)‖)
    (hsmall : (3 / 2 : ℝ) * K * r ≤ 1 / 2) :
    let M := expectComplex μ (fun i => Complex.exp (h i))
    M + E ≠ 0 ∧
      ‖Complex.log (1 + E / M)‖ ≤ (9 / 4 : ℝ) * K * r ∧
      Complex.exp (Complex.log (1 + E / M)) = (M + E) / M := by
  dsimp only
  let M := expectComplex μ (fun i => Complex.exp (h i))
  have hm : M ≠ 0 := main_average_ne_zero μ h anchor hosc
  have hb := defect_div_main_bound μ h anchor hosc E hK hr hE
  have hhalf : ‖E / M‖ ≤ (1 / 2 : ℝ) := hb.trans hsmall
  have hone : 1 + E / M ≠ 0 := by
    intro hz
    have he : E / M = -1 := by linear_combination hz
    rw [he] at hhalf
    norm_num at hhalf
  have heq : (M + E) / M = 1 + E / M := by rw [add_div, div_self hm]
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    apply hone
    rw [← heq, hz, zero_div]
  · have hl := Complex.norm_log_one_add_half_le_self hhalf
    have hs := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 3 / 2 by norm_num)
    nlinarith
  · rw [Complex.exp_log hone]
    exact heq.symm

end
end CI2ZF
