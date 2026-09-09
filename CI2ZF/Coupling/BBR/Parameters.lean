import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Exact parameter analysis for `thm:intro-bbr-interval` and the BBR
appendix. The unrounded parameter uses the real exponential, not a decimal
replacement. No tree contraction or graph theorem is assumed here. -/
namespace CI2ZF.Appendix.BBR
noncomputable section

def parameter (q Δ : ℝ) : ℝ := Real.exp 1 * (Δ - q / 2) / (Δ - q)

def intervalStart (q Δ : ℝ) : ℝ :=
  1 - q / Δ * (1 - parameter q Δ / Δ) ^ 2 *
    (Δ - parameter q Δ) / (Δ - parameter q Δ / 2)

/-- Multiplication of the paper's ratio hypothesis by positive denominators. -/
theorem ratio_iff {q Δ : ℝ} (hq : 0 < q) :
    (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ Δ / q ↔
      q / 2 ≤ (Δ - q) * (Real.exp 1 - 1) := by
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.exp_one_gt_two]
  rw [div_le_div_iff₀ he hq]
  constructor <;> intro h <;> nlinarith

theorem degree_gt_colours {q Δ : ℝ} (hq : 0 < q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ Δ / q) : q < Δ := by
  have hb := (ratio_iff hq).mp hr
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.exp_one_gt_two]
  by_contra hn
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hn)) he.le
  linarith

/-- Integrality isolates the exceptional `(q,Δ)=(3,4)` pair. -/
theorem integer_degree_gap {q Δ : ℕ} (hq : 3 ≤ q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / q) :
    (q = 3 ∧ Δ = 4) ∨ q + 2 ≤ Δ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hgt : q < Δ := by exact_mod_cast (degree_gt_colours hqpos hr)
  by_cases hgap : q + 2 ≤ Δ
  · exact Or.inr hgap
  have heq : Δ = q + 1 := by omega
  have hb := (ratio_iff hqpos).mp hr
  have hcast : (Δ : ℝ) = q + 1 := by exact_mod_cast heq
  rw [hcast] at hb
  have hq4 : (q : ℝ) < 4 := by nlinarith [Real.exp_one_lt_three]
  have hq4n : q < 4 := by exact_mod_cast hq4
  exact Or.inl ⟨by omega, by omega⟩

theorem parameter_pos {q Δ : ℝ} (hq : 0 < q) (hΔ : q < Δ) :
    0 < parameter q Δ := by
  unfold parameter
  exact div_pos (mul_pos (Real.exp_pos _) (by linarith)) (sub_pos.mpr hΔ)

/-- The unrounded parameter never exceeds the rounded `e²` parameter. -/
theorem parameter_le_exp_sq {q Δ : ℝ} (hq : 0 < q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ Δ / q) :
    parameter q Δ ≤ Real.exp 1 ^ 2 := by
  have hΔ := degree_gt_colours hq hr
  have hb := (ratio_iff hq).mp hr
  unfold parameter
  apply (div_le_iff₀ (sub_pos.mpr hΔ)).mpr
  nlinarith [mul_nonneg (Real.exp_pos 1).le
    (sub_nonneg.mpr hb)]

/-- For all nonexceptional integer pairs, `k` lies strictly below `Δ`. -/
theorem parameter_lt_degree {q Δ : ℕ} (hq : 3 ≤ q) (hgap : q + 2 ≤ Δ) :
    parameter q Δ < Δ := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hΔq2 : (q : ℝ) + 2 ≤ Δ := by exact_mod_cast hgap
  have he0 := Real.exp_pos 1
  have he3 := Real.exp_one_lt_three
  have he : Real.exp 1 < 11 / 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  unfold parameter
  apply (div_lt_iff₀ (by linarith : (0 : ℝ) < Δ - q)).mpr
  by_cases htwo : Δ = q + 2
  · have heq : (Δ : ℝ) = q + 2 := by exact_mod_cast htwo
    rw [heq]
    have hm := mul_nonneg (sub_nonneg.mpr hq3)
      (show 0 ≤ 2 - Real.exp 1 / 2 by linarith)
    nlinarith
  · have hgap3 : q + 3 ≤ Δ := by omega
    have hgap3r : (q : ℝ) + 3 ≤ Δ := by exact_mod_cast hgap3
    have h1 := mul_pos (show 0 < (Δ : ℝ) - q by linarith)
      (show 0 < (Δ : ℝ) - q - Real.exp 1 by linarith)
    have h2 := mul_pos (show 0 < (q : ℝ) by linarith)
      (show 0 < (Δ : ℝ) - q - Real.exp 1 / 2 by linarith)
    nlinarith

/-- Elementary interval bounds before specializing the formula for `k`. -/
theorem interval_formula_mem_Ioo {q Δ k : ℝ} (hq : 0 < q) (hqΔ : q < Δ)
    (hk : 0 < k) (hkΔ : k < Δ) :
    0 < 1 - q / Δ * (1 - k / Δ) ^ 2 * (Δ - k) / (Δ - k / 2) ∧
      1 - q / Δ * (1 - k / Δ) ^ 2 * (Δ - k) / (Δ - k / 2) < 1 := by
  have hΔ : 0 < Δ := hq.trans hqΔ
  have hp : 0 < q / Δ := div_pos hq hΔ
  have hp1 : q / Δ < 1 := (div_lt_one hΔ).mpr hqΔ
  have ht : 0 < 1 - k / Δ := sub_pos.mpr ((div_lt_one hΔ).mpr hkΔ)
  have ht1 : 1 - k / Δ < 1 := by linarith [div_pos hk hΔ]
  have ht2 : (1 - k / Δ) ^ 2 < 1 := by nlinarith
  have hb : 0 < Δ - k / 2 := by linarith
  have hs : 0 < (Δ - k) / (Δ - k / 2) := div_pos (sub_pos.mpr hkΔ) hb
  have hs1 : (Δ - k) / (Δ - k / 2) < 1 := (div_lt_one hb).mpr (by linarith)
  have hab0 : 0 < q / Δ * (1 - k / Δ) ^ 2 := mul_pos hp (sq_pos_of_pos ht)
  have hab1 : q / Δ * (1 - k / Δ) ^ 2 < 1 :=
    (mul_lt_mul_of_pos_left ht2 hp).trans (by simpa using hp1)
  have hprod0 := mul_pos hab0 hs
  have hprod1 : q / Δ * (1 - k / Δ) ^ 2 * ((Δ - k) / (Δ - k / 2)) < 1 :=
    (mul_lt_mul_of_pos_left hs1 hab0).trans (by simpa using hab1)
  rw [← mul_div_assoc] at hprod0 hprod1
  constructor <;> linarith

/-- The actual unrounded BBR interval is nonempty and has positive left end. -/
theorem intervalStart_mem_Ioo {q Δ : ℕ} (hq : 3 ≤ q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / q)
    (hne : ¬ (q = 3 ∧ Δ = 4)) : intervalStart q Δ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hΔ := degree_gt_colours hqpos hr
  exact interval_formula_mem_Ioo hqpos hΔ (parameter_pos hqpos hΔ)
    (parameter_lt_degree hq ((integer_degree_gap hq hr).resolve_left hne))

/-- The exceptional interval starts at `3/4`, independently of the formula. -/
theorem exceptional_interval : (3 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num

end
end CI2ZF.Appendix.BBR
