import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# The entropy weight inequality in the large-girth contraction

This proves the entropy estimate directly by differentiating twice on
`[0,1/3]`. Thus the numerical fact used by the appendix is discharged rather
than imported as an unproved citation.
-/

namespace ZeroFreeness.Appendix.Girth

open Set

noncomputable section

private theorem nonneg_on_interval_of_derivative (f f' : ℝ → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hd : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x)
    (hd0 : ∀ x ∈ Icc 0 b, 0 ≤ f' x) (h0 : 0 ≤ f 0)
    {x : ℝ} (hx : x ∈ Icc 0 b) : 0 ≤ f x := by
  have hmon := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) b)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hd0 y (interior_subset hy))
  exact h0.trans (hmon ⟨le_rfl, hb⟩ hx hx.1)

def entropyCorrection (y : ℝ) : ℝ := ((1 + y) / y) * Real.log (1 + y) - 1

private def entropyAux (y : ℝ) : ℝ :=
  1 - Real.log (1 + y) - (1 - y / 2) * Real.exp (-y / 2)

private def entropyGap (y : ℝ) : ℝ :=
  2 * y - (1 + y) * Real.log (1 + y) - y * Real.exp (-y / 2)

private theorem entropyAux_derivative {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt entropyAux
      (-(1 / (1 + y)) + (1 - y / 4) * Real.exp (-y / 2)) y := by
  have hlog := ((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).log
    (by linarith : 1 + y ≠ 0)
  have he := (((hasDerivAt_id y).neg).div_const 2).exp
  have hl := (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).div_const 2)
  have hd := ((hasDerivAt_const y (1 : ℝ)).sub hlog).sub (hl.mul he)
  change HasDerivAt entropyAux
    (0 - (0 + 1) / (1 + y) -
      ((0 - 1 / 2) * Real.exp (-y / 2) +
        (1 - y / 2) * (Real.exp (-y / 2) * (-1 / 2)))) y at hd
  exact hd.congr_deriv (by ring)

private theorem entropyGap_derivative {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt entropyGap (entropyAux y) y := by
  have hlog := ((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).log
    (by linarith : 1 + y ≠ 0)
  have he := (((hasDerivAt_id y).neg).div_const 2).exp
  have hlinear := (hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)
  have hd := ((hasDerivAt_id y).const_mul 2).sub (hlinear.mul hlog)
  have hfinal := hd.sub ((hasDerivAt_id y).mul he)
  change HasDerivAt entropyGap
    (2 * 1 - ((0 + 1) * Real.log (1 + y) + (1 + y) * ((0 + 1) / (1 + y))) -
      (1 * Real.exp (-y / 2) + y * (Real.exp (-y / 2) * (-1 / 2)))) y at hfinal
  apply hfinal.congr_deriv
  unfold entropyAux
  field_simp [show 1 + y ≠ 0 by linarith]
  ring

private theorem entropyAux_derivative_nonneg {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 3)) :
    0 ≤ -(1 / (1 + y)) + (1 - y / 4) * Real.exp (-y / 2) := by
  have hy1 : 0 < 1 + y := by linarith [hy.1]
  have he : 1 - y / 2 ≤ Real.exp (-y / 2) := by
    have h := Real.add_one_le_exp (-y / 2)
    linarith
  have hlin : 0 ≤ 1 - y / 4 := by linarith [hy.2]
  have hp := mul_le_mul_of_nonneg_left he hlin
  have hpoly : 0 ≤ y * (2 - 5 * y + y ^ 2) :=
    mul_nonneg hy.1 (by nlinarith [hy.2, sq_nonneg y])
  have hrat : 1 / (1 + y) ≤ (1 - y / 4) * (1 - y / 2) := by
    apply (div_le_iff₀ hy1).mpr
    nlinarith
  have h := hrat.trans hp
  linarith

private theorem entropyAux_nonneg {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 3)) :
    0 ≤ entropyAux y := by
  apply nonneg_on_interval_of_derivative entropyAux
    (fun t => -(1 / (1 + t)) + (1 - t / 4) * Real.exp (-t / 2)) (by norm_num)
    (fun t ht => entropyAux_derivative ht.1) (fun _ ht => entropyAux_derivative_nonneg ht)
    (by simp [entropyAux]) hy

private theorem entropyGap_nonneg {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 3)) :
    0 ≤ entropyGap y := by
  apply nonneg_on_interval_of_derivative entropyGap entropyAux (by norm_num)
    (fun t ht => entropyGap_derivative ht.1) (fun _ ht => entropyAux_nonneg ht)
    (by simp [entropyGap]) hy

theorem entropyCorrection_nonneg {y : ℝ} (hy : 0 < y) :
    0 ≤ entropyCorrection y := by
  have hy1 : 0 < 1 + y := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hy1
  have hmul := mul_le_mul_of_nonneg_left hlog hy1.le
  have hcancel : (1 + y) * (1 - (1 + y)⁻¹) = y := by field_simp [hy1.ne']; ring
  rw [hcancel] at hmul
  have hdiv : 1 ≤ ((1 + y) * Real.log (1 + y)) / y :=
    (le_div_iff₀ hy).mpr (by simpa using hmul)
  unfold entropyCorrection
  have hid : (1 + y) / y * Real.log (1 + y) =
      ((1 + y) * Real.log (1 + y)) / y := by ring
  rw [hid]
  linarith

/-- The numerical entropy inequality used to define the weight `w_v`. -/
theorem entropyCorrection_exp_bound {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 3) :
    Real.exp (-y / 2) ≤ 1 - entropyCorrection y := by
  have hg := entropyGap_nonneg ⟨hy0.le, hy1⟩
  unfold entropyGap at hg
  calc
    Real.exp (-y / 2) ≤ (2 * y - (1 + y) * Real.log (1 + y)) / y := by
      apply (le_div_iff₀ hy0).mpr
      nlinarith
    _ = 1 - entropyCorrection y := by
      unfold entropyCorrection
      field_simp [hy0.ne']
      ring

theorem entropyCorrection_lt_one {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 3) :
    entropyCorrection y < 1 := by
  have h := (Real.exp_pos (-y / 2)).trans_le (entropyCorrection_exp_bound hy0 hy1)
  linarith

theorem entropy_weight_inverse_bound {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 3) :
    1 / (1 - entropyCorrection y) ≤ Real.exp (y / 2) := by
  have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (Real.exp_pos (-y / 2)) (entropyCorrection_exp_bound hy0 hy1)
  have he : 1 / Real.exp (-y / 2) = Real.exp (y / 2) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  exact h.trans_eq he

end

end ZeroFreeness.Appendix.Girth
