import CI2ZF.Appendix.GirthCovariance
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Scalar insertion estimates under an arbitrary finite exterior law. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset Set
noncomputable section
attribute [local instance] Classical.propDecidable

def logRemainder (y : ℝ) : ℝ := -Real.log (1 - y) - y

theorem logRemainder_nonneg {y : ℝ} (hy : y < 1) : 0 ≤ logRemainder y := by
  have hh := Real.log_le_sub_one_of_pos (sub_pos.mpr hy)
  dsimp [logRemainder]
  linarith

theorem logRemainder_le {B y : ℝ} (hB : B < 1) (hy0 : 0 ≤ y) (hyB : y ≤ B) :
    logRemainder y ≤ y ^ 2 / (2 * (1 - B)) := by
  let f : ℝ → ℝ := fun x => Real.log (1 - x) + x + x ^ 2 / (2 * (1 - B))
  have hd (x : ℝ) (hx : x ≤ B) : HasDerivAt f
      (-1 / (1 - x) + 1 + 2 * x / (2 * (1 - B))) x := by
    have hi : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
    have hp : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x ^ (2 - 1)) x := hasDerivAt_pow 2 x
    have hh := (((hi.const_sub 1).log
      (by linarith : 1 - x ≠ 0)).add hi).add (hp.div_const (2 * (1 - B)))
    convert hh using 1 <;> first | rfl | norm_num
  have hc : ContinuousOn f (Icc 0 B) := fun x hx => (hd x hx.2).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc 0 B) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 B) hc
      (fun x hx => (hd x (interior_subset hx).2).hasDerivWithinAt) ?_
    intro x hx
    have hx0 := (interior_subset hx).1
    have hxB := (interior_subset hx).2
    have he : -1 / (1 - x) + 1 + 2 * x / (2 * (1 - B)) =
        x * (B - x) / ((1 - B) * (1 - x)) := by
      field_simp [ne_of_gt (by linarith : 0 < 1 - B), ne_of_gt (by linarith : 0 < 1 - x)]
      ring
    rw [he]
    exact div_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hxB))
      (mul_nonneg (by linarith) (by linarith))
  have hh := hm ⟨le_rfl, hy0.trans hyB⟩ ⟨hy0, hyB⟩ hy0
  simp only [f, sub_zero, Real.log_one, zero_add, zero_pow (by decide : 2 ≠ 0), zero_div] at hh
  dsimp [logRemainder]
  linarith

theorem exp_quadratic_upper {A x : ℝ} (hA : 0 ≤ A) (hx : |x| ≤ A) :
    Real.exp x ≤ 1 + x + Real.exp A * x ^ 2 / 2 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (Ne.symm hx0) (f := Real.exp) Real.contDiff_exp.contDiffOn
  have hu : UniqueDiffWithinAt ℝ (uIcc 0 x) 0 :=
    (uniqueDiffOn_uIcc (Ne.symm hx0)) 0 (left_mem_uIcc)
  have hid : taylorWithinEval Real.exp 1 (uIcc 0 x) 0 x = 1 + x := by
    rw [show 1 = 0 + 1 from rfl, taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Real.exp_zero, Nat.cast_zero, zero_add,
      Nat.factorial_zero, Nat.cast_one, one_mul, inv_one, sub_zero, pow_one,
      iteratedDerivWithin_one, (Real.hasDerivAt_exp 0).hasDerivWithinAt.derivWithin hu,
      smul_eq_mul, mul_one]
  rw [hid, iteratedDeriv_eq_iterate, Real.iter_deriv_exp] at he
  norm_num at he
  have hzA : z ≤ A := hz.2.le.trans (max_le hA (abs_le.mp hx).2)
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hzA) (sq_nonneg x)
  nlinarith

theorem exp_nonpos_lipschitz {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have hh := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs, Real.abs_exp] using Real.exp_le_one_iff.mpr hz)
    hy hx
  simpa only [Real.norm_eq_abs, one_mul] using hh

end
end CI2ZF.Appendix.Girth
