import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite complex averages

This file develops the finite weighted-average estimates used in the
complex-average argument in `main.tex`, lines 720–800. Probabilities are
represented by real, nonnegative weights whose finite sum is one.
-/

namespace CI2ZF

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A finite complex average with real weights. -/
def complexAverage (p : ι → ℝ) (f : ι → ℂ) : ℂ :=
  ∑ i, (p i : ℂ) * f i

/-- Finite nonnegative averaging does not increase a uniform norm bound. -/
theorem norm_complexAverage_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (f : ι → ℂ) (B : ℝ)
    (hf : ∀ i, ‖f i‖ ≤ B) : ‖complexAverage p f‖ ≤ B := by
  calc
    ‖complexAverage p f‖ ≤ ∑ i, ‖(p i : ℂ) * f i‖ := by
      exact norm_sum_le _ _
    _ = ∑ i, p i * ‖f i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i)]
    _ ≤ ∑ i, p i * B := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (hp i)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Centering commutes with averaging when the weights have total mass one. -/
theorem complexAverage_sub_const (p : ι → ℝ) (hsum : ∑ i, p i = 1)
    (f : ι → ℂ) (a : ℂ) :
    complexAverage p (fun i => f i - a) = complexAverage p f - a := by
  have hsumC : ∑ i, (p i : ℂ) = 1 := by exact_mod_cast hsum
  simp only [complexAverage, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hsumC, one_mul]

/-- Every convex combination of points in a closed disk remains in the disk. -/
theorem norm_complexAverage_sub_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (f : ι → ℂ) (a : ℂ) (B : ℝ)
    (hf : ∀ i, ‖f i - a‖ ≤ B) : ‖complexAverage p f - a‖ ≤ B := by
  rw [← complexAverage_sub_const p hsum f a]
  exact norm_complexAverage_le p hp hsum _ B hf

/-- A disk centered at `a` of radius strictly below `‖a‖` excludes zero. -/
theorem complexAverage_ne_zero_of_norm_sub_le (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (f : ι → ℂ) (a : ℂ) (B : ℝ) (hB : B < ‖a‖)
    (hf : ∀ i, ‖f i - a‖ ≤ B) : complexAverage p f ≠ 0 := by
  intro hz
  have hb := norm_complexAverage_sub_le p hp hsum f a B hf
  rw [hz, zero_sub, norm_neg] at hb
  exact (not_le_of_gt hB) hb

/-- A convenient rational exponential bound for the analytic estimates. -/
theorem exp_quarter_le_four_thirds : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
  have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
  rw [Real.exp_neg] at h
  have hp := Real.exp_pos (1 / 4 : ℝ)
  have hm := mul_le_mul_of_nonneg_right h hp.le
  rw [inv_mul_cancel₀ (ne_of_gt hp)] at hm
  nlinarith

/-- The exponential is `4/3`-Lipschitz on the quarter disk. -/
theorem norm_exp_sub_exp_le_four_thirds (u v : ℂ)
    (hu : ‖u‖ ≤ 1 / 4) (hv : ‖v‖ ≤ 1 / 4) :
    ‖Complex.exp u - Complex.exp v‖ ≤ (4 / 3 : ℝ) * ‖u - v‖ := by
  have bound : ∀ z ∈ Metric.closedBall (0 : ℂ) (1 / 4 : ℝ),
      ‖Complex.exp z‖ ≤ (4 / 3 : ℝ) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans hz')).trans
      exp_quarter_le_four_thirds
  exact (convex_closedBall (0 : ℂ) (1 / 4 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (Complex.hasDerivAt_exp z).hasDerivWithinAt) bound
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)

/-- Exponents in the quarter disk give values in the third disk about one. -/
theorem norm_exp_sub_one_le_third (u : ℂ) (hu : ‖u‖ ≤ 1 / 4) :
    ‖Complex.exp u - 1‖ ≤ (1 / 3 : ℝ) := by
  have h := norm_exp_sub_exp_le_four_thirds u 0 hu (by norm_num)
  simp only [Complex.exp_zero, sub_zero] at h
  linarith

/-- The averaged exponential remains in the third disk about one. -/
theorem norm_complexAverage_exp_sub_one_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (u : ι → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1 / 4) :
    ‖complexAverage p (fun i => Complex.exp (u i)) - 1‖ ≤ (1 / 3 : ℝ) := by
  exact norm_complexAverage_sub_le p hp hsum _ 1 _
    (fun i => norm_exp_sub_one_le_third (u i) (hu i))

/-- In particular the averaged exponential cannot vanish. -/
theorem complexAverage_exp_ne_zero (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (u : ι → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1 / 4) :
    complexAverage p (fun i => Complex.exp (u i)) ≠ 0 := by
  exact complexAverage_ne_zero_of_norm_sub_le p hp hsum _ 1 (1 / 3) (by norm_num)
    (fun i => norm_exp_sub_one_le_third (u i) (hu i))

/-- The third disk about one lies in the domain of the principal logarithm. -/
theorem mem_slitPlane_of_norm_sub_one_le_third (z : ℂ)
    (hz : ‖z - 1‖ ≤ (1 / 3 : ℝ)) : z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have h := Complex.re_le_norm (1 - z)
  rw [norm_sub_rev] at h
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

/-- The logarithm is `3/2`-Lipschitz on the third disk about one. -/
theorem norm_log_sub_log_le_three_halves (u v : ℂ)
    (hu : ‖u - 1‖ ≤ (1 / 3 : ℝ)) (hv : ‖v - 1‖ ≤ (1 / 3 : ℝ)) :
    ‖Complex.log u - Complex.log v‖ ≤ (3 / 2 : ℝ) * ‖u - v‖ := by
  have hnorm : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 3 : ℝ),
      ‖z - 1‖ ≤ (1 / 3 : ℝ) := by
    intro z hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have bound : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 3 : ℝ),
      ‖z⁻¹‖ ≤ (3 / 2 : ℝ) := by
    intro z hz
    have hn := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one, norm_sub_rev] at hn
    have hz' := hnorm z hz
    have hlow : (2 / 3 : ℝ) ≤ ‖z‖ := by linarith
    rw [norm_inv]
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 2 / 3) hlow
    norm_num at hi ⊢
    exact hi
  exact (convex_closedBall (1 : ℂ) (1 / 3 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (Complex.hasDerivAt_log
      (mem_slitPlane_of_norm_sub_one_le_third z (hnorm z hz))).hasDerivWithinAt) bound
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)

/-- Comparing finite averages on one common coupling space. -/
theorem norm_complexAverage_sub_le_sum (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (f g : ι → ℂ) :
    ‖complexAverage p f - complexAverage p g‖ ≤ ∑ i, p i * ‖f i - g i‖ := by
  calc
    ‖complexAverage p f - complexAverage p g‖ =
        ‖∑ i, (p i : ℂ) * (f i - g i)‖ := by
      simp [complexAverage, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖(p i : ℂ) * (f i - g i)‖ := norm_sum_le _ _
    _ = ∑ i, p i * ‖f i - g i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i)]

/-- The complex-average comparison with its sharp-for-this-argument factor `2`.

The two exponent functions live on one common finite probability space. This
is exactly the form needed after choosing a coupling of the original laws.
The logarithms here are evaluated in the third disk about one, which avoids
the branch cut. Their difference is an explicit logarithm of the quotient.
-/
theorem norm_log_complexAverage_exp_sub_le (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (u v : ι → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1 / 4) (hv : ∀ i, ‖v i‖ ≤ 1 / 4) :
    ‖Complex.log (complexAverage p (fun i => Complex.exp (u i))) -
      Complex.log (complexAverage p (fun i => Complex.exp (v i)))‖ ≤
      2 * ∑ i, p i * ‖u i - v i‖ := by
  have hav := norm_complexAverage_sub_le_sum p hp
    (fun i => Complex.exp (u i)) (fun i => Complex.exp (v i))
  have hsumExp : (∑ i, p i * ‖Complex.exp (u i) - Complex.exp (v i)‖) ≤
      (4 / 3 : ℝ) * ∑ i, p i * ‖u i - v i‖ := by
    calc
      _ ≤ ∑ i, p i * ((4 / 3 : ℝ) * ‖u i - v i‖) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (norm_exp_sub_exp_le_four_thirds (u i) (v i) (hu i) (hv i)) (hp i)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hlog := norm_log_sub_log_le_three_halves
    (complexAverage p (fun i => Complex.exp (u i)))
    (complexAverage p (fun i => Complex.exp (v i)))
    (norm_complexAverage_exp_sub_one_le p hp hsum u hu)
    (norm_complexAverage_exp_sub_one_le p hp hsum v hv)
  linarith

/-- The explicit logarithmic difference exponentiates to the quotient. -/
theorem exp_log_complexAverage_exp_sub (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (u v : ι → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1 / 4) (hv : ∀ i, ‖v i‖ ≤ 1 / 4) :
    Complex.exp (Complex.log (complexAverage p (fun i => Complex.exp (u i))) -
      Complex.log (complexAverage p (fun i => Complex.exp (v i)))) =
      complexAverage p (fun i => Complex.exp (u i)) /
        complexAverage p (fun i => Complex.exp (v i)) := by
  rw [Complex.exp_sub, Complex.exp_log (complexAverage_exp_ne_zero p hp hsum u hu),
    Complex.exp_log (complexAverage_exp_ne_zero p hp hsum v hv)]

/-- Adding a common exponent factors out of the finite average. -/
theorem complexAverage_exp_add_const (p : ι → ℝ) (u : ι → ℂ) (a : ℂ) :
    complexAverage p (fun i => Complex.exp (u i + a)) =
      Complex.exp a * complexAverage p (fun i => Complex.exp (u i)) := by
  simp only [complexAverage, Complex.exp_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Centering both exponent functions by the same constant preserves their quotient. -/
theorem complexAverage_exp_centered_quotient (p : ι → ℝ) (u v : ι → ℂ) (a : ℂ) :
    complexAverage p (fun i => Complex.exp (u i)) /
      complexAverage p (fun i => Complex.exp (v i)) =
    complexAverage p (fun i => Complex.exp (u i - a)) /
      complexAverage p (fun i => Complex.exp (v i - a)) := by
  have hu := complexAverage_exp_add_const p (fun i => u i - a) a
  have hv := complexAverage_exp_add_const p (fun i => v i - a) a
  simp only [sub_add_cancel] at hu hv
  rw [hu, hv, mul_div_mul_left _ _ (Complex.exp_ne_zero a)]

/-- The `2 A · cost + 4 δ` comparison on a common finite coupling space.

Here `h₀` and `h₁` are the two evaluations of the centered common response,
and `d` is their pointwise coupling distance. Marginal identities can then
rewrite these two averages as the original expectations under two laws.
-/
theorem complex_average_comparison (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (h₀ h₁ η₀ η₁ : ι → ℂ) (d : ι → ℝ) (A δ : ℝ)
    (hδ : δ ≤ 1 / 8)
    (hh₀ : ∀ i, ‖h₀ i‖ ≤ 1 / 8) (hh₁ : ∀ i, ‖h₁ i‖ ≤ 1 / 8)
    (hη₀ : ∀ i, ‖η₀ i‖ ≤ δ) (hη₁ : ∀ i, ‖η₁ i‖ ≤ δ)
    (hlip : ∀ i, ‖h₀ i - h₁ i‖ ≤ A * d i) :
    ‖Complex.log (complexAverage p (fun i => Complex.exp (h₀ i + η₀ i))) -
      Complex.log (complexAverage p (fun i => Complex.exp (h₁ i + η₁ i)))‖ ≤
      2 * A * (∑ i, p i * d i) + 4 * δ := by
  have hu : ∀ i, ‖h₀ i + η₀ i‖ ≤ 1 / 4 := by
    intro i
    have h := norm_add_le (h₀ i) (η₀ i)
    have hh := hh₀ i
    have he := hη₀ i
    linarith
  have hv : ∀ i, ‖h₁ i + η₁ i‖ ≤ 1 / 4 := by
    intro i
    have h := norm_add_le (h₁ i) (η₁ i)
    have hh := hh₁ i
    have he := hη₁ i
    linarith
  have hdiff : ∀ i, ‖h₀ i + η₀ i - (h₁ i + η₁ i)‖ ≤ A * d i + 2 * δ := by
    intro i
    have heq : h₀ i + η₀ i - (h₁ i + η₁ i) =
        (h₀ i - h₁ i) + (η₀ i - η₁ i) := by ring
    rw [heq]
    have h := norm_add_le (h₀ i - h₁ i) (η₀ i - η₁ i)
    have he := norm_sub_le (η₀ i) (η₁ i)
    have hl := hlip i
    have h0 := hη₀ i
    have h1 := hη₁ i
    linarith
  have hsumDiff : (∑ i, p i * ‖h₀ i + η₀ i - (h₁ i + η₁ i)‖) ≤
      A * (∑ i, p i * d i) + 2 * δ := by
    calc
      _ ≤ ∑ i, p i * (A * d i + 2 * δ) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hdiff i) (hp i)
      _ = A * (∑ i, p i * d i) + 2 * δ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hsum, one_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have h := norm_log_complexAverage_exp_sub_le p hp hsum
    (fun i => h₀ i + η₀ i) (fun i => h₁ i + η₁ i) hu hv
  linarith

/-- Parameter-dependent averaged exponentials have a differentiable logarithm
on every domain where the centered exponents stay in the quarter disk.

This supplies the branch needed to compare with a logarithm continued from
a base point; it is stronger than a merely pointwise choice of a logarithm.
-/
theorem differentiableOn_log_complexAverage_exp (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (u : ι → ℂ → ℂ) (s : Set ℂ)
    (hu : ∀ i, DifferentiableOn ℂ (u i) s)
    (hbound : ∀ z ∈ s, ∀ i, ‖u i z‖ ≤ 1 / 4) :
    DifferentiableOn ℂ
      (fun z => Complex.log (complexAverage p (fun i => Complex.exp (u i z)))) s := by
  apply DifferentiableOn.clog
  · unfold complexAverage
    exact DifferentiableOn.fun_sum fun i _ => (hu i).cexp.const_mul (p i : ℂ)
  · intro z hz
    exact mem_slitPlane_of_norm_sub_one_le_third _
      (norm_complexAverage_exp_sub_one_le p hp hsum _ (hbound z hz))

/-- The chosen logarithm is normalized at any base point with zero exponents. -/
theorem log_complexAverage_exp_zero (p : ι → ℝ) (hsum : ∑ i, p i = 1) :
    Complex.log (complexAverage p (fun _ => Complex.exp (0 : ℂ))) = 0 := by
  have hsumC : ∑ i, (p i : ℂ) = 1 := by exact_mod_cast hsum
  simp [complexAverage, hsumC]

end

end CI2ZF
