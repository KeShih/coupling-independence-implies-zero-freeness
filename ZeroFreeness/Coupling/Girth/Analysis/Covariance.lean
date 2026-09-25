import ZeroFreeness.Coupling.Foundations.FiniteCoupling

/-!
# Finite colour covariance and the exact Potts edge channel

These identities are the probabilistic algebra used in both girth-five
appendices. All expectations use the project's actual finite distributions.
The Gram formula is proved from the categorical law, with no spectral-gap
or mixing hypothesis.
-/

namespace ZeroFreeness.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

noncomputable section

variable {S C : Type*} [Fintype S] [Fintype C]

def covariance (μ : FinDist S) (f g : S → ℝ) : ℝ :=
  expectReal μ (fun t => (f t - expectReal μ f) * (g t - expectReal μ g))

def variance (μ : FinDist S) (f : S → ℝ) : ℝ :=
  expectReal μ (fun t => (f t - expectReal μ f) ^ 2)

theorem covariance_self (μ : FinDist S) (f : S → ℝ) :
    covariance μ f f = variance μ f := by
  simp [covariance, variance, pow_two]

theorem variance_nonneg (μ : FinDist S) (f : S → ℝ) : 0 ≤ variance μ f :=
  Finset.sum_nonneg fun t _ => mul_nonneg (μ.nonneg t) (sq_nonneg _)

theorem expectation_centered (μ : FinDist S) (f : S → ℝ) :
    expectReal μ (fun t => f t - expectReal μ f) = 0 := by
  simp only [expectReal, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, μ.sum_one,
    one_mul, sub_self]

theorem covariance_eq_moment (μ : FinDist S) (f g : S → ℝ) :
    covariance μ f g = expectReal μ (fun t => f t * g t) -
      expectReal μ f * expectReal μ g := by
  calc
    covariance μ f g = ∑ t, (μ.w t * (f t * g t) -
        (μ.w t * f t) * expectReal μ g - (μ.w t * g t) * expectReal μ f +
        μ.w t * (expectReal μ f * expectReal μ g)) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        μ.sum_one, one_mul]
      change expectReal μ (fun t => f t * g t) - expectReal μ f * expectReal μ g -
        expectReal μ g * expectReal μ f + expectReal μ f * expectReal μ g = _
      ring

/-- Variance is the least squared error among constants. -/
theorem variance_le_error (μ : FinDist S) (f : S → ℝ) (a : ℝ) :
    variance μ f ≤ expectReal μ (fun t => (f t - a) ^ 2) := by
  have hid : expectReal μ (fun t => (f t - a) ^ 2) =
      variance μ f + (expectReal μ f - a) ^ 2 := by
    rw [← covariance_self, covariance_eq_moment]
    have hexp : expectReal μ (fun t => (f t - a) ^ 2) =
        expectReal μ (fun t => f t * f t) - 2 * a * expectReal μ f + a ^ 2 := by
      calc
        _ = ∑ t, (μ.w t * (f t * f t) - (μ.w t * f t) * (2 * a) +
            μ.w t * a ^ 2) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
            μ.sum_one, one_mul]
          change expectReal μ (fun t => f t * f t) - expectReal μ f * (2 * a) + a ^ 2 = _
          ring
    rw [hexp]
    ring
  rw [hid]
  nlinarith [sq_nonneg (expectReal μ f - a)]

/-- Atom bounds convert ordinary Euclidean squared error into variance. -/
theorem variance_le_atom_bound (μ : FinDist S) (f : S → ℝ) {B : ℝ}
    (hB : ∀ t, μ.w t ≤ B) (a : ℝ) :
    variance μ f ≤ B * ∑ t, (f t - a) ^ 2 := by
  calc
    _ ≤ expectReal μ (fun t => (f t - a) ^ 2) := variance_le_error μ f a
    _ ≤ ∑ t, B * (f t - a) ^ 2 := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_right (hB t) (sq_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm

/-- Weighted Cauchy--Schwarz, with no strict positivity assumptions on atoms. -/
theorem covariance_sq_le (μ : FinDist S) (f g : S → ℝ) :
    covariance μ f g ^ 2 ≤ variance μ f * variance μ g := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro t _
    exact mul_nonneg (μ.nonneg t) (sq_nonneg _)
  · intro t _
    exact mul_nonneg (μ.nonneg t) (sq_nonneg _)
  · intro t _
    exact le_of_eq (by ring)

variable [DecidableEq C]

def colourIndicator (c t : C) : ℝ := if t = c then 1 else 0

@[simp] theorem expect_colourIndicator (r : FinDist C) (c : C) :
    expectReal r (colourIndicator c) = r.w c := by
  simp [expectReal, colourIndicator]

theorem expect_colourIndicator_mul (r : FinDist C) (c d : C) :
    expectReal r (fun t => colourIndicator c t * colourIndicator d t) =
      if c = d then r.w c else 0 := by
  by_cases h : c = d
  · subst d
    simp [expectReal, colourIndicator]
  · simp [expectReal, colourIndicator, h, Ne.symm h]

theorem categorical_covariance (r : FinDist C) (c d : C) :
    covariance r (colourIndicator c) (colourIndicator d) =
      (if c = d then r.w c else 0) - r.w c * r.w d := by
  rw [covariance_eq_moment, expect_colourIndicator_mul, expect_colourIndicator,
    expect_colourIndicator]

/-- The normalized likelihood of the leaf colour conditional on centre `c`. -/
def edgeLikelihood (s : ℝ) (r : FinDist C) (c t : C) : ℝ :=
  (1 - s * colourIndicator c t) / (1 - s * r.w c)

def edgeFluctuation (s : ℝ) (r : FinDist C) (c t : C) : ℝ :=
  edgeLikelihood s r c t - 1

theorem edgeLikelihood_mean {s : ℝ} (r : FinDist C) (c : C)
    (hden : 1 - s * r.w c ≠ 0) :
    expectReal r (edgeLikelihood s r c) = 1 := by
  simp only [expectReal, edgeLikelihood, ← mul_div_assoc, ← Finset.sum_div,
    mul_sub, Finset.sum_sub_distrib, mul_one]
  have hsum : ∑ t, r.w t * (s * colourIndicator c t) = s * r.w c := by
    simp [colourIndicator, mul_comm]
  rw [r.sum_one, hsum, div_self hden]

theorem edgeFluctuation_eq {s : ℝ} (r : FinDist C) (c t : C)
    (hden : 1 - s * r.w c ≠ 0) :
    edgeFluctuation s r c t =
      (-s / (1 - s * r.w c)) * (colourIndicator c t - r.w c) := by
  unfold edgeFluctuation edgeLikelihood
  field_simp
  ring

theorem edgeFluctuation_mean {s : ℝ} (r : FinDist C) (c : C)
    (hden : 1 - s * r.w c ≠ 0) :
    expectReal r (edgeFluctuation s r c) = 0 := by
  simp only [edgeFluctuation, expectReal, mul_sub, Finset.sum_sub_distrib, mul_one]
  change expectReal r (edgeLikelihood s r c) - ∑ t, r.w t = 0
  rw [edgeLikelihood_mean r c hden, r.sum_one, sub_self]

/-- The exact one-leaf Gram matrix in `fixed-girth-ci.tex`. -/
theorem edge_gram_formula {s : ℝ} (r : FinDist C) (c d : C)
    (hc : 1 - s * r.w c ≠ 0) (hd : 1 - s * r.w d ≠ 0) :
    expectReal r (fun t => edgeFluctuation s r c t * edgeFluctuation s r d t) =
      s ^ 2 * ((if c = d then r.w c else 0) - r.w c * r.w d) /
        ((1 - s * r.w c) * (1 - s * r.w d)) := by
  simp_rw [edgeFluctuation_eq r c _ hc, edgeFluctuation_eq r d _ hd]
  have hfactor : expectReal r (fun t =>
      (-s / (1 - s * r.w c)) * (colourIndicator c t - r.w c) *
      ((-s / (1 - s * r.w d)) * (colourIndicator d t - r.w d))) =
      ((-s / (1 - s * r.w c)) * (-s / (1 - s * r.w d))) *
      covariance r (colourIndicator c) (colourIndicator d) := by
    unfold covariance
    rw [expect_colourIndicator, expect_colourIndicator]
    simp only [expectReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hfactor, categorical_covariance]
  field_simp

/-- Nonnegativity of every Gram quadratic form follows from its representation
as the second moment of the colour-direction fluctuation. -/
theorem edge_gram_positive (s : ℝ) (r : FinDist C) (z : C → ℝ) :
    0 ≤ ∑ c, ∑ d, z c * z d *
      expectReal r (fun t => edgeFluctuation s r c t * edgeFluctuation s r d t) := by
  have hid : (∑ c, ∑ d, z c * z d *
      expectReal r (fun t => edgeFluctuation s r c t * edgeFluctuation s r d t)) =
      expectReal r (fun t => (∑ c, z c * edgeFluctuation s r c t) ^ 2) := by
    simp only [expectReal, pow_two, Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ c, ∑ t, ∑ d,
          z c * z d * (r.w t * (edgeFluctuation s r c t * edgeFluctuation s r d t)) := by
        apply Finset.sum_congr rfl
        intro c _
        exact Finset.sum_comm
      _ = ∑ t, ∑ c, ∑ d,
          z c * z d * (r.w t * (edgeFluctuation s r c t * edgeFluctuation s r d t)) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        ring
  rw [hid]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (r.nonneg t) (sq_nonneg _)

end

end ZeroFreeness.Appendix.Girth
