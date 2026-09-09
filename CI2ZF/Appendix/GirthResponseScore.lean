import CI2ZF.Appendix.GirthInsertionCovariance
import CI2ZF.Appendix.GirthInfluenceBounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual finite-law response scores and their source operator. The
score is expressed by covariance and identified with conditional means. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]

def colourNorm (f : C → ℝ) : ℝ := ‖(WithLp.toLp 2 f : EuclideanSpace ℝ C)‖

theorem colourNorm_nonneg (f : C → ℝ) : 0 ≤ colourNorm f := norm_nonneg _

theorem colourNorm_sq (f : C → ℝ) : colourNorm f ^ 2 = ∑ c, f c ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

theorem colourNorm_add (f g : C → ℝ) :
    colourNorm (fun c => f c + g c) ≤ colourNorm f + colourNorm g := norm_add_le _ _

theorem covariance_comm (μ : FinDist Ω) (f g : Ω → ℝ) : covariance μ f g = covariance μ g f := by
  unfold covariance
  simp only [mul_comm]

theorem covariance_add_right (μ : FinDist Ω) (f g h : Ω → ℝ) :
    covariance μ f (fun ω => g ω + h ω) = covariance μ f g + covariance μ f h := by
  simp only [covariance_eq_moment, mul_add, expectReal_add]
  ring

theorem covariance_sub_right (μ : FinDist Ω) (f g h : Ω → ℝ) :
    covariance μ f (fun ω => g ω - h ω) = covariance μ f g - covariance μ f h := by
  simp only [covariance_eq_moment, mul_sub, expectReal_sub]
  ring

theorem covariance_const_right (μ : FinDist Ω) (f : Ω → ℝ) (a : ℝ) :
    covariance μ f (fun _ => a) = 0 := by
  rw [covariance_eq_moment, expectReal_mul_const, expectReal_const, sub_self]

def coordinateMarginal (μ : FinDist Ω) (k : Ω → C) : FinDist C := mapLaw μ k

def coordinateMean (μ : FinDist Ω) (k : Ω → C) (f : Ω → ℝ) (c : C) : ℝ :=
  expectReal μ (fun ω => f ω * colourIndicator c (k ω)) / (coordinateMarginal μ k).w c

def responseScore (s : ℝ) (μ : FinDist Ω) (k : Ω → C) (f : Ω → ℝ) (c : C) : ℝ :=
  covariance μ f (fun ω => colourIndicator c (k ω)) /
    (Real.sqrt ((coordinateMarginal μ k).w c) * (1 - s * (coordinateMarginal μ k).w c))

def scoreDiagonal (s : ℝ) (p : FinDist C) (c : C) : ℝ :=
  Real.sqrt (p.w c) / (1 - s * p.w c)

def scoreSource (s : ℝ) (p : FinDist C) (f : C → ℝ) (c : C) : ℝ :=
  scoreDiagonal s p c * (f c - expectReal p f)

theorem coordinateIndicator_mean (μ : FinDist Ω) (k : Ω → C) (c : C) :
    expectReal μ (fun ω => colourIndicator c (k ω)) = (coordinateMarginal μ k).w c := by
  rw [← CI2ZF.expectReal_mapLaw]
  exact expect_colourIndicator _ _

theorem covariance_coordinate (μ : FinDist Ω) (k : Ω → C) (f : Ω → ℝ) (c : C)
    (hc : (coordinateMarginal μ k).w c ≠ 0) :
    covariance μ f (fun ω => colourIndicator c (k ω)) =
      (coordinateMarginal μ k).w c * (coordinateMean μ k f c - expectReal μ f) := by
  rw [covariance_eq_moment, coordinateIndicator_mean]
  unfold coordinateMean
  field_simp

theorem responseScore_eq (s : ℝ) (μ : FinDist Ω) (k : Ω → C) (f : Ω → ℝ) (c : C)
    (hc : 0 < (coordinateMarginal μ k).w c) :
    responseScore s μ k f c = scoreDiagonal s (coordinateMarginal μ k) c *
      (coordinateMean μ k f c - expectReal μ f) := by
  rw [responseScore, covariance_coordinate μ k f c hc.ne', scoreDiagonal]
  have hsq := Real.sq_sqrt hc.le
  have hsr : Real.sqrt ((coordinateMarginal μ k).w c) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  field_simp [hsr]
  rw [hsq]
  ring

/-- The actual conditional variance of a response is bounded by its
Euclidean transformed-score energy. -/
theorem coordinate_response_variance_le (s : ℝ) (μ : FinDist Ω) (k : Ω → C)
    (f : Ω → ℝ) (hp : ∀ c, 0 < (coordinateMarginal μ k).w c)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hden : ∀ c, 1 - s * (coordinateMarginal μ k).w c ≠ 0) :
    (∑ c, (coordinateMarginal μ k).w c * (coordinateMean μ k f c - expectReal μ f) ^ 2) ≤
      ∑ c, responseScore s μ k f c ^ 2 := by
  apply Finset.sum_le_sum
  intro c _
  rw [responseScore_eq s μ k f c (hp c), mul_pow, scoreDiagonal, div_pow,
    Real.sq_sqrt (hp c).le]
  have hp1 := probability_atom_le_one (coordinateMarginal μ k) c
  have hd0 : 0 ≤ 1 - s * (coordinateMarginal μ k).w c := by nlinarith [hp c]
  have hd1 : 1 - s * (coordinateMarginal μ k).w c ≤ 1 := by nlinarith [hp c]
  have hd : (1 - s * (coordinateMarginal μ k).w c) ^ 2 ≤ 1 := by nlinarith
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply (le_div_iff₀ (sq_pos_of_ne_zero (hden c))).mpr
  exact mul_le_of_le_one_right (hp c).le hd

theorem scoreSource_add (s : ℝ) (p : FinDist C) (f g : C → ℝ) :
    scoreSource s p (fun c => f c + g c) = fun c => scoreSource s p f c + scoreSource s p g c := by
  funext c
  simp only [scoreSource, expectReal_add]
  ring

theorem scoreSource_const (s : ℝ) (p : FinDist C) (a : ℝ) :
    scoreSource s p (fun _ => a) = fun _ => 0 := by
  funext c
  simp only [scoreSource, expectReal_const, sub_self, mul_zero]

theorem scoreSource_energy (s : ℝ) (p : FinDist C) (f : C → ℝ) {B : ℝ}
    (_hs : 0 ≤ s) (hs1 : s ≤ 1) (hB : B < 1) (hp : ∀ c, p.w c ≤ B) :
    (∑ c, scoreSource s p f c ^ 2) ≤ (1 / (1 - B)) ^ 2 * variance p f := by
  have hd : 0 < 1 - B := sub_pos.mpr hB
  have hpoint (c : C) : scoreSource s p f c ^ 2 ≤
      (1 / (1 - B)) ^ 2 * (p.w c * (f c - expectReal p f) ^ 2) := by
    have hdc : 1 - B ≤ 1 - s * p.w c := by nlinarith [p.nonneg c, hp c]
    have hdc0 : 0 < 1 - s * p.w c := hd.trans_le hdc
    have hdiv : 1 / (1 - s * p.w c) ≤ 1 / (1 - B) := one_div_le_one_div_of_le hd hdc
    have hdiv0 : 0 ≤ 1 / (1 - s * p.w c) := by positivity
    have hsq := pow_le_pow_left₀ hdiv0 hdiv 2
    have hh := mul_le_mul_of_nonneg_right hsq (mul_nonneg (p.nonneg c) (sq_nonneg (f c - expectReal p f)))
    simpa only [scoreSource, scoreDiagonal, mul_pow, div_pow, Real.sq_sqrt (p.nonneg c), one_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hh
  calc
    _ ≤ ∑ c, (1 / (1 - B)) ^ 2 * (p.w c * (f c - expectReal p f) ^ 2) :=
      Finset.sum_le_sum fun c _ => hpoint c
    _ = _ := (Finset.mul_sum ..).symm

end
end CI2ZF.Appendix.Girth
