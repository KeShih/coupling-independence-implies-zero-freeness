import CI2ZF.Appendix.GirthResponseScore
import CI2ZF.Appendix.GirthInsertionLocalSource

/-! Quantitative bounds for the actual colour source operator. The far
source is a covariance with the full conditional source on the shell. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]

theorem variance_bounded_source (p : FinDist C) (f : C → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hf : ∀ c, |f c| ≤ A) : variance p f ≤ A ^ 2 := by
  calc
    _ ≤ expectReal p (fun c => (f c - 0) ^ 2) := variance_le_error p f 0
    _ ≤ expectReal p (fun _ => A ^ 2) := expectReal_mono p (fun c => by
      simpa only [sub_zero, sq_abs] using (sq_le_sq₀ (abs_nonneg (f c)) hA).mpr (hf c))
    _ = _ := expectReal_const _ _

theorem scoreSource_norm (s : ℝ) (p : FinDist C) (f : C → ℝ) {B : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB : B < 1) (hp : ∀ c, p.w c ≤ B) :
    colourNorm (scoreSource s p f) ≤ (1 / (1 - B)) * Real.sqrt (variance p f) := by
  apply (sq_le_sq₀ (colourNorm_nonneg _) (by positivity)).mp
  rw [colourNorm_sq, mul_pow, Real.sq_sqrt (variance_nonneg p f)]
  exact scoreSource_energy s p f hs hs1 hB hp

theorem scoreSource_bounded_norm (s : ℝ) (p : FinDist C) (f : C → ℝ) {B A : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB : B < 1) (hp : ∀ c, p.w c ≤ B)
    (hA : 0 ≤ A) (hf : ∀ c, |f c| ≤ A) :
    colourNorm (scoreSource s p f) ≤ (1 / (1 - B)) * A := by
  have hv := variance_bounded_source p f hA hf
  have hsqrt : Real.sqrt (variance p f) ≤ A :=
    (Real.sqrt_le_left hA).mpr hv
  exact (scoreSource_norm s p f hs hs1 hB hp).trans
    (mul_le_mul_of_nonneg_left hsqrt (by positivity))

theorem scoreDiagonal_bound (s : ℝ) (p : FinDist C) {B : ℝ}
    (hs1 : s ≤ 1) (_hB0 : 0 ≤ B) (hB : B < 1) (hp : ∀ c, p.w c ≤ B) (c : C) :
    0 ≤ scoreDiagonal s p c ∧ scoreDiagonal s p c ≤ (1 / (1 - B)) * Real.sqrt B := by
  have hd : 0 < 1 - B := sub_pos.mpr hB
  have hdc : 1 - B ≤ 1 - s * p.w c := by nlinarith [p.nonneg c, hp c]
  unfold scoreDiagonal
  constructor
  · exact div_nonneg (Real.sqrt_nonneg _) (hd.trans_le hdc).le
  · calc
      _ ≤ Real.sqrt B / (1 - B) := div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (hp c)) hd hdc
      _ = _ := by ring

theorem scoreSource_bounded_infty (s : ℝ) (p : FinDist C) (f : C → ℝ) {B A : ℝ}
    (hs1 : s ≤ 1) (hB0 : 0 ≤ B) (hB : B < 1) (hp : ∀ c, p.w c ≤ B)
    (_hA : 0 ≤ A) (hf : ∀ c, |f c| ≤ A) (c : C) :
    |scoreSource s p f c| ≤ 2 * (1 / (1 - B)) * Real.sqrt B * A := by
  have hdiag := scoreDiagonal_bound s p hs1 hB0 hB hp c
  have he := expectReal_abs_bound p f hf
  have hdiff : |f c - expectReal p f| ≤ 2 * A := (abs_sub _ _).trans (by linarith [hf c])
  rw [scoreSource, abs_mul, abs_of_nonneg hdiag.1]
  calc
    _ ≤ ((1 / (1 - B)) * Real.sqrt B) * (2 * A) :=
      mul_le_mul hdiag.2 hdiff (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem covariance_source_energy (μ : FinDist Ω) (G : C → Ω → ℝ) (f : Ω → ℝ)
    {g D : ℝ} (hG : ColourCovarianceBound μ G (g ^ 2))
    (hf : variance μ f ≤ D ^ 2) :
    (∑ c, covariance μ f (G c) ^ 2) ≤ (g * D) ^ 2 := by
  calc
    _ ≤ variance μ f * g ^ 2 := covariance_vector_energy μ G (sq_nonneg _) hG f
    _ ≤ D ^ 2 * g ^ 2 := mul_le_mul_of_nonneg_right hf (sq_nonneg _)
    _ = _ := by ring

theorem covariance_source_infty (μ : FinDist Ω) (G : C → Ω → ℝ) (f : Ω → ℝ)
    {g D : ℝ} (hg : 0 ≤ g) (hD : 0 ≤ D) (hG : ColourCovarianceBound μ G (g ^ 2))
    (hf : variance μ f ≤ D ^ 2) (c : C) : |covariance μ f (G c)| ≤ g * D := by
  have hsingle : covariance μ f (G c) ^ 2 ≤ ∑ b, covariance μ f (G b) ^ 2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (covariance μ f (G b))) (Finset.mem_univ c)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hg hD)).mp
  rw [sq_abs]
  exact hsingle.trans (covariance_source_energy μ G f hG hf)

theorem scoreSource_covariance_norm (s : ℝ) (p : FinDist C)
    (μ : FinDist Ω) (G : C → Ω → ℝ) (f : Ω → ℝ) {B g D : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB0 : 0 ≤ B) (hB : B < 1) (hp : ∀ c, p.w c ≤ B)
    (hg : 0 ≤ g) (hD : 0 ≤ D) (hG : ColourCovarianceBound μ G (g ^ 2))
    (hf : variance μ f ≤ D ^ 2) :
    colourNorm (scoreSource s p (fun c => covariance μ f (G c))) ≤
      (1 / (1 - B)) * Real.sqrt B * g * D := by
  have he : expectReal p (fun c => covariance μ f (G c) ^ 2) ≤ B * D ^ 2 * g ^ 2 := by
    have h := weighted_covariance_vector_energy μ G (sq_nonneg g) hB0 hG p hp f
    simp only [mul_pow, Real.sq_sqrt (p.nonneg _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hB0) (sq_nonneg _))
  have hv : variance p (fun c => covariance μ f (G c)) ≤ B * D ^ 2 * g ^ 2 := by
    have h := variance_le_error p (fun c => covariance μ f (G c)) 0
    simp only [sub_zero] at h
    exact h.trans he
  have henergy := (scoreSource_energy s p (fun c => covariance μ f (G c)) hs hs1 hB hp).trans
    (mul_le_mul_of_nonneg_left hv (sq_nonneg _))
  apply (sq_le_sq₀ (colourNorm_nonneg _) (by positivity)).mp
  rw [colourNorm_sq]
  calc
    _ ≤ (1 / (1 - B)) ^ 2 * (B * D ^ 2 * g ^ 2) := henergy
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hB0]; ring

/-- The two source bounds used by the simultaneous response induction. -/
theorem scoreSource_full_both (s : ℝ) (p : FinDist C) (localSource : C → ℝ)
    (μ : FinDist Ω) (G : C → Ω → ℝ) (f : Ω → ℝ) {B A g D : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB0 : 0 ≤ B) (hB : B < 1) (hp : ∀ c, p.w c ≤ B)
    (hA : 0 ≤ A) (hlocal : ∀ c, |localSource c| ≤ A) (hg : 0 ≤ g) (hD : 0 ≤ D)
    (hG : ColourCovarianceBound μ G (g ^ 2)) (hf : variance μ f ≤ D ^ 2) :
    colourNorm (scoreSource s p (fun c => localSource c + covariance μ f (G c))) ≤
      (1 / (1 - B)) * (A + Real.sqrt B * g * D) ∧
    ∀ c, |scoreSource s p (fun c => localSource c + covariance μ f (G c)) c| ≤
      2 * (1 / (1 - B)) * Real.sqrt B * (A + g * D) := by
  constructor
  · rw [scoreSource_add]
    calc
      _ ≤ colourNorm (scoreSource s p localSource) +
          colourNorm (scoreSource s p (fun c => covariance μ f (G c))) := colourNorm_add _ _
      _ ≤ (1 / (1 - B)) * A + (1 / (1 - B)) * Real.sqrt B * g * D :=
        add_le_add (scoreSource_bounded_norm s p localSource hs hs1 hB hp hA hlocal)
          (scoreSource_covariance_norm s p μ G f hs hs1 hB0 hB hp hg hD hG hf)
      _ = _ := by ring
  · apply scoreSource_bounded_infty s p _ hs1 hB0 hB hp (add_nonneg hA (mul_nonneg hg hD))
    intro c
    exact (abs_add_le _ _).trans (add_le_add (hlocal c) (covariance_source_infty μ G f hg hD hG hf c))

end
end CI2ZF.Appendix.Girth
