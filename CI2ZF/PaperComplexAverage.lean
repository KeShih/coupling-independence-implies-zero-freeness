import CI2ZF.FiniteCoupling

/-!
# The complex-average lemma with oscillation and Wasserstein hypotheses

This module proves the finite-law form of `lem:cavg` in `main.tex`.
Only the oscillation of the common response is assumed small. A common
center is subtracted before using the principal logarithm; the resulting
logarithmic difference exponentiates to the original quotient.

The transportation cost `d` may be any finite real cost. In the paper it
is the metric distance, and in the Potts application it is Hamming distance.
-/

namespace CI2ZF

open scoped BigOperators
open PottsCI PottsCI.FinDist

noncomputable section

variable {S : Type*} [Fintype S]

/-- A finite probability law supplies a point at which to center a response. -/
theorem nonempty_of_finDist (μ : FinDist S) : Nonempty S := by
  classical
  by_cases hs : Nonempty S
  · exact hs
  · let : IsEmpty S := ⟨fun x => hs ⟨x⟩⟩
    have h := μ.sum_one
    simp at h

/-- Explicit logarithm of the ratio, using one common response center.

Under the bounds in `paper_complex_average_with_anchor`, each argument of
`Complex.log` lies in the third disk about one, so no branch cut is crossed.
-/
def centeredAverageLogRatio (μ ν : FinDist S) (h η η' : S → ℂ) (anchor : S) : ℂ :=
  Complex.log (expectComplex μ (fun x => Complex.exp (h x - h anchor + η x))) -
    Complex.log (expectComplex ν (fun x => Complex.exp (h x - h anchor + η' x)))

/-- Centering an exponent multiplies its original expectation by one common
nonzero exponential factor. -/
theorem expectComplex_exp_center (μ : FinDist S) (h η : S → ℂ) (a : ℂ) :
    expectComplex μ (fun x => Complex.exp (h x + η x)) =
      Complex.exp a * expectComplex μ (fun x => Complex.exp (h x - a + η x)) := by
  have hc := complexAverage_exp_add_const μ.w (fun x => h x - a + η x) a
  change complexAverage μ.w (fun x => Complex.exp (h x + η x)) =
    Complex.exp a * complexAverage μ.w (fun x => Complex.exp (h x - a + η x))
  convert hc using 1
  congr 1
  funext x
  congr 1
  ring

/-- The paper's complex-average lemma, with any chosen common anchor.

It proves nonvanishing of both original averages, the exponential identity
for an explicit logarithm of their ratio, and the `2 A W₁ + 4 δ` norm bound.
No optimal-coupling existence theorem is assumed: the imported comparison
passes from arbitrary coupling costs to their infimum.
-/
theorem paper_complex_average_with_anchor (μ ν : FinDist S)
    (h η η' : S → ℂ) (d : S → S → ℝ) {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : δ ∈ Set.Icc 0 (1 / 8 : ℝ))
    (hlip : ∀ x y, ‖h x - h y‖ ≤ A * d x y)
    (hosc : ∀ x y, ‖h x - h y‖ ≤ (1 / 8 : ℝ))
    (hη : ∀ x, ‖η x‖ ≤ δ) (hη' : ∀ x, ‖η' x‖ ≤ δ) (anchor : S) :
    expectComplex μ (fun x => Complex.exp (h x + η x)) ≠ 0 ∧
    expectComplex ν (fun x => Complex.exp (h x + η' x)) ≠ 0 ∧
    Complex.exp (centeredAverageLogRatio μ ν h η η' anchor) =
      expectComplex μ (fun x => Complex.exp (h x + η x)) /
        expectComplex ν (fun x => Complex.exp (h x + η' x)) ∧
    ‖centeredAverageLogRatio μ ν h η η' anchor‖ ≤ 2 * A * W d μ ν + 4 * δ := by
  have hu : ∀ x, ‖h x - h anchor + η x‖ ≤ (1 / 4 : ℝ) := by
    intro x
    have h := norm_add_le (h x - h anchor) (η x)
    have hh := hosc x anchor
    have he := hη x
    have hd := hδ.2
    linarith
  have hv : ∀ x, ‖h x - h anchor + η' x‖ ≤ (1 / 4 : ℝ) := by
    intro x
    have h := norm_add_le (h x - h anchor) (η' x)
    have hh := hosc x anchor
    have he := hη' x
    have hd := hδ.2
    linarith
  have hμ : expectComplex μ (fun x => Complex.exp (h x - h anchor + η x)) ≠ 0 :=
    complexAverage_exp_ne_zero μ.w μ.nonneg μ.sum_one _ hu
  have hν : expectComplex ν (fun x => Complex.exp (h x - h anchor + η' x)) ≠ 0 :=
    complexAverage_exp_ne_zero ν.w ν.nonneg ν.sum_one _ hv
  have hcμ := expectComplex_exp_center μ h η (h anchor)
  have hcν := expectComplex_exp_center ν h η' (h anchor)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcμ]
    exact mul_ne_zero (Complex.exp_ne_zero _) hμ
  · rw [hcν]
    exact mul_ne_zero (Complex.exp_ne_zero _) hν
  · rw [centeredAverageLogRatio, Complex.exp_sub, Complex.exp_log hμ, Complex.exp_log hν]
    rw [hcμ, hcν, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
  · apply complex_average_comparison_W (μ := μ) (ν := ν)
      (fun x => h x - h anchor) η (fun x => h x - h anchor) η' d hA δ hδ.2
      (fun x => hosc x anchor) (fun x => hosc x anchor) hη hη'
    intro x y
    have heq : (h x - h anchor) - (h y - h anchor) = h x - h y := by ring
    rw [heq]
    exact hlip x y

/-- The full finite-law conclusion of the paper's complex-average lemma.

The witness is the centered logarithmic difference defined above. Existence
of an anchor is derived from the probability law, so no nonemptiness
assumption on the finite space is added to the paper's hypotheses.
-/
theorem paper_complex_average (μ ν : FinDist S)
    (h η η' : S → ℂ) (d : S → S → ℝ) {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : δ ∈ Set.Icc 0 (1 / 8 : ℝ))
    (hlip : ∀ x y, ‖h x - h y‖ ≤ A * d x y)
    (hosc : ∀ x y, ‖h x - h y‖ ≤ (1 / 8 : ℝ))
    (hη : ∀ x, ‖η x‖ ≤ δ) (hη' : ∀ x, ‖η' x‖ ≤ δ) :
    expectComplex μ (fun x => Complex.exp (h x + η x)) ≠ 0 ∧
    expectComplex ν (fun x => Complex.exp (h x + η' x)) ≠ 0 ∧
    ∃ L : ℂ,
      Complex.exp L = expectComplex μ (fun x => Complex.exp (h x + η x)) /
        expectComplex ν (fun x => Complex.exp (h x + η' x)) ∧
      ‖L‖ ≤ 2 * A * W d μ ν + 4 * δ := by
  let anchor := Classical.choice (nonempty_of_finDist μ)
  obtain ⟨hμ, hν, hexp, hnorm⟩ := paper_complex_average_with_anchor μ ν h η η' d
    hA hδ hlip hosc hη hη' anchor
  exact ⟨hμ, hν, centeredAverageLogRatio μ ν h η η' anchor, hexp, hnorm⟩

/-- The logarithmic difference along simultaneous scaling of all exponents. -/
def scaledCenteredAverageLogRatio (μ ν : FinDist S) (h η η' : S → ℂ)
    (anchor : S) (z : ℂ) : ℂ :=
  Complex.log (expectComplex μ
    (fun x => Complex.exp (z * (h x - h anchor + η x)))) -
  Complex.log (expectComplex ν
    (fun x => Complex.exp (z * (h x - h anchor + η' x))))

/-- The constructed branch starts at zero when the exponents are zero. -/
@[simp] theorem scaledCenteredAverageLogRatio_zero (μ ν : FinDist S)
    (h η η' : S → ℂ) (anchor : S) :
    scaledCenteredAverageLogRatio μ ν h η η' anchor 0 = 0 := by
  simp [scaledCenteredAverageLogRatio]

/-- At the end of the scaling path this is the logarithm used in the bound. -/
@[simp] theorem scaledCenteredAverageLogRatio_one (μ ν : FinDist S)
    (h η η' : S → ℂ) (anchor : S) :
    scaledCenteredAverageLogRatio μ ν h η η' anchor 1 =
      centeredAverageLogRatio μ ν h η η' anchor := by
  simp [scaledCenteredAverageLogRatio, centeredAverageLogRatio]

/-- The logarithm used in the paper is obtained by continuous (indeed complex
differentiable) continuation under simultaneous scaling from zero.

The real interpolation interval `[0,1]` lies in this closed unit disk.
-/
theorem differentiableOn_scaledCenteredAverageLogRatio (μ ν : FinDist S)
    (h η η' : S → ℂ) (anchor : S) {δ : ℝ} (hδ : δ ≤ 1 / 8)
    (hosc : ∀ x y, ‖h x - h y‖ ≤ (1 / 8 : ℝ))
    (hη : ∀ x, ‖η x‖ ≤ δ) (hη' : ∀ x, ‖η' x‖ ≤ δ) :
    DifferentiableOn ℂ (scaledCenteredAverageLogRatio μ ν h η η' anchor)
      (Metric.closedBall (0 : ℂ) 1) := by
  have hdiff (w : S → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1 / 4) (π : FinDist S) :
      DifferentiableOn ℂ
        (fun z => Complex.log (expectComplex π (fun x => Complex.exp (z * w x))))
        (Metric.closedBall (0 : ℂ) 1) := by
    apply differentiableOn_log_complexAverage_exp π.w π.nonneg π.sum_one
      (fun x z => z * w x) (Metric.closedBall (0 : ℂ) 1)
    · intro x
      exact ((differentiable_id : Differentiable ℂ (fun z : ℂ => z)).mul_const
        (w x)).differentiableOn
    · intro z hz x
      have hz' : ‖z‖ ≤ (1 : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      rw [norm_mul]
      have hm := mul_le_mul hz' (hw x) (norm_nonneg (w x)) zero_le_one
      simpa using hm
  have hu : ∀ x, ‖h x - h anchor + η x‖ ≤ (1 / 4 : ℝ) := by
    intro x
    have h := norm_add_le (h x - h anchor) (η x)
    have hh := hosc x anchor
    have he := hη x
    linarith
  have hv : ∀ x, ‖h x - h anchor + η' x‖ ≤ (1 / 4 : ℝ) := by
    intro x
    have h := norm_add_le (h x - h anchor) (η' x)
    have hh := hosc x anchor
    have he := hη' x
    linarith
  exact (hdiff _ hu μ).sub (hdiff _ hv ν)

/-- At every point of the scaling disk, the continued logarithm exponentiates
to the ratio of the corresponding original, uncentered averages. -/
theorem exp_scaledCenteredAverageLogRatio (μ ν : FinDist S)
    (h η η' : S → ℂ) (anchor : S) {δ : ℝ} (hδ : δ ≤ 1 / 8)
    (hosc : ∀ x y, ‖h x - h y‖ ≤ (1 / 8 : ℝ))
    (hη : ∀ x, ‖η x‖ ≤ δ) (hη' : ∀ x, ‖η' x‖ ≤ δ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Complex.exp (scaledCenteredAverageLogRatio μ ν h η η' anchor z) =
      expectComplex μ (fun x => Complex.exp (z * (h x + η x))) /
        expectComplex ν (fun x => Complex.exp (z * (h x + η' x))) := by
  have hbound (e : S → ℂ) (he : ∀ x, ‖e x‖ ≤ δ) :
      ∀ x, ‖z * (h x - h anchor + e x)‖ ≤ (1 / 4 : ℝ) := by
    intro x
    have hn := norm_add_le (h x - h anchor) (e x)
    have ho := hosc x anchor
    have hp := he x
    have hq : ‖h x - h anchor + e x‖ ≤ (1 / 4 : ℝ) := by linarith
    rw [norm_mul]
    have hm := mul_le_mul hz hq (norm_nonneg _) zero_le_one
    simpa using hm
  have hfactor (π : FinDist S) (e : S → ℂ) :
      expectComplex π (fun x => Complex.exp (z * (h x + e x))) =
        Complex.exp (z * h anchor) *
          expectComplex π (fun x => Complex.exp (z * (h x - h anchor + e x))) := by
    calc
      _ = expectComplex π
          (fun x => Complex.exp (z * (h x - h anchor + e x) + z * h anchor)) := by
        congr 1
        funext x
        congr 1
        ring
      _ = _ := complexAverage_exp_add_const π.w _ _
  have hμ : expectComplex μ
      (fun x => Complex.exp (z * (h x - h anchor + η x))) ≠ 0 :=
    complexAverage_exp_ne_zero μ.w μ.nonneg μ.sum_one _ (hbound η hη)
  have hν : expectComplex ν
      (fun x => Complex.exp (z * (h x - h anchor + η' x))) ≠ 0 :=
    complexAverage_exp_ne_zero ν.w ν.nonneg ν.sum_one _ (hbound η' hη')
  rw [scaledCenteredAverageLogRatio, Complex.exp_sub, Complex.exp_log hμ, Complex.exp_log hν,
    hfactor μ η, hfactor ν η', mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

end

end CI2ZF
