import CI2ZF.PaperComplexAverage
import CI2ZF.AnalyticLog

/-! The complex-average logarithm continued in the actual activity
variable, with branch uniqueness on the full disk. -/
namespace CI2ZF
open PottsCI PottsCI.FinDist
noncomputable section
variable {S : Type*} [Fintype S]

def analyticCenteredLog (μ ν : FinDist S) (h η θ : S → ℂ → ℂ)
    (anchor : S) (z : ℂ) : ℂ :=
  centeredAverageLogRatio μ ν (fun i => h i z) (fun i => η i z) (fun i => θ i z) anchor

theorem analyticCenteredLog_differentiable (μ ν : FinDist S)
    (h η θ : S → ℂ → ℂ) (anchor : S) (D : Set ℂ)
    (hh : ∀ i, DifferentiableOn ℂ (h i) D)
    (hη : ∀ i, DifferentiableOn ℂ (η i) D)
    (hθ : ∀ i, DifferentiableOn ℂ (θ i) D)
    (hosc : ∀ z ∈ D, ∀ i j, ‖h i z - h j z‖ ≤ (1 / 8 : ℝ))
    (hbη : ∀ z ∈ D, ∀ i, ‖η i z‖ ≤ (1 / 8 : ℝ))
    (hbθ : ∀ z ∈ D, ∀ i, ‖θ i z‖ ≤ (1 / 8 : ℝ)) :
    DifferentiableOn ℂ (analyticCenteredLog μ ν h η θ anchor) D := by
  have ha (e : S → ℂ → ℂ) (he : ∀ i, DifferentiableOn ℂ (e i) D)
      (hb : ∀ z ∈ D, ∀ i, ‖e i z‖ ≤ (1 / 8 : ℝ)) (π : FinDist S) :
      DifferentiableOn ℂ (fun z => Complex.log
        (expectComplex π (fun i => Complex.exp (h i z - h anchor z + e i z)))) D := by
    apply differentiableOn_log_complexAverage_exp π.w π.nonneg π.sum_one
    · intro i
      exact ((hh i).sub (hh anchor)).add (he i)
    · intro z hz i
      have ht := norm_add_le (h i z - h anchor z) (e i z)
      have ho := hosc z hz i anchor
      have hb' := hb z hz i
      linarith
  exact (ha η hη hbη μ).sub (ha θ hθ hbθ ν)

theorem analyticCenteredLog_zero (μ ν : FinDist S) (h η θ : S → ℂ → ℂ)
    (anchor : S) (x : ℂ) (hh : ∀ i, h i x = 0) (hη : ∀ i, η i x = 0)
    (hθ : ∀ i, θ i x = 0) : analyticCenteredLog μ ν h η θ anchor x = 0 := by
  simp only [analyticCenteredLog, centeredAverageLogRatio, hh, hη, hθ,
    sub_self, add_zero]
  change Complex.log (complexAverage μ.w (fun _ => Complex.exp (0 : ℂ))) -
    Complex.log (complexAverage ν.w (fun _ => Complex.exp (0 : ℂ))) = 0
  rw [log_complexAverage_exp_zero μ.w μ.sum_one,
    log_complexAverage_exp_zero ν.w ν.sum_one, sub_self]

/-- Any normalized analytic branch of the separator-response quotient
equals the explicit centered branch, so it inherits the Wasserstein bound.
The continuation is in `z`, not merely in an auxiliary scaling parameter. -/
theorem continued_average_log_bound (μ ν : FinDist S) (h η θ : S → ℂ → ℂ)
    (anchor : S) (d : S → S → ℝ) {x : ℂ} {r A δ : ℝ} (hr : 0 < r)
    (hA : 0 ≤ A) (hδ : δ ∈ Set.Icc 0 (1 / 8 : ℝ))
    (hh : ∀ i, DifferentiableOn ℂ (h i) (Metric.ball x r))
    (hη : ∀ i, DifferentiableOn ℂ (η i) (Metric.ball x r))
    (hθ : ∀ i, DifferentiableOn ℂ (θ i) (Metric.ball x r))
    (hh0 : ∀ i, h i x = 0) (hη0 : ∀ i, η i x = 0) (hθ0 : ∀ i, θ i x = 0)
    (hlip : ∀ z ∈ Metric.ball x r, ∀ i j, ‖h i z - h j z‖ ≤ A * d i j)
    (hosc : ∀ z ∈ Metric.ball x r, ∀ i j, ‖h i z - h j z‖ ≤ (1 / 8 : ℝ))
    (hbη : ∀ z ∈ Metric.ball x r, ∀ i, ‖η i z‖ ≤ δ)
    (hbθ : ∀ z ∈ Metric.ball x r, ∀ i, ‖θ i z‖ ≤ δ)
    (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (Metric.ball x r)) (hL0 : L x = 0)
    (hexp : ∀ z ∈ Metric.ball x r, Complex.exp (L z) =
      expectComplex μ (fun i => Complex.exp (h i z + η i z)) /
        expectComplex ν (fun i => Complex.exp (h i z + θ i z))) :
    ∀ z ∈ Metric.ball x r, ‖L z‖ ≤ 2 * A * W d μ ν + 4 * δ := by
  have hpoint (z : ℂ) (hz : z ∈ Metric.ball x r) :=
    paper_complex_average_with_anchor μ ν (fun i => h i z) (fun i => η i z)
      (fun i => θ i z) d hA hδ (hlip z hz) (hosc z hz) (hbη z hz) (hbθ z hz) anchor
  have hEq : Set.EqOn L (analyticCenteredLog μ ν h η θ anchor) (Metric.ball x r) := by
    apply logs_eq_on_ball_of_exp_eq hr L _ hL
      (analyticCenteredLog_differentiable μ ν h η θ anchor _ hh hη hθ hosc
        (fun z hz i => (hbη z hz i).trans hδ.2)
        (fun z hz i => (hbθ z hz i).trans hδ.2))
    · intro z hz
      exact (hexp z hz).trans (hpoint z hz).2.2.1.symm
    · rw [hL0, analyticCenteredLog_zero μ ν h η θ anchor x hh0 hη0 hθ0]
  intro z hz
  rw [hEq hz]
  exact (hpoint z hz).2.2.2

end
end CI2ZF
