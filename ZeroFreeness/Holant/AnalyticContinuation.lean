import ZeroFreeness.Holant.Analytic
import ZeroFreeness.Analysis.AnalyticLog

/-! Analytic continuation of the additive-error shell comparison. The
normalization is in the actual complex interpolation parameter. -/
namespace ZeroFreeness.Holant
open PottsCI PottsCI.FinDist Set Metric
noncomputable section
variable {S : Type*} [Fintype S]

theorem exponentialAverage_differentiable (μ : FinDist S) (h : S → ℂ → ℂ)
    (D : Set ℂ) (hh : ∀ s, DifferentiableOn ℂ (h s) D) :
    DifferentiableOn ℂ (fun z => exponentialAverage μ (fun s => h s z)) D := by
  unfold exponentialAverage expectComplex
  exact DifferentiableOn.fun_sum fun s _ => (hh s).cexp.const_mul (μ.w s : ℂ)

theorem centeredLog_differentiable (μ ν : FinDist S) (h : S → ℂ → ℂ) (b : S)
    (D : Set ℂ) (hh : ∀ s, DifferentiableOn ℂ (h s) D)
    (hosc : ∀ z ∈ D, ∀ s t, ‖h s z - h t z‖ ≤ (1 / 8 : ℝ)) :
    DifferentiableOn ℂ
      (fun z => centeredAverageLogRatio μ ν (fun s => h s z) (fun _ => 0) (fun _ => 0) b) D := by
  have hd (π : FinDist S) : DifferentiableOn ℂ
      (fun z => Complex.log (expectComplex π (fun s => Complex.exp (h s z - h b z)))) D := by
    apply differentiableOn_log_complexAverage_exp π.w π.nonneg π.sum_one
    · intro s
      exact (hh s).sub (hh b)
    · intro z hz s
      exact (hosc z hz s b).trans (by norm_num)
  simp only [centeredAverageLogRatio, add_zero]
  apply DifferentiableOn.sub
  · exact hd μ
  · exact hd ν

theorem additiveResponseLog_differentiable (μ ν : FinDist S) (h : S → ℂ → ℂ) (b : S)
    (E F : ℂ → ℂ) (D : Set ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 2 / 9)
    (hh : ∀ s, DifferentiableOn ℂ (h s) D)
    (hE : DifferentiableOn ℂ E D) (hF : DifferentiableOn ℂ F D)
    (hosc : ∀ z ∈ D, ∀ s t, ‖h s z - h t z‖ ≤ (1 / 8 : ℝ))
    (hbE : ∀ z ∈ D, ‖E z‖ ≤ δ * ‖Complex.exp (h b z)‖)
    (hbF : ∀ z ∈ D, ‖F z‖ ≤ δ * ‖Complex.exp (h b z)‖) :
    DifferentiableOn ℂ (fun z => additiveResponseLog μ ν (fun s => h s z) b (E z) (F z)) D := by
  have hc (π : FinDist S) (K : ℂ → ℂ) (hK : DifferentiableOn ℂ K D)
      (hbK : ∀ z ∈ D, ‖K z‖ ≤ δ * ‖Complex.exp (h b z)‖) :
      DifferentiableOn ℂ (fun z => Complex.log
        (1 + K z / exponentialAverage π (fun s => h s z))) D := by
    apply DifferentiableOn.clog
    · exact (differentiableOn_const (1 : ℂ) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) D).add
        (hK.div (exponentialAverage_differentiable π h D hh)
        (fun z hz => exponentialAverage_ne_zero π (fun s => h s z) b (fun s => hosc z hz s b)))
    · intro z hz
      apply mem_slitPlane_of_norm_sub_one_le_third
      simp only [add_sub_cancel_left]
      have hb := relative_shell_error_le π (fun s => h s z) b (fun s => hosc z hz s b)
        (K z) hδ (hbK z hz)
      linarith
  exact ((centeredLog_differentiable μ ν h b D hh hosc).add (hc μ E hE hbE)).sub
    (hc ν F hF hbF)

theorem additiveResponseLog_zero (μ ν : FinDist S) (h : S → ℂ) (b : S)
    (hh : ∀ s, h s = 0) : additiveResponseLog μ ν h b 0 0 = 0 := by
  simp [additiveResponseLog, centeredAverageLogRatio, hh]

/-- The actual continued logarithm inherits the shell estimate: uniqueness
discharges all branch choices, including when an activity is zero. -/
theorem continued_additive_response (μ ν : FinDist S) (h : S → ℂ → ℂ) (b : S)
    (E F L : ℂ → ℂ) (d : S → S → ℝ) {c : ℂ} {r α δ : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 2 / 9)
    (hδbudget : δ ≤ α / 16) (hW : W d μ ν ≤ 1 / 64)
    (hh : ∀ s, DifferentiableOn ℂ (h s) (ball c r))
    (hE : DifferentiableOn ℂ E (ball c r)) (hF : DifferentiableOn ℂ F (ball c r))
    (hL : DifferentiableOn ℂ L (ball c r))
    (hh0 : ∀ s, h s c = 0) (hE0 : E c = 0) (hF0 : F c = 0) (hL0 : L c = 0)
    (hlip : ∀ z ∈ ball c r, ∀ s t, ‖h s z - h t z‖ ≤ α * d s t)
    (hosc : ∀ z ∈ ball c r, ∀ s t, ‖h s z - h t z‖ ≤ (1 / 8 : ℝ))
    (hbE : ∀ z ∈ ball c r, ‖E z‖ ≤ δ * ‖Complex.exp (h b z)‖)
    (hbF : ∀ z ∈ ball c r, ‖F z‖ ≤ δ * ‖Complex.exp (h b z)‖)
    (hexp : ∀ z ∈ ball c r, Complex.exp (L z) =
      (exponentialAverage μ (fun s => h s z) + E z) /
      (exponentialAverage ν (fun s => h s z) + F z)) :
    ∀ z ∈ ball c r, ‖L z‖ < α := by
  have heq : EqOn L (fun z => additiveResponseLog μ ν (fun s => h s z) b (E z) (F z))
      (ball c r) := by
    apply logs_eq_on_ball_of_exp_eq hr L _ hL
      (additiveResponseLog_differentiable μ ν h b E F (ball c r) hδ hδsmall hh hE hF hosc hbE hbF)
    · intro z hz
      exact (hexp z hz).trans ((additive_response μ ν (fun s => h s z) b d hα.le hδ
        hδsmall (hlip z hz) (hosc z hz) (E z) (F z) (hbE z hz) (hbF z hz)).2.2.1.symm)
    · rw [hL0, hE0, hF0, additiveResponseLog_zero μ ν (fun s => h s c) b hh0]
  intro z hz
  rw [heq hz]
  exact additive_response_closes μ ν (fun s => h s z) b d hα hδ hδsmall hδbudget hW
    (hlip z hz) (hosc z hz) (E z) (F z) (hbE z hz) (hbF z hz)

end
end ZeroFreeness.Holant
