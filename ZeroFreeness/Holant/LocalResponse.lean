import ZeroFreeness.Holant.PolynomialStability
import ZeroFreeness.Holant.Analytic
import ZeroFreeness.Analysis.AnalyticLog

/-! A numerical local radius and the normalized analytic response used
when the root component has bounded size. The radius formula is independent
of the edge type and of the graph. -/
namespace ZeroFreeness.Holant
open scoped BigOperators
open Set Metric
noncomputable section

def localRadius (N : ℕ) (B R α : ℝ) : ℝ :=
  min 1 (α / (8 * polynomialLipschitzConstant N B (R + 1)))

theorem localRadius_pos (N : ℕ) {B R α : ℝ} (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hα : 0 < α) : 0 < localRadius N B R α := by
  have hK := polynomialLipschitzConstant_pos N hB (by linarith : 0 ≤ R + 1)
  exact lt_min zero_lt_one (div_pos hα (by positivity))

theorem localRadius_budget (N : ℕ) {B R α : ℝ} (hB : 0 ≤ B)
    (hR : 0 ≤ R) :
    polynomialLipschitzConstant N B (R + 1) * localRadius N B R α ≤ α / 8 := by
  have hK := polynomialLipschitzConstant_pos N hB (by linarith : 0 ≤ R + 1)
  have hm := min_le_right (1 : ℝ) (α / (8 * polynomialLipschitzConstant N B (R + 1)))
  have ht := (le_div_iff₀ (by positivity : 0 < 8 * polynomialLipschitzConstant N B (R + 1))).mp hm
  change _ * min _ _ ≤ _
  linarith

theorem local_polynomial_relative_bound {E : Type*} [DecidableEq E]
    (edges : Finset E) (c : Finset E → ℂ) (x : E → ℝ) (z : E → ℂ)
    {N : ℕ} {B R α : ℝ} (hN : edges.card ≤ N) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hα : 0 < α)
    (hc : ∀ s ⊆ edges, ‖c s‖ ≤ B) (hx : ∀ e ∈ edges, x e ∈ Icc 0 R)
    (hz : ∀ e ∈ edges, ‖z e - (x e : ℂ)‖ < localRadius N B R α)
    (hbase : 1 ≤ ‖multilinear edges c (fun e => (x e : ℂ))‖) :
    ‖multilinear edges c z / multilinear edges c (fun e => (x e : ℂ)) - 1‖ ≤ α / 8 := by
  have hε := localRadius_pos N hB hR hα
  have hε1 : localRadius N B R α ≤ 1 := min_le_left _ _
  have hxn : ∀ e ∈ edges, ‖(x e : ℂ)‖ ≤ R + 1 := by
    intro e he
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx e he).1]
    linarith [(hx e he).2]
  have hzn : ∀ e ∈ edges, ‖z e‖ ≤ R + 1 := by
    intro e he
    have ht := norm_sub_norm_le (z e) (x e : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx e he).1] at ht
    linarith [hz e he, (hx e he).2]
  have hp : 0 < ‖multilinear edges c (fun e => (x e : ℂ))‖ := zero_lt_one.trans_le hbase
  rw [div_sub_one (norm_pos_iff.mp hp), norm_div]
  have hl := multilinear_lipschitz edges c z (fun e => (x e : ℂ)) hN hB
    (by linarith : 1 ≤ R + 1) hε.le hc hzn hxn (fun e he => (hz e he).le)
  exact (div_le_self (norm_nonneg _) hbase).trans (hl.trans (localRadius_budget N hB hR))

def localResponseLog (P Q X Y : ℂ) : ℂ := Complex.log (P / X) - Complex.log (Q / Y)

/-- The bounded local comparison includes a specific logarithm of the
normalized quotient. Both perturbed polynomials are proved nonzero. -/
theorem local_response {P Q X Y : ℂ} (hX : X ≠ 0) (hY : Y ≠ 0)
    {α : ℝ} (hα : 0 < α) (hαsmall : α ≤ 1 / 4)
    (hP : ‖P / X - 1‖ ≤ α / 8) (hQ : ‖Q / Y - 1‖ ≤ α / 8) :
    P ≠ 0 ∧ Q ≠ 0 ∧ Complex.exp (localResponseLog P Q X Y) = (P / X) / (Q / Y) ∧
      ‖localResponseLog P Q X Y‖ < α := by
  have hPsmall : ‖P / X - 1‖ ≤ (1 / 3 : ℝ) := by linarith
  have hQsmall : ‖Q / Y - 1‖ ≤ (1 / 3 : ℝ) := by linarith
  have hPn : P ≠ 0 := by intro h; simp [h] at hP; linarith
  have hQn : Q ≠ 0 := by intro h; simp [h] at hQ; linarith
  refine ⟨hPn, hQn, ?_, ?_⟩
  · rw [localResponseLog, Complex.exp_sub, Complex.exp_log (div_ne_zero hPn hX),
      Complex.exp_log (div_ne_zero hQn hY)]
  · have h := norm_log_sub_log_le_three_halves (P / X) (Q / Y) hPsmall hQsmall
    have ht : ‖P / X - Q / Y‖ ≤ ‖P / X - 1‖ + ‖Q / Y - 1‖ := by
      simpa using norm_sub_le (P / X - 1) (Q / Y - 1)
    unfold localResponseLog
    linarith

/-- Local logarithms are analytically continued from the common real
base point on a disk; no pointwise choice of an unrelated branch is used. -/
theorem localResponseLog_differentiable (P Q : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hP : DifferentiableOn ℂ P (ball c r)) (hQ : DifferentiableOn ℂ Q (ball c r))
    (_hPc : P c ≠ 0) (_hQc : Q c ≠ 0)
    (hbP : ∀ z ∈ ball c r, ‖P z / P c - 1‖ ≤ (1 / 3 : ℝ))
    (hbQ : ∀ z ∈ ball c r, ‖Q z / Q c - 1‖ ≤ (1 / 3 : ℝ)) :
    DifferentiableOn ℂ (fun z => localResponseLog (P z) (Q z) (P c) (Q c)) (ball c r) := by
  apply DifferentiableOn.sub
  · exact (hP.div_const (P c)).clog (fun z hz => mem_slitPlane_of_norm_sub_one_le_third _ (hbP z hz))
  · exact (hQ.div_const (Q c)).clog (fun z hz => mem_slitPlane_of_norm_sub_one_le_third _ (hbQ z hz))

theorem localResponseLog_zero (X Y : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) :
    localResponseLog X Y X Y = 0 := by simp [localResponseLog, hX, hY]

end
end ZeroFreeness.Holant
