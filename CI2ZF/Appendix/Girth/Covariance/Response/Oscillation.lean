import CI2ZF.Appendix.Girth.Covariance.Response.Step

/-! The unprojected colour response is bounded before any division by
a root marginal. This yields a bound uniform over root colours. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C U : Type*} [Fintype Ω] [Fintype C] [Fintype U] [DecidableEq C]

theorem unprojected_block_bound (s : ℝ) (r : U → FinDist C) (h : U → C → ℝ)
    {B H : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hr : ∀ u c, (r u).w c ≤ B) (hh : ∀ u c, |h u c| ≤ Real.sqrt B * H) (c : C) :
    |s * ∑ u, Real.sqrt ((r u).w c) * h u c| ≤ (Fintype.card U : ℝ) * B * H := by
  have ht (u : U) : |Real.sqrt ((r u).w c) * h u c| ≤ B * H := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt B * (Real.sqrt B * H) :=
        mul_le_mul (Real.sqrt_le_sqrt (hr u c)) (hh u c) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [← mul_assoc, Real.mul_self_sqrt hB]
  rw [abs_mul, abs_of_nonneg hs]
  calc
    _ ≤ s * ∑ u, |Real.sqrt ((r u).w c) * h u c| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hs
    _ ≤ s * ∑ _u : U, B * H :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ht u) hs
    _ ≤ ∑ _u : U, B * H := mul_le_of_le_one_left (by positivity) hs1
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem colour_oscillation_of_expansion (p : CovarianceScale) (s : ℝ)
    (r : U → FinDist C) (h : U → C → ℝ) (μ : FinDist Ω) (G : C → Ω → ℝ) (f : Ω → ℝ)
    (localSource response : C → ℝ) (constant : ℝ) {χ A U₀ V₀ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hχ : 0 ≤ χ) (hA : 0 ≤ A) (hU : 0 ≤ U₀) (hV : 0 ≤ V₀)
    (hdeg : (Fintype.card U : ℝ) ≤ p.Δ) (hr : ∀ u c, (r u).w c ≤ p.B)
    (hh : ∀ u c, |h u c| ≤ Real.sqrt p.B * (χ * V₀ * A))
    (hG : ColourCovarianceBound μ G (p.g ^ 2))
    (hf : variance μ f ≤ (p.Δ * χ ^ 2 * A * U₀) ^ 2)
    (hlocal : ∀ c, |localSource c| ≤ (1 + p.ell * χ) * A)
    (heq : ∀ c, response c = constant + localSource c + covariance μ f (G c) -
      s * ∑ u, Real.sqrt ((r u).w c) * h u c) (c d : C) :
    |response c - response d| ≤
      (2 * (1 + p.ell * χ + p.K * χ ^ 2 * U₀) + 2 * (p.Δ * p.B) * χ * V₀) * A := by
  have hD : 0 ≤ p.Δ * χ ^ 2 * A * U₀ := by positivity [p.Δ_pos]
  have hpoint (b : C) : |response b - constant| ≤
      ((1 + p.ell * χ) * A + p.g * (p.Δ * χ ^ 2 * A * U₀)) + p.Δ * p.B * (χ * V₀ * A) := by
    rw [heq]
    have he : constant + localSource b + covariance μ f (G b) -
        s * ∑ u, Real.sqrt ((r u).w b) * h u b - constant =
        (localSource b + covariance μ f (G b)) - s * ∑ u, Real.sqrt ((r u).w b) * h u b := by ring
    rw [he]
    calc
      _ ≤ |localSource b| + |covariance μ f (G b)| +
          |s * ∑ u, Real.sqrt ((r u).w b) * h u b| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (1 + p.ell * χ) * A + p.g * (p.Δ * χ ^ 2 * A * U₀) +
          (Fintype.card U : ℝ) * p.B * (χ * V₀ * A) :=
        add_le_add (add_le_add (hlocal b) (covariance_source_infty μ G f p.g_nonneg hD hG hf b))
          (unprojected_block_bound s r h hs hs1 p.B_pos.le (by positivity) hr hh b)
      _ ≤ _ := by gcongr; exact p.B_pos.le
  have he : response c - response d = (response c - constant) - (response d - constant) := by ring
  rw [he]
  calc
    _ ≤ |response c - constant| + |response d - constant| := abs_sub _ _
    _ ≤ (((1 + p.ell * χ) * A + p.g * (p.Δ * χ ^ 2 * A * U₀)) + p.Δ * p.B * (χ * V₀ * A)) +
        (((1 + p.ell * χ) * A + p.g * (p.Δ * χ ^ 2 * A * U₀)) + p.Δ * p.B * (χ * V₀ * A)) :=
      add_le_add (hpoint c) (hpoint d)
    _ = _ := by unfold CovarianceScale.K; ring

theorem colour_oscillation_supersolution (p : CovarianceScale) {χ A U V : ℝ}
    (hχ : χ = covarianceChi p.δ) (hU : U = p.responseU) (hV : V = p.responseV)
    (response : C → ℝ) (h : ∀ c d, |response c - response d| ≤
      (2 * (1 + p.ell * χ + p.K * χ ^ 2 * U) + 2 * (p.Δ * p.B) * χ * V) * A) :
    ∀ c d, |response c - response d| ≤ p.responseM * A := by
  subst χ U V
  exact h

end
end CI2ZF.Appendix.Girth
