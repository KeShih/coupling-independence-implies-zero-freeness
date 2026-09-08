import CI2ZF.LocalResponseLog

/-! Uniform logarithmic budgets for bounded components and root boundary
monomials. The radius precedes the instance and the compact real base. -/
namespace CI2ZF
noncomputable section

/-- Relative stability at the center itself supplies its nonzero value. -/
theorem principalResponseLog_control_of_relative (f : ℂ → ℂ) {x : ℂ} {r alpha : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (Metric.ball x r))
    (hb : ∀ z ∈ Metric.ball x r, ‖f z / f x - 1‖ ≤ min (1 / 2 : ℝ) (alpha / 12)) :
    principalResponseLog f x x = 0 ∧
      DifferentiableOn ℂ (principalResponseLog f x) (Metric.ball x r) ∧
      (∀ z ∈ Metric.ball x r, Complex.exp (principalResponseLog f x z) = f z / f x) ∧
      ∀ z ∈ Metric.ball x r, ‖principalResponseLog f x z‖ ≤ alpha / 8 := by
  have hx : f x ≠ 0 := by
    intro hzero
    have hc := (hb x (Metric.mem_ball_self hr)).trans (min_le_left _ _)
    simp only [hzero, zero_div, zero_sub, norm_neg, norm_one] at hc
    norm_num at hc
  exact principalResponseLog_control f hf hx hb

namespace Potts
open PottsCI Separator
attribute [local instance] Classical.propDecidable

/-- The bounded-component local logarithms, uniformly on a compact
positive real set; no colour threshold is needed at positive activity. -/
theorem bounded_pinning_positive_log_stability (C : Type*) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0) {alpha : ℝ} (ha : 0 < alpha) :
    ∃ ε > 0, ∀ {V : Type*} [Fintype V] (I : PinningData V C),
      I.DegreeBound Δ → Fintype.card V ≤ B → ∀ x ∈ K,
      let L := principalResponseLog (pinningProductPartition I) x
      L x = 0 ∧ DifferentiableOn ℂ L (Metric.ball x ε) ∧
      (∀ z ∈ Metric.ball x ε, Complex.exp (L z) =
        pinningProductPartition I z / pinningProductPartition I x) ∧
      ∀ z ∈ Metric.ball x ε, ‖L z‖ ≤ alpha / 8 := by
  obtain ⟨ε, hε, hb⟩ := bounded_pinning_positive_relative_stability C Δ B K hK hreal
    (η := min (1 / 2 : ℝ) (alpha / 12)) (lt_min (by norm_num) (by positivity))
  refine ⟨ε, hε, ?_⟩
  intro V _ I hd hB x hx
  apply principalResponseLog_control_of_relative _ hε
  · have he : (pinningProductPartition I : ℂ → ℂ) = (pinningPolynomial I).eval := by
      funext z
      exact (pinningPolynomial_eval I z).symm
    rw [he]
    exact (Polynomial.differentiable _).differentiableOn
  · intro z hz
    exact (hb I hd hB x hx z hz).le

/-- The same radius construction includes the hard base when every
bounded datum has a hard extension, supplied by the colour threshold. -/
theorem bounded_pinning_nonnegative_log_stability (C : Type*) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Set.Ici 0) {alpha : ℝ} (ha : 0 < alpha) :
    ∃ ε > 0, ∀ {V : Type*} [Fintype V] (I : PinningData V C),
      I.DegreeBound Δ → Fintype.card V ≤ B → ∀ x ∈ K,
      let L := principalResponseLog (pinningProductPartition I) x
      L x = 0 ∧ DifferentiableOn ℂ L (Metric.ball x ε) ∧
      (∀ z ∈ Metric.ball x ε, Complex.exp (L z) =
        pinningProductPartition I z / pinningProductPartition I x) ∧
      ∀ z ∈ Metric.ball x ε, ‖L z‖ ≤ alpha / 8 := by
  obtain ⟨ε, hε, hb⟩ := bounded_pinning_relative_stability C Δ B hq K hK hreal
    (η := min (1 / 2 : ℝ) (alpha / 12)) (lt_min (by norm_num) (by positivity))
  refine ⟨ε, hε, ?_⟩
  intro V _ I hd hB x hx
  apply principalResponseLog_control_of_relative _ hε
  · have he : (pinningProductPartition I : ℂ → ℂ) = (pinningPolynomial I).eval := by
      funext z
      exact (pinningPolynomial_eval I z).symm
    rw [he]
    exact (Polynomial.differentiable _).differentiableOn
  · intro z hz
    exact (hb I hd hB x hx z hz).le

/-- All possible root boundary powers have a uniformly small analytic
response logarithm, including exponent zero. -/
theorem bounded_boundary_positive_log_stability (Δ : ℕ) (K : Set ℂ)
    (hK : IsCompact K) (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0)
    {alpha : ℝ} (ha : 0 < alpha) :
    ∃ ε > 0, ∀ m : ℕ, m ≤ Δ → ∀ x ∈ K,
      let L := principalResponseLog (fun z : ℂ => z ^ m) x
      L x = 0 ∧ DifferentiableOn ℂ L (Metric.ball x ε) ∧
      (∀ z ∈ Metric.ball x ε, Complex.exp (L z) = z ^ m / x ^ m) ∧
      ∀ z ∈ Metric.ball x ε, ‖L z‖ ≤ alpha / 8 := by
  let p : Fin (Δ + 1) → Polynomial ℂ := fun m => Polynomial.X ^ m.val
  have hn : ∀ m : Fin (Δ + 1), ∀ x ∈ K, (p m).eval x ≠ 0 := by
    intro m x hx
    obtain ⟨t, ht, rfl⟩ := hreal hx
    simp only [p, Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero _ (by exact_mod_cast ht.ne')
  obtain ⟨ε, hε, hb⟩ := finite_polynomial_relative_stability p K hK hn
    (η := min (1 / 2 : ℝ) (alpha / 12)) (lt_min (by norm_num) (by positivity))
  refine ⟨ε, hε, ?_⟩
  intro m hm x hx
  apply principalResponseLog_control_of_relative _ hε
  · exact (differentiable_id.pow m).differentiableOn
  · intro z hz
    simpa only [p, Polynomial.eval_pow, Polynomial.eval_X] using
      (hb ⟨m, by omega⟩ x hx z hz).le

end Potts
end
end CI2ZF
