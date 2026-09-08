import CI2ZF.SeparatorInsidePolynomial
import CI2ZF.HardMainPerturbation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Uniform local relative stability supplies actual analytic logarithms
on the activity disk, with the small budget needed by the shell proof. -/
namespace CI2ZF
noncomputable section

def principalResponseLog (f : ℂ → ℂ) (x z : ℂ) : ℂ := Complex.log (f z / f x)

theorem principalResponseLog_control (f : ℂ → ℂ) {x : ℂ} {r alpha : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball x r)) (hx : f x ≠ 0)
    (hbound : ∀ z ∈ Metric.ball x r,
      ‖f z / f x - 1‖ ≤ min (1 / 2 : ℝ) (alpha / 12)) :
    principalResponseLog f x x = 0 ∧
      DifferentiableOn ℂ (principalResponseLog f x) (Metric.ball x r) ∧
      (∀ z ∈ Metric.ball x r, Complex.exp (principalResponseLog f x z) = f z / f x) ∧
      ∀ z ∈ Metric.ball x r, ‖principalResponseLog f x z‖ ≤ alpha / 8 := by
  have hhalf (z : ℂ) (hz : z ∈ Metric.ball x r) :
      ‖f z / f x - 1‖ ≤ (1 / 2 : ℝ) := (hbound z hz).trans (min_le_left _ _)
  have hslit (z : ℂ) (hz : z ∈ Metric.ball x r) : f z / f x ∈ Complex.slitPlane := by
    have hs := Complex.mem_slitPlane_of_norm_lt_one ((hhalf z hz).trans_lt (by norm_num))
    simpa only [add_sub_cancel] using hs
  refine ⟨by simp [principalResponseLog, hx], ?_, ?_, ?_⟩
  · exact (hf.div_const _).clog hslit
  · intro z hz
    exact Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz))
  · intro z hz
    have hb := Complex.norm_log_one_add_half_le_self (hhalf z hz)
    simp only [add_sub_cancel] at hb
    have ha := (hbound z hz).trans (min_le_right _ _)
    change ‖Complex.log (f z / f x)‖ ≤ _
    linarith

namespace Potts.Separator
open PottsCI
attribute [local instance] Classical.propDecidable

/-- A single radius works for the normalized analytic logarithms of all
actual inside polynomials of bounded size, even if some vanish at zero. -/
theorem bounded_inside_positive_log_stability (C : Type*) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0) {alpha : ℝ} (ha : 0 < alpha) :
    ∃ ε > 0, ∀ {U S O : Type*} [Fintype U] [Fintype S] [Fintype O]
      (I : PinningData (Vertex U S O) C), I.DegreeBound Δ →
      Fintype.card U + Fintype.card S ≤ B → ∀ ξ : S → C, ∀ x ∈ K,
      let L := principalResponseLog (fun z => insidePartition I z ξ) x
      L x = 0 ∧ DifferentiableOn ℂ L (Metric.ball x ε) ∧
      (∀ z ∈ Metric.ball x ε, Complex.exp (L z) =
        insidePartition I z ξ / insidePartition I x ξ) ∧
      ∀ z ∈ Metric.ball x ε, ‖L z‖ ≤ alpha / 8 := by
  obtain ⟨ε, hε, hb⟩ := bounded_inside_positive_relative_stability C Δ B K hK hreal
    (η := min (1 / 2 : ℝ) (alpha / 12)) (lt_min (by norm_num) (by positivity))
  refine ⟨ε, hε, ?_⟩
  intro U S O _ _ _ I hd hB ξ x hx
  have hpoly : (fun z : ℂ => insidePartition I z ξ) = (insidePolynomial I ξ).eval := by
    funext z
    exact (insidePolynomial_eval I ξ z).symm
  have hnz : insidePartition I x ξ ≠ 0 := by
    obtain ⟨t, ht, rfl⟩ := hreal hx
    have hm : insidePartition I (t : ℂ) ξ = ((insidePartition I t ξ : ℝ) : ℂ) := by
      simpa only [Complex.ofRealHom_eq_coe] using
        (map_insidePartition Complex.ofRealHom I t ξ).symm
    rw [hm]
    exact_mod_cast (insidePartition_pos I t ht ξ).ne'
  apply principalResponseLog_control
  · rw [hpoly]
    exact (Polynomial.differentiable _).differentiableOn
  · exact hnz
  · intro z hz
    exact (hb I hd hB ξ x hx z hz).le

end Potts.Separator
end
end CI2ZF
