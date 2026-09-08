import CI2ZF.ExteriorRepinning
import CI2ZF.AnalyticLog
import CI2ZF.HammingResponses
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The exterior logarithm is Lipschitz by the induction hypothesis on
actual smaller one-root instances. Analytic uniqueness identifies the
continued branches before the coordinate bounds are telescoped. -/

namespace CI2ZF.Potts.Separator

open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

theorem exteriorPartition_eq_pinningProductPartition
    (I : PinningData (Vertex U S O) C) (hsep : Separates I) (ξ : S → C) (z : ℂ) :
    exteriorPartition I z ξ = pinningProductPartition (exteriorData I ξ) z := by
  unfold exteriorPartition pinningProductPartition
  apply Finset.sum_congr rfl
  intro ζ _
  exact exteriorWeight_eq_pinningProductWeight I hsep z ξ ζ

theorem exteriorPartition_differentiable
    (I : PinningData (Vertex U S O) C) (hsep : Separates I) (ξ : S → C) :
    Differentiable ℂ (fun z : ℂ => exteriorPartition I z ξ) := by
  have he : (fun z : ℂ => exteriorPartition I z ξ) =
      fun z => (pinningPolynomial (exteriorData I ξ)).eval z := by
    funext z
    rw [exteriorPartition_eq_pinningProductPartition I hsep, pinningPolynomial_eval]
  rw [he]
  exact Polynomial.differentiable _

/-- Zero-freeness of the actual smaller exterior supplies analytic
response logs normalized at the real or complex base point. -/
theorem exists_exterior_response_logs
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    {x : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hnz : ∀ ξ : S → C, ∀ z ∈ Metric.ball x ε, exteriorPartition I z ξ ≠ 0) :
    ∃ h : (S → C) → ℂ → ℂ,
      (∀ ξ, h ξ x = 0) ∧
      (∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball x ε)) ∧
      ∀ ξ, ∀ z ∈ Metric.ball x ε,
        Complex.exp (h ξ z) = exteriorPartition I z ξ / exteriorPartition I x ξ := by
  have hex (ξ : S → C) := exists_normalized_log_on_ball
    (fun z => exteriorPartition I z ξ) hε
    (exteriorPartition_differentiable I hsep ξ).differentiableOn (hnz ξ)
  choose h hzero hderiv hexp using hex
  refine ⟨h, hzero, ?_, hexp⟩
  intro ξ z hz
  exact (hderiv ξ z hz).differentiableAt.differentiableWithinAt

/-- A normalized analytic one-root quotient bound on every smaller
instance gives the exterior's full Hamming Lipschitz bound. The only
response hypothesis here is applied to the explicitly constructed,
strictly smaller `unpinnedExteriorData`. -/
theorem exterior_logs_lipschitz_of_smaller_root_responses [Nonempty U]
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) {x : ℂ} {ε α : ℝ} (hε : 0 < ε)
    (h : (S → C) → ℂ → ℂ)
    (hzero : ∀ ξ, h ξ x = 0)
    (hdiff : ∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball x ε))
    (hexp : ∀ ξ, ∀ z ∈ Metric.ball x ε,
      Complex.exp (h ξ z) = exteriorPartition I z ξ / exteriorPartition I x ξ)
    (hroot : ∀ J : PinningData (Option O) C, J.DegreeBound Δ →
      Fintype.card (Option O) < Fintype.card (Vertex U S O) →
      ∀ a b : C, ∃ L : ℂ → ℂ,
        L x = 0 ∧ DifferentiableOn ℂ L (Metric.ball x ε) ∧
        (∀ z ∈ Metric.ball x ε, Complex.exp (L z) =
          (pinningProductPartition (optionChildData J a) z /
            pinningProductPartition (optionChildData J a) x) /
          (pinningProductPartition (optionChildData J b) z /
            pinningProductPartition (optionChildData J b) x)) ∧
        ∀ z ∈ Metric.ball x ε, ‖L z‖ ≤ α) :
    ∀ z ∈ Metric.ball x ε, ∀ ξ ξ' : S → C,
      ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ' := by
  have hstep (ξ : S → C) (s : S) (a : C) :
      ∀ z ∈ Metric.ball x ε, ‖h (Function.update ξ s a) z - h ξ z‖ ≤ α := by
    obtain ⟨L, hLzero, hLdiff, hLexp, hLbound⟩ :=
      hroot (unpinnedExteriorData I ξ s) (unpinnedExterior_degreeBound I hdegree ξ s)
        (unpinnedExterior_card_lt (U := U) (O := O) s) a (ξ s)
    have hEq : Set.EqOn (fun z => h (Function.update ξ s a) z - h ξ z) L (Metric.ball x ε) := by
      apply logs_eq_on_ball_of_exp_eq hε _ L ((hdiff _).sub (hdiff ξ)) hLdiff
      · intro z hz
        change Complex.exp (h (Function.update ξ s a) z - h ξ z) = Complex.exp (L z)
        rw [Complex.exp_sub, hexp _ z hz, hexp _ z hz, hLexp z hz]
        simp only [unpinnedExterior_child_partition I hsep, Function.update_eq_self]
      · change h (Function.update ξ s a) x - h ξ x = L x
        rw [hzero, hzero, sub_self, hLzero]
    intro z hz
    have heqz : h (Function.update ξ s a) z - h ξ z = L z := hEq hz
    rw [heqz]
    exact hLbound z hz
  intro z hz ξ ξ'
  exact norm_sub_le_ham_of_coordinates (fun η => h η z) (fun η s a => hstep η s a z hz) ξ ξ'

end
end CI2ZF.Potts.Separator
