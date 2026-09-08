import CI2ZF.PottsModel
import CI2ZF.AnalyticLog
import CI2ZF.LocalStability
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Analytic consequences of the normalized Potts polynomial

These results connect the analytic infrastructure to genuine graph/pinning
instances. The root multiplicity statement uses hard feasibility, not CI.
The logarithm statement assumes a nonzero disk explicitly, as required when
it is used for a smaller instance in the shell induction.
-/

namespace CI2ZF.Potts

open PottsCI Metric

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- Hard feasibility makes the normalized pinned polynomial nonzero as a
polynomial, including for improper pinnings. -/
theorem normalizedPolynomial_ne_zero [Nonempty C] (tau : PartialColouring V C)
    (G : SimpleGraph V) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C) : normalizedPolynomial tau G ≠ 0 := by
  intro heq
  have hnz := normalizedPartition_zero_ne_zero tau G hdegree hcolours
  simp [normalizedPartition, heq] at hnz

/-- The forced zero at zero has exactly the number of monochromatic
pinned-only edges as its multiplicity. This is valid before proving any
uniform complex zero-free neighborhood. -/
theorem fullPolynomial_rootMultiplicity_zero [Nonempty C] (tau : PartialColouring V C)
    (G : SimpleGraph V) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G := by
  have hp := normalizedPolynomial_ne_zero tau G hdegree hcolours
  have hnz : ¬ (normalizedPolynomial tau G).IsRoot 0 :=
    normalizedPartition_zero_ne_zero tau G hdegree hcolours
  have h := Polynomial.rootMultiplicity_mul_X_sub_C_pow
    (a := (0 : ℂ)) (n := tau.pinnedConflictCount G) hp
  rw [fullPolynomial_eq]
  simpa [Polynomial.rootMultiplicity_eq_zero hnz, mul_comm] using h

/-- The ordinary pinned partition has no additional zeros away from zero
whenever the normalized partition is nonzero. -/
theorem fullPartition_ne_zero_of_normalized (tau : PartialColouring V C)
    (G : SimpleGraph V) {z : ℂ} (hz : z ≠ 0)
    (hZ : normalizedPartition tau G z ≠ 0) : fullPartition tau G z ≠ 0 := by
  rw [fullPartition_eq]
  exact mul_ne_zero (pow_ne_zero _ hz) hZ

/-- The induction's nonzero-disk hypothesis supplies a normalized analytic
logarithm of the actual pinned partition response. -/
theorem normalizedPartition_has_log_on_ball (tau : PartialColouring V C)
    (G : SimpleGraph V) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hnz : ∀ z ∈ ball c r, normalizedPartition tau G z ≠ 0) :
    ∃ L : ℂ → ℂ, L c = 0 ∧
      (∀ z ∈ ball c r, HasDerivAt L
        (deriv (normalizedPartition tau G) z / normalizedPartition tau G z) z) ∧
      ∀ z ∈ ball c r, Complex.exp (L z) =
        normalizedPartition tau G z / normalizedPartition tau G c := by
  apply exists_normalized_log_on_ball (normalizedPartition tau G) hr
  · exact (normalizedPolynomial tau G).differentiable.differentiableOn
  · exact hnz

end
end CI2ZF.Potts
