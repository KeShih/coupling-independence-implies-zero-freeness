import CI2ZF.Potts.Transfer.ExteriorAnalyticResponses
import CI2ZF.Analysis.AnalyticComplexAverage
import CI2ZF.Potts.Transfer.LocalResponseLog

/-! The positive separator comparison for two actual instances with a
common exterior. The response identities are derived from the finite
partition sums, and the analytic logarithm is constructed on the disk. -/
namespace CI2ZF.Potts.Separator
open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C] [Nonempty C]

omit [Nonempty C] in
theorem exteriorPartition_eq_of_data_eq
    (I J : PinningData (Vertex U S O) C) (hi : Separates I) (hj : Separates J)
    (he : ∀ ξ, exteriorData I ξ = exteriorData J ξ) (ξ : S → C) (z : ℂ) :
    exteriorPartition I z ξ = exteriorPartition J z ξ := by
  rw [exteriorPartition_eq_pinningProductPartition I hi,
    exteriorPartition_eq_pinningProductPartition J hj, he]

theorem positive_response_eq_exp_average
    (I : PinningData (Vertex U S O) C) (hi : Separates I)
    {x : ℝ} (hx : 0 < x) (z : ℂ) (h eta : (S → C) → ℂ)
    (he : ∀ ξ, Complex.exp (h ξ) = exteriorPartition I z ξ / exteriorPartition I (x : ℂ) ξ)
    (hd : ∀ ξ, Complex.exp (eta ξ) = insidePartition I z ξ / insidePartition I (x : ℂ) ξ) :
    partition I z / partition I (x : ℂ) =
      expectComplex (shellMarginal I x hx.le (I.partition_pos_of_parameter_pos hx))
        (fun ξ => Complex.exp (h ξ + eta ξ)) := by
  rw [response_eq_shell_average I hi x hx z]
  unfold expectComplex
  apply Finset.sum_congr rfl
  intro ξ _
  dsimp only
  rw [Complex.exp_add, he, hd]
  ring

/-- A normalized analytic logarithm of the actual separator response
quotient, with the quantitative Wasserstein estimate and nonvanishing of
both partitions. No analytic logarithm of the desired quotient is assumed. -/
theorem exists_positive_separator_quotient_log
    (I J : PinningData (Vertex U S O) C) (hi : Separates I) (hj : Separates J)
    (hcommon : ∀ ξ, exteriorData I ξ = exteriorData J ξ)
    {x : ℝ} (hx : 0 < x) {r A delta : ℝ} (hA : 0 ≤ A)
    (hd : delta ∈ Set.Icc 0 (1 / 8 : ℝ))
    (h eta theta : (S → C) → ℂ → ℂ)
    (hh : ∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball (x : ℂ) r))
    (heta : ∀ ξ, DifferentiableOn ℂ (eta ξ) (Metric.ball (x : ℂ) r))
    (htheta : ∀ ξ, DifferentiableOn ℂ (theta ξ) (Metric.ball (x : ℂ) r))
    (hh0 : ∀ ξ, h ξ x = 0) (heta0 : ∀ ξ, eta ξ x = 0) (htheta0 : ∀ ξ, theta ξ x = 0)
    (hexp : ∀ z ∈ Metric.ball (x : ℂ) r, ∀ ξ, Complex.exp (h ξ z) =
      exteriorPartition I z ξ / exteriorPartition I (x : ℂ) ξ)
    (hetaexp : ∀ z ∈ Metric.ball (x : ℂ) r, ∀ ξ, Complex.exp (eta ξ z) =
      insidePartition I z ξ / insidePartition I (x : ℂ) ξ)
    (hthetaexp : ∀ z ∈ Metric.ball (x : ℂ) r, ∀ ξ, Complex.exp (theta ξ z) =
      insidePartition J z ξ / insidePartition J (x : ℂ) ξ)
    (hlip : ∀ z ∈ Metric.ball (x : ℂ) r, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ A * ham ξ ξ')
    (hosc : ∀ z ∈ Metric.ball (x : ℂ) r, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ (1 / 8 : ℝ))
    (hbeta : ∀ z ∈ Metric.ball (x : ℂ) r, ∀ ξ, ‖eta ξ z‖ ≤ delta)
    (hbtheta : ∀ z ∈ Metric.ball (x : ℂ) r, ∀ ξ, ‖theta ξ z‖ ≤ delta) :
    let μ := shellMarginal I x hx.le (I.partition_pos_of_parameter_pos hx)
    let ν := shellMarginal J x hx.le (J.partition_pos_of_parameter_pos hx)
    (∀ z ∈ Metric.ball (x : ℂ) r, partition I z ≠ 0 ∧ partition J z ≠ 0) ∧
    ∃ L : ℂ → ℂ, L x = 0 ∧ DifferentiableOn ℂ L (Metric.ball (x : ℂ) r) ∧
      (∀ z ∈ Metric.ball (x : ℂ) r, Complex.exp (L z) =
        (partition I z / partition I (x : ℂ)) / (partition J z / partition J (x : ℂ))) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, ‖L z‖ ≤ 2 * A * W ham μ ν + 4 * delta := by
  dsimp only
  let μ := shellMarginal I x hx.le (I.partition_pos_of_parameter_pos hx)
  let ν := shellMarginal J x hx.le (J.partition_pos_of_parameter_pos hx)
  let anchor : S → C := fun _ => Classical.choice (inferInstance : Nonempty C)
  have heJ (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) r) (ξ : S → C) :
      Complex.exp (h ξ z) = exteriorPartition J z ξ / exteriorPartition J (x : ℂ) ξ := by
    rw [hexp z hz, exteriorPartition_eq_of_data_eq I J hi hj hcommon,
      exteriorPartition_eq_of_data_eq I J hi hj hcommon]
  have hri (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) r) :=
    positive_response_eq_exp_average I hi hx z _ _ (hexp z hz) (hetaexp z hz)
  have hrj (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) r) :=
    positive_response_eq_exp_average J hj hx z _ _ (heJ z hz) (hthetaexp z hz)
  have hp (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) r) :=
    paper_complex_average_with_anchor μ ν (fun ξ => h ξ z) (fun ξ => eta ξ z)
      (fun ξ => theta ξ z) ham hA hd (hlip z hz) (hosc z hz) (hbeta z hz) (hbtheta z hz) anchor
  refine ⟨?_, analyticCenteredLog μ ν h eta theta anchor, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hi' := (hp z hz).1
    have hj' := (hp z hz).2.1
    rw [← hri z hz] at hi'
    rw [← hrj z hz] at hj'
    exact ⟨fun hz0 => hi' (by rw [hz0, zero_div]), fun hz0 => hj' (by rw [hz0, zero_div])⟩
  · exact analyticCenteredLog_zero μ ν h eta theta anchor x hh0 heta0 htheta0
  · exact analyticCenteredLog_differentiable μ ν h eta theta anchor _ hh heta htheta hosc
      (fun z hz ξ => (hbeta z hz ξ).trans hd.2) (fun z hz ξ => (hbtheta z hz ξ).trans hd.2)
  · intro z hz
    rw [hri z hz, hrj z hz]
    exact (hp z hz).2.2.1
  · intro z hz
    exact (hp z hz).2.2.2

end
end CI2ZF.Potts.Separator
