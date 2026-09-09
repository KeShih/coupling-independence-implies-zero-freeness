import CI2ZF.LeeYang.Local
import CI2ZF.AnalyticComplexAverage

/-! The field separator response is an average under the actual hard
shell law. Zero local supports are included exactly, through a
multiplicative identity that never divides by a vanishing coefficient. -/
namespace CI2ZF.LeeYang
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

/-- Exact normalized response, including every hard-defective shell. -/
theorem field_response_eq_exp_average (I : PinningData (Vertex U S O) C)
    (hi : Separates I) (hZ : 0 < I.partition 0) (ℓ : Vertex U S O → C → ℂ)
    (h eta : (S → C) → ℂ)
    (he : ∀ ξ, fieldPartition (exteriorData I ξ) oneField * Complex.exp (h ξ) =
      fieldPartition (exteriorData I ξ) (exteriorField ℓ))
    (hd : ∀ ξ, insideFieldPartition I oneField ξ * Complex.exp (eta ξ) =
      insideFieldPartition I ℓ ξ) :
    fieldPartition I ℓ / fieldPartition I oneField =
      expectComplex (shellMarginal I 0 le_rfl hZ) (fun ξ => Complex.exp (h ξ + eta ξ)) := by
  rw [fieldPartition_separator I hi, fieldPartition_one, Finset.sum_div]
  unfold expectComplex
  apply Finset.sum_congr rfl
  intro ξ _
  rw [shellMarginal_apply I hi, exteriorPartition_eq_real_partition I hi]
  rw [← hd ξ, ← he ξ, insideFieldPartition_one, fieldPartition_one]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.exp_add]
  ring_nf
  congr!

/-- Actual analytic field response comparison. The local logarithms are
constructed internally from the uniform radius, including zero support. -/
theorem field_separator_control [Nonempty C]
    (I J : PinningData (Vertex U S O) C) (hi : Separates I) (hj : Separates J)
    (hcommon : ∀ ξ, exteriorData I ξ = exteriorData J ξ)
    (hZI : 0 < I.partition 0) (hZJ : 0 < J.partition 0)
    {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B)
    {α r : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : r ≤ localFieldRadius B α)
    (d : Vertex U S O → C → ℂ) (hd : DirectionBound d)
    (h : (S → C) → ℂ → ℂ)
    (hh : ∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball 0 r)) (hh0 : ∀ ξ, h ξ 0 = 0)
    (hexp : ∀ z ∈ Metric.ball 0 r, ∀ ξ, Complex.exp (h ξ z) =
      fieldCurve (exteriorData I ξ) (fieldPull outsideEmbedding d) z /
        fieldCurve (exteriorData I ξ) (fieldPull outsideEmbedding d) 0)
    (hlip : ∀ z ∈ Metric.ball 0 r, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ')
    (hosc : ∀ z ∈ Metric.ball 0 r, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ (1 / 8 : ℝ)) :
    let μ := shellMarginal I 0 le_rfl hZI
    let ν := shellMarginal J 0 le_rfl hZJ
    (CurveNonzeroOn I d r ∧ CurveNonzeroOn J d r) ∧
      HasSmallResponseLog (fieldCurve I d) (fieldCurve J d) 0 r
        (2 * α * W ham μ ν + α / 2) := by
  dsimp only
  let μ := shellMarginal I 0 le_rfl hZI
  let ν := shellMarginal J 0 le_rfl hZJ
  let eta : (S → C) → ℂ → ℂ := fun ξ z => insideFieldLog I (fieldLine d z) ξ
  let theta : (S → C) → ℂ → ℂ := fun ξ z => insideFieldLog J (fieldLine d z) ξ
  let anchor : S → C := fun _ => Classical.choice (inferInstance : Nonempty C)
  have hdelta : α / 8 ∈ Set.Icc (0 : ℝ) (1 / 8) := by constructor <;> linarith
  have heta (ξ : S → C) : DifferentiableOn ℂ (eta ξ) (Metric.ball 0 r) :=
    insideFieldLog_curve_differentiableOn I ξ hB hα hr d hd
  have htheta (ξ : S → C) : DifferentiableOn ℂ (theta ξ) (Metric.ball 0 r) :=
    insideFieldLog_curve_differentiableOn J ξ hB hα hr d hd
  have heta0 (ξ : S → C) : eta ξ 0 = 0 := insideFieldLog_curve_zero I d ξ
  have htheta0 (ξ : S → C) : theta ξ 0 = 0 := insideFieldLog_curve_zero J d ξ
  have hbeta (z : ℂ) (hz : z ∈ Metric.ball 0 r) (ξ : S → C) : ‖eta ξ z‖ ≤ α / 8 :=
    insideFieldLog_curve_bound I ξ hB hα hr d hd hz
  have hbtheta (z : ℂ) (hz : z ∈ Metric.ball 0 r) (ξ : S → C) : ‖theta ξ z‖ ≤ α / 8 :=
    insideFieldLog_curve_bound J ξ hB hα hr d hd hz
  have heI (z : ℂ) (hz : z ∈ Metric.ball 0 r) (ξ : S → C) :
      fieldPartition (exteriorData I ξ) oneField * Complex.exp (h ξ z) =
        fieldPartition (exteriorData I ξ) (exteriorField (fieldLine d z)) := by
    have he := hexp z hz ξ
    simp only [fieldCurve, fieldLine_zero] at he
    change Complex.exp (h ξ z) =
      fieldPartition (exteriorData I ξ) (exteriorField (fieldLine d z)) /
        fieldPartition (exteriorData I ξ) oneField at he
    have hn : fieldPartition (exteriorData I ξ) oneField ≠ 0 := by
      intro hz0
      rw [hz0, div_zero] at he
      exact Complex.exp_ne_zero _ he
    rw [he]
    exact mul_div_cancel₀ _ hn
  have heJ (z : ℂ) (hz : z ∈ Metric.ball 0 r) (ξ : S → C) :
      fieldPartition (exteriorData J ξ) oneField * Complex.exp (h ξ z) =
        fieldPartition (exteriorData J ξ) (exteriorField (fieldLine d z)) := by
    simpa only [hcommon ξ] using heI z hz ξ
  have hri (z : ℂ) (hz : z ∈ Metric.ball 0 r) :
      fieldCurve I d z / fieldCurve I d 0 =
        expectComplex μ (fun ξ => Complex.exp (h ξ z + eta ξ z)) := by
    simpa only [fieldCurve, fieldLine_zero] using
      field_response_eq_exp_average I hi hZI (fieldLine d z) (fun ξ => h ξ z) (fun ξ => eta ξ z)
        (heI z hz) (fun ξ => insideFieldLog_curve_exp_mul I ξ hB hα hr d hd hz)
  have hrj (z : ℂ) (hz : z ∈ Metric.ball 0 r) :
      fieldCurve J d z / fieldCurve J d 0 =
        expectComplex ν (fun ξ => Complex.exp (h ξ z + theta ξ z)) := by
    simpa only [fieldCurve, fieldLine_zero] using
      field_response_eq_exp_average J hj hZJ (fieldLine d z) (fun ξ => h ξ z) (fun ξ => theta ξ z)
        (heJ z hz) (fun ξ => insideFieldLog_curve_exp_mul J ξ hB hα hr d hd hz)
  have hp (z : ℂ) (hz : z ∈ Metric.ball 0 r) :=
    paper_complex_average_with_anchor μ ν (fun ξ => h ξ z) (fun ξ => eta ξ z)
      (fun ξ => theta ξ z) ham hα.le hdelta (hlip z hz) (hosc z hz)
      (hbeta z hz) (hbtheta z hz) anchor
  refine ⟨⟨?_, ?_⟩, analyticCenteredLog μ ν h eta theta anchor, ?_, ?_, ?_, ?_⟩
  · intro z hz hz0
    have hn := (hp z hz).1
    rw [← hri z hz, hz0, zero_div] at hn
    exact hn rfl
  · intro z hz hz0
    have hn := (hp z hz).2.1
    rw [← hrj z hz, hz0, zero_div] at hn
    exact hn rfl
  · exact analyticCenteredLog_zero μ ν h eta theta anchor 0 hh0 heta0 htheta0
  · exact analyticCenteredLog_differentiable μ ν h eta theta anchor _ hh heta htheta hosc
      (fun z hz ξ => (hbeta z hz ξ).trans hdelta.2)
      (fun z hz ξ => (hbtheta z hz ξ).trans hdelta.2)
  · intro z hz
    rw [hri z hz, hrj z hz]
    exact (hp z hz).2.2.1
  · intro z hz
    simpa only [analyticCenteredLog, μ, ν, show 4 * (α / 8) = α / 2 by ring] using
      (hp z hz).2.2.2

/-- Direct response-log wrapper for the BFS induction. -/
theorem exists_field_separator_quotient_log [Nonempty C]
    (I J : PinningData (Vertex U S O) C) (hi : Separates I) (hj : Separates J)
    (hcommon : ∀ ξ, exteriorData I ξ = exteriorData J ξ)
    (hZI : 0 < I.partition 0) (hZJ : 0 < J.partition 0)
    {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B)
    {α r : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : r ≤ localFieldRadius B α)
    (d : Vertex U S O → C → ℂ) (hd : DirectionBound d)
    (h : (S → C) → ℂ → ℂ)
    (hh : ∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball 0 r)) (hh0 : ∀ ξ, h ξ 0 = 0)
    (hexp : ∀ z ∈ Metric.ball 0 r, ∀ ξ, Complex.exp (h ξ z) =
      fieldCurve (exteriorData I ξ) (fieldPull outsideEmbedding d) z /
        fieldCurve (exteriorData I ξ) (fieldPull outsideEmbedding d) 0)
    (hlip : ∀ z ∈ Metric.ball 0 r, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ')
    (hosc : ∀ z ∈ Metric.ball 0 r, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ (1 / 8 : ℝ)) :
    HasSmallResponseLog (fieldCurve I d) (fieldCurve J d) 0 r
      (2 * α * W ham (shellMarginal I 0 le_rfl hZI) (shellMarginal J 0 le_rfl hZJ) + α / 2) :=
  (field_separator_control I J hi hj hcommon hZI hZJ hB hα hα1 hr d hd h hh hh0 hexp hlip hosc).2

end
end CI2ZF.LeeYang
