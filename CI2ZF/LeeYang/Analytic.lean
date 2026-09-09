import CI2ZF.LeeYang.GeometryFields
import CI2ZF.Potts.Transfer.InductionState
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! One complex parameter parametrizes every bounded direction in the full
vertex-colour field space. The radius in the transfer theorem is uniform
over these directions, so it gives a multivariable polydisc. -/
namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]

def fieldCurve (I : PinningData V C) (d : V → C → ℂ) (z : ℂ) : ℂ :=
  fieldPartition I (fieldLine d z)

@[simp] theorem fieldCurve_zero (I : PinningData V C) (d : V → C → ℂ) :
    fieldCurve I d 0 = (I.partition 0 : ℂ) := by
  simp [fieldCurve]

theorem fieldCurve_differentiable (I : PinningData V C) (d : V → C → ℂ) :
    Differentiable ℂ (fieldCurve I d) := by
  unfold fieldCurve fieldPartition fieldWeight
  apply Differentiable.fun_sum
  intro σ _
  split_ifs
  · apply Differentiable.fun_finsetProd
    intro v _
    exact (differentiable_const (1 : ℂ)).add (differentiable_id.mul_const (d v (σ v)))
  · exact differentiable_const _

def CurveNonzeroOn (I : PinningData V C) (d : V → C → ℂ) (r : ℝ) : Prop :=
  ∀ z ∈ Metric.ball 0 r, fieldCurve I d z ≠ 0

def CurveRootResponses (I : PinningData (Option V) C)
    (d : Option V → C → ℂ) (r α : ℝ) : Prop :=
  ∀ a b : C, HasSmallResponseLog
    (fieldCurve (optionChildData I a) (fieldPull some d))
    (fieldCurve (optionChildData I b) (fieldPull some d)) 0 r α

theorem exists_curve_response_log (I : PinningData V C) (d : V → C → ℂ)
    {r : ℝ} (hr : 0 < r) (hnz : CurveNonzeroOn I d r) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ DifferentiableOn ℂ L (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball 0 r, Complex.exp (L z) = fieldCurve I d z / fieldCurve I d 0 := by
  obtain ⟨L, h0, hd, he⟩ := exists_normalized_log_on_ball (fieldCurve I d) hr
    (fieldCurve_differentiable I d).differentiableOn hnz
  exact ⟨L, h0, fun z hz => (hd z hz).differentiableAt.differentiableWithinAt, he⟩

theorem fieldCurve_zero_ne_zero [Nonempty C] (I : PinningData V C)
    (d : V → C → ℂ) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) : fieldCurve I d 0 ≠ 0 := by
  simpa [fieldCurve] using fieldPartition_one_ne_zero I hd hq

theorem fieldPartition_of_isEmpty [IsEmpty V] (I : PinningData V C)
    (ℓ : V → C → ℂ) : fieldPartition I ℓ = 1 := by
  have hadm (σ : V → C) : I.HardAdmissible σ :=
    ⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  simp [fieldPartition, fieldWeight, hadm]

theorem curveNonzeroOn_of_isEmpty [IsEmpty V] (I : PinningData V C)
    (d : V → C → ℂ) (r : ℝ) : CurveNonzeroOn I d r := by
  intro z _
  simp [fieldCurve, fieldPartition_of_isEmpty]

end
end CI2ZF.LeeYang
