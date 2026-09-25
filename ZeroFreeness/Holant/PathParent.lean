import ZeroFreeness.Holant.Parent
import ZeroFreeness.Holant.Paths

/-!
# Parent nonvanishing on an activity path

The nonvanishing and response parts of strong induction meet here.  The
child response logarithm is constructed from actual nonzero analytic child
partitions; its size is then supplied by `ResponseBound`.  Empty instances
and structurally zero one-children are handled separately by their exact
partition identities.
-/

namespace ZeroFreeness.Holant

open scoped BigOperators
open Set Metric

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq E]

theorem childCoefficient_le_growthBound (F : Finset Signature) (H : NormalizedInstance V E)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (e : E)
    (htwo : (Finset.univ.filter (H.incidence e)).card = 2) :
    childCoefficient H.incidence (realValues H.signature) e ≤ (residualGrowthBound F) ^ 2 := by
  have hle : childCoefficient H.incidence (realValues H.signature) e ≤
      ∏ v, if H.incidence e v then residualGrowthBound F else 1 := by
    apply Finset.prod_le_prod
    · intro v _
      by_cases hv : H.incidence e v
      · simpa [realValues, hv] using (H.signature v).nonneg 1
      · simp [hv]
    · intro v _
      by_cases hv : H.incidence e v
      · simpa [realValues, hv] using residual_first_le_growthBound F (hF v)
      · simp [hv]
  have hprod : (∏ v, if H.incidence e v then residualGrowthBound F else 1) =
      (residualGrowthBound F) ^ 2 := by
    rw [← Finset.prod_filter]
    simp [htwo]
  exact hle.trans_eq hprod

namespace NormalizedInstance

/-- Actual nonzero child paths admit an analytic response logarithm
normalized at the real base, without a global principal-branch assumption. -/
theorem exists_response_log (H : NormalizedInstance V E) (e : E) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) {R ε : ℝ} (p : ActivityPath H.edges R ε)
    (hzero : ∀ t ∈ ball 0 p.radius, (H.zeroChild e).toInstance.complexPartition (p.activity t) ≠ 0)
    (hone : ∀ t ∈ ball 0 p.radius, (H.oneChild e he hs).toInstance.complexPartition (p.activity t) ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball 0 p.radius) ∧ L 0 = 0 ∧
      ∀ t ∈ ball 0 p.radius, Complex.exp (L t) =
        ((H.oneChild e he hs).toInstance.complexPartition (p.activity t) /
          ((H.oneChild e he hs).toInstance.realPartition p.base : ℂ)) /
        ((H.zeroChild e).toInstance.complexPartition (p.activity t) /
          ((H.zeroChild e).toInstance.realPartition p.base : ℂ)) := by
  let pc := p.restrict (Finset.erase_subset e H.edges)
  have hD0 := pc.instance_differentiable (H.zeroChild e).toInstance
  have hD1 := pc.instance_differentiable (H.oneChild e he hs).toInstance
  have hbase0 := pc.instance_at_zero (H.zeroChild e).toInstance
  have hbase1 := pc.instance_at_zero (H.oneChild e he hs).toInstance
  change (H.zeroChild e).toInstance.complexPartition (p.activity 0) =
    ((H.zeroChild e).toInstance.realPartition p.base : ℂ) at hbase0
  change (H.oneChild e he hs).toInstance.complexPartition (p.activity 0) =
    ((H.oneChild e he hs).toInstance.realPartition p.base : ℂ) at hbase1
  obtain ⟨L, hL, hL0, hLexp⟩ := exists_child_response_log
    (fun t => (H.oneChild e he hs).toInstance.complexPartition (p.activity t))
    (fun t => (H.zeroChild e).toInstance.complexPartition (p.activity t))
    p.radius_pos hD1 hD0 hone hzero
  refine ⟨L, hL, hL0, fun t ht => ?_⟩
  simpa only [hbase0, hbase1] using hLexp t ht

/-- The surviving-edge parent step, instantiated with actual residual
signatures and the response logarithm on the activity path. -/
theorem path_ne_zero_of_child_response (H : NormalizedInstance V E)
    (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (e : E) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (htwo : (Finset.univ.filter (H.incidence e)).card = 2)
    {R ε α : ℝ} (p : ActivityPath H.edges R ε) (hα : α ≤ 1 / 4)
    (hsmall : (residualGrowthBound F) ^ 2 * ε * (4 / 3) < 1)
    (hzero : ∀ t ∈ ball 0 p.radius, (H.zeroChild e).toInstance.complexPartition (p.activity t) ≠ 0)
    (hone : ∀ t ∈ ball 0 p.radius, (H.oneChild e he hs).toInstance.complexPartition (p.activity t) ≠ 0)
    (hresponse : ResponseBound H e he hs p α) :
    ∀ t ∈ ball 0 p.radius, H.toInstance.complexPartition (p.activity t) ≠ 0 := by
  obtain ⟨L, hL, hL0, hLexp⟩ := H.exists_response_log e he hs p hzero hone
  have hnorm := hresponse L hL hL0 hLexp
  have hcoef := childCoefficient_le_growthBound F H hF e htwo
  intro t ht
  have hsmall' : childCoefficient H.incidence (realValues H.signature) e *
      ‖p.activity t e - (p.base e : ℂ)‖ * (4 / 3) < 1 := by
    have hle := mul_le_mul hcoef (p.near t ht e he).le
      (norm_nonneg _) (sq_nonneg (residualGrowthBound F))
    exact (mul_le_mul_of_nonneg_right hle (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans_lt hsmall
  apply partition_ne_zero_of_child_response H.incidence H.edges
    (realValues H.signature) p.base (p.activity t) e he
    (fun v k => (H.signature v).nonneg k) H.normalized hs
    (fun a ha => (p.realBox a ha).1)
  · intro v k hv _
    exact (H.signature v).first_shift_le (H.normalized v) (hs v hv) k
  · have h := hzero t ht
    rw [H.zeroChild_complexPartition] at h
    exact h
  · exact (hnorm t ht).trans hα
  · have h := hLexp t ht
    rw [H.oneChild_complexPartition, H.zeroChild_complexPartition,
      H.oneChild_realPartition, H.zeroChild_realPartition] at h
    have hcv : complexValues H.signature =
        fun v k => (realValues H.signature v k : ℂ) := rfl
    rw [hcv, normalizedChildSignature_ofReal] at h
    exact h
  · exact hsmall'

/-- Complete parent step for simultaneous nonvanishing/response induction.
The statement includes empty edge sets and structurally dead one-children. -/
theorem path_ne_zero_of_children (H : NormalizedInstance V E)
    (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (htwo : ∀ e ∈ H.edges, (Finset.univ.filter (H.incidence e)).card = 2)
    {R ε α : ℝ} (p : ActivityPath H.edges R ε) (hα : α ≤ 1 / 4)
    (hsmall : (residualGrowthBound F) ^ 2 * ε * (4 / 3) < 1)
    (hzero : ∀ e, ∀ _he : e ∈ H.edges, ∀ t ∈ ball 0 p.radius,
      (H.zeroChild e).toInstance.complexPartition (p.activity t) ≠ 0)
    (hone : ∀ e, ∀ he : e ∈ H.edges, ∀ hs : H.OneSurvives e, ∀ t ∈ ball 0 p.radius,
      (H.oneChild e he hs).toInstance.complexPartition (p.activity t) ≠ 0)
    (hresponse : ∀ e, ∀ he : e ∈ H.edges, ∀ hs : H.OneSurvives e, ResponseBound H e he hs p α) :
    ∀ t ∈ ball 0 p.radius, H.toInstance.complexPartition (p.activity t) ≠ 0 := by
  by_cases hempty : H.edges = ∅
  · intro t _ht
    simp [Instance.complexPartition, hempty, complexValues, H.normalized]
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  by_cases hs : H.OneSurvives e
  · exact H.path_ne_zero_of_child_response F hF e he hs (htwo e he) p hα hsmall
      (hzero e he) (hone e he hs) (hresponse e he hs)
  · intro t ht
    rw [H.complexPartition_dead_edge e he hs]
    exact hzero e he t ht

end NormalizedInstance
end
end ZeroFreeness.Holant
