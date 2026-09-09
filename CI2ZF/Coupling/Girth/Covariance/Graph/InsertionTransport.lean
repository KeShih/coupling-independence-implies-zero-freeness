import CI2ZF.Coupling.Girth.Covariance.Graph.TwoLayer
import CI2ZF.Coupling.Girth.Covariance.Insertion.ActualEstimates

/-! Exact transport between the root-deleted Gibbs law and its two-layer
insertion disintegration. This identifies both the first-layer marginals
and the insertion normalizer before any covariance estimate is used. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphTwoLayer
variable (I : PinningData (Option V) C)

theorem girth (hg : 5 ≤ I.graph.egirth) : 5 ≤ (data I).graph.egirth := by
  let e : Vertex I ↪ Option V :=
    ⟨fun v => some (value I v), fun u v h => (splitEquiv I).symm.injective (Option.some.inj h)⟩
  exact hg.trans (SimpleGraph.Embedding.comap e I.graph).isContained.egirth_le

abbrev Configuration := (Second I → C) × ((First I → C) × (Outside I → C))

def configurationEquiv : (V → C) ≃ Configuration I :=
  (relabelColouring (splitEquiv I)).trans Separator.coloringEquiv

theorem configuration_first (σ : V → C) (u : First I) :
    (configurationEquiv I σ).2.1 u = GraphResponseRoot.coordinate I u σ := rfl

variable (x : ℝ) (hx : 0 < x) (c₀ : C)

def model : InsertionModel (Second I → C) (First I) (Outside I → C) C :=
  InsertionGraph.model (data I) x hx c₀ ((data I).partition_pos_of_parameter_pos hx)

theorem model_expectation (hg : 5 ≤ I.graph.egirth) (f : Configuration I → ℝ) :
    expectReal (model I x hx c₀).law f =
      expectReal (GraphResponseRoot.deletedLaw I x hx) (fun σ => f (configurationEquiv I σ)) := by
  rw [model, ← InsertionGraph.law_eq_model (data I) x hx (independent I hg) (separates I),
    InsertionGraph.law, CI2ZF.expectReal_mapLaw]
  erw [gibbs_relabel (optionMiddleData I) (splitEquiv I) x hx.le
    ((optionMiddleData I).partition_pos_of_parameter_pos hx)
    ((data I).partition_pos_of_parameter_pos hx), CI2ZF.expectReal_mapLaw]
  rfl

theorem model_coordinate_mean (u : First I) (c : C) :
    expectReal (model I x hx c₀).law (fun σ => colourIndicator c (σ.2.1 u)) =
      (model I x hx c₀).p u c := by
  rw [InsertionModel.law, expectReal_kernelJoint]
  have he (ξ : Second I → C) : expectReal ((model I x hx c₀).conditionalLaw ξ)
      (fun τ => colourIndicator c (τ.1 u)) = (model I x hx c₀).pi u c ξ := by
    rw [InsertionModel.conditionalLaw, expectReal_kernelJoint]
    simp only [expectReal_const]
    rw [CI2ZF.expectReal_product_coordinate, expect_colourIndicator]
    rfl
  simp_rw [he]
  rfl

theorem model_marginal (hg : 5 ≤ I.graph.egirth) (u : First I) (c : C) :
    (model I x hx c₀).p u c =
      (coordinateMarginal (GraphResponseRoot.deletedLaw I x hx) (GraphResponseRoot.coordinate I u)).w c := by
  rw [← model_coordinate_mean, model_expectation I x hx c₀ hg]
  exact coordinateIndicator_mean _ _ _

theorem model_F_mean (s : ℝ) (c : C) :
    expectReal (model I x hx c₀).law (fun σ => (model I x hx c₀).F s c σ.2.1) =
      (model I x hx c₀).T s c := by
  rw [InsertionModel.law, expectReal_kernelJoint]
  have he (ξ : Second I → C) : expectReal ((model I x hx c₀).conditionalLaw ξ)
      (fun τ => (model I x hx c₀).F s c τ.1) = (model I x hx c₀).Y s c ξ := by
    rw [InsertionModel.conditionalLaw, expectReal_kernelJoint]
    simp only [expectReal_const]
    exact InsertionModel.expect_F _ _ _ _
  simp_rw [he]
  rfl

theorem model_normalizer (hg : 5 ≤ I.graph.egirth) (s : ℝ) (c : C) :
    (model I x hx c₀).T s c =
      RootInsertion.normalizer (GraphResponseRoot.deletedLaw I x hx) (GraphResponseRoot.coordinate I) s c := by
  rw [← model_F_mean, model_expectation I x hx c₀ hg]
  rfl

theorem model_Q (hg : 5 ≤ I.graph.egirth) (s : ℝ) (c : C) :
    (model I x hx c₀).Q s c = ∏ u, (1 - s *
      (coordinateMarginal (GraphResponseRoot.deletedLaw I x hx) (GraphResponseRoot.coordinate I u)).w c) := by
  unfold InsertionModel.Q
  simp_rw [model_marginal I x hx c₀ hg]

theorem model_residual (hg : 5 ≤ I.graph.egirth) (s : ℝ) (c : C) (σ : V → C) :
    (model I x hx c₀).residual s c (configurationEquiv I σ).2.1 =
      RootInsertion.residual (GraphResponseRoot.deletedLaw I x hx) (GraphResponseRoot.coordinate I) s c σ := by
  unfold InsertionModel.residual InsertionModel.alpha RootInsertion.residual RootInsertion.alpha
  rw [model_normalizer I x hx c₀ hg]
  simp_rw [model_marginal I x hx c₀ hg]
  rfl

theorem defect_eq_model (hg : 5 ≤ I.graph.egirth) (s : ℝ) (f : (V → C) → ℝ) (c : C) :
    RootInsertion.defect (GraphResponseRoot.deletedLaw I x hx) (GraphResponseRoot.coordinate I) s f c =
      covariance (model I x hx c₀).law (fun σ => f ((configurationEquiv I).symm σ))
        (fun σ => (model I x hx c₀).residual s c σ.2.1) := by
  unfold RootInsertion.defect
  simp only [covariance_eq_moment, model_expectation I x hx c₀ hg,
    Equiv.symm_apply_apply, model_residual I x hx c₀ hg]

theorem actual_estimates (hg : 5 ≤ I.graph.egirth) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ))
    (hpq : p.q = (Fintype.card C : ℝ)) (hδ1 : p.δ ≤ 1) (ht : girthFiveThreshold p.δ ≤ Δ) :
    (model I x hx c₀).CovarianceEstimates (1-x) p :=
  InsertionGraph.actual_estimates (data I) x hx (independent I hg) (separates I) c₀
    ((data I).partition_pos_of_parameter_pos hx) hx1 (degreeBound I hd) (first_card_le I hd)
    (owner I) (owner_unique I hg) p hpΔ hpq hδ1 ht (girth I hg)

include c₀ in
theorem actual_log_quotient (hg : 5 ≤ I.graph.egirth) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ))
    (hpq : p.q = (Fintype.card C : ℝ)) (hδ1 : p.δ ≤ 1) (ht : girthFiveThreshold p.δ ≤ Δ) (c : C) :
    |Real.log (RootInsertion.normalizer (GraphResponseRoot.deletedLaw I x hx) (GraphResponseRoot.coordinate I) (1-x) c /
      (∏ u, (1 - (1-x) * (coordinateMarginal (GraphResponseRoot.deletedLaw I x hx)
        (GraphResponseRoot.coordinate I u)).w c)))| ≤ p.E := by
  have hh := (actual_estimates I x hx c₀ hg hx1 hd p hpΔ hpq hδ1 ht).log_quotient c
  rwa [model_normalizer I x hx c₀ hg, model_Q I x hx c₀ hg] at hh

end GraphTwoLayer
end
end CI2ZF.Appendix.Girth
