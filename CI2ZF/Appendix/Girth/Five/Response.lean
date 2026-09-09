import CI2ZF.Appendix.Girth.Covariance.Response.Induction
import CI2ZF.Appendix.Girth.Covariance.Response.UniformSourceAdapter

/-! The complete uniform weighted source theorem at girth five. All
response, insertion, spectral and conditioning estimates are proved
internally; this file has no literature premise. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

theorem actual_uniform_child_oscillation (p : CovarianceScale) {Δ : ℕ}
    (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ))
    (hδ1 : p.δ ≤ 1) (ht : girthFiveThreshold p.δ ≤ Δ)
    (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) (x : ℝ) (hx1 : x < 1) :
    UniformChildOscillation.{u,v} C Δ 5 x (covarianceChi p.δ) p.responseM := by
  intro V _ _ I hd hg hx F a b
  have hχ : 0 ≤ covarianceChi p.δ := (Real.exp_pos _).le
  have hV := p.responseV_nonneg hlarge
  have hglobal := actual_response_bounds C p hpΔ hpq hδ1 ht hlarge (Fintype.card V)
  have hmiddle : 5 ≤ (optionMiddleData I).graph.egirth := by
    let e : V ↪ Option V := ⟨Option.some, Option.some_injective V⟩
    exact hg.trans (SimpleGraph.Embedding.comap e I.graph).isContained.egirth_le
  have hinf (u : GraphResponseRoot.Neighbour I) (c : C) :
      |GraphResponseRoot.deletedScore I x hx p F u c| ≤
        Real.sqrt p.B * covarianceChi p.δ * p.responseV * F.weight none := by
    have h := (hglobal V (optionMiddleData I) le_rfl (GraphTwoLayer.middle_degreeBound I hd)
      hmiddle x hx hx1 F.deleted u.val).2 c
    have hw : F.deleted.weight u.val ≤ covarianceChi p.δ * F.weight none :=
      F.neighbour_bound none (some u.val) (GraphTwoLayer.first_adj I u)
    calc
      _ ≤ Real.sqrt p.B * p.responseV * F.deleted.weight u.val := h
      _ ≤ Real.sqrt p.B * p.responseV * (covarianceChi p.δ * F.weight none) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg (Real.sqrt_nonneg _) hV)
      _ = _ := by ring
  let c₀ : C := Classical.arbitrary C
  have hvar := GraphTwoLayer.shellVariance_of_response I x hx hglobal c₀ le_rfl hd hg hx1 hχ F
  apply GraphResponseRoot.option_child_oscillation I x hx c₀ p F hg hx1.le hd hpΔ hpq hδ1 ht hlarge hinf
    (c := a) (d := b)
  simpa only [WeightedSource.twoLayer, WeightedSource.shellSource, GraphTwoLayer.data, hpΔ] using hvar

/-- Weighted additive response, uniformly over all graph sizes, all
residual boundary counts, all admissible weights and the full positive
physical interval. The degree threshold is explicit and delta-only. -/
theorem actual_uniform_weighted_source {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hThreshold : girthFiveCIThreshold δ ≤ Δ)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    let p := actualCovarianceScale hδ hδ1 (girthFiveCIThreshold_gap hThreshold) hq
    ∀ (x : ℝ), 0 < x → x ≤ 1 →
      UniformWeightedSource.{u,v} C Δ 5 x (covarianceChi δ) p.responseM := by
  let p := actualCovarianceScale hδ hδ1 (girthFiveCIThreshold_gap hThreshold) hq
  have hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ := girthFiveCIThreshold_covariance hThreshold
  apply uniformWeightedSource_include_one (p.responseM_pos hlarge).le
  intro x _hx hx1
  exact uniformWeightedSource_of_child_oscillation
    (actual_uniform_child_oscillation (C := C) p rfl rfl hδ1 (girthFiveCIThreshold_gap hThreshold) hlarge x hx1)

end
end CI2ZF.Appendix.Girth
