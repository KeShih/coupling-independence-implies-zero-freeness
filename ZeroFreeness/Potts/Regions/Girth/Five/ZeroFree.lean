import ZeroFreeness.Potts.Regions.Girth.Five.Transfer
import ZeroFreeness.Coupling.Girth.Five.Response

/-! The fixed-girth Potts conclusion. The source estimates, finite
response induction, endpoint passage, and complex transfer are proved
internally, as is CLMM Lemma 5.13 (`sphere_to_coupling`); no literature
parameter remains. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI PottsCI.FinDist ZeroFreeness.Potts ZeroFreeness.Potts.Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

/-- One coupling constant works for all sizes, pinnings, and activities
in the closed physical interval on residual graphs of girth at least five. -/
theorem girth_five_coupling
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hThreshold : girthFiveCIThreshold δ ≤ Δ)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    ∃ cost : ℝ, 0 ≤ cost ∧ ∀ (x : ℝ) (hx : 0 ≤ x), x ≤ 1 →
      ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
        I.DegreeBound Δ → 5 ≤ I.graph.egirth → ∀ (a b : C)
        (ha : 0 < (optionChildData I a).partition x)
        (hb : 0 < (optionChildData I b).partition x),
        W ham ((optionChildData I a).gibbs x hx ha)
          ((optionChildData I b).gibbs x hx hb) ≤ cost := by
  let p := actualCovarianceScale hδ hδ1 (girthFiveCIThreshold_gap hThreshold) hq
  exact closed_coupling_from_weighted_source Δ 5
    (girthFiveCIThreshold_degree_three hδ hδ1 hThreshold) (covarianceChi_gt_one hδ)
    (p.responseM_pos (girthFiveCIThreshold_covariance hThreshold)).le
    (actual_uniform_weighted_source (C := C) hδ hδ1 hThreshold hq)

/-- A single positive complex radius is uniform over all residual
graphs, graph sizes, pinnings, and base activities in `[0,1]`. -/
theorem girth_five_zero_free
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hThreshold : girthFiveCIThreshold δ ≤ Δ)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      5 ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0 := by
  let p := actualCovarianceScale hδ hδ1 (girthFiveCIThreshold_gap hThreshold) hq
  have hcolours := girthFiveCIThreshold_colour_slack hδ hδ1 hThreshold hq
  exact large_girth_zero_free_of_weighted_source Δ 5
    (girthFiveCIThreshold_degree_three hδ hδ1 hThreshold) (by omega)
    (covarianceChi_gt_one hδ)
    (p.responseM_pos (girthFiveCIThreshold_covariance hThreshold)).le
    (actual_uniform_weighted_source (C := C) hδ hδ1 hThreshold hq)

/-- Original-graph semantics, including arbitrary improper pinnings:
the normalized partition is zero-free, and the full polynomial has
exactly its forced pinned-conflict zero and multiplicity. -/
theorem girth_five_original_zero_free
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hThreshold : girthFiveCIThreshold δ ≤ Δ)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    ∃ eps > 0, UniformGirthPottsZeroFree.{u,v} C Δ 5 eps := by
  obtain ⟨eps, heps, hnz⟩ := girth_five_zero_free hδ hδ1 hThreshold hq
  exact ⟨eps, heps, uniformGirthPottsZeroFree_of_residual heps hnz⟩

end
end ZeroFreeness.Appendix.Girth
