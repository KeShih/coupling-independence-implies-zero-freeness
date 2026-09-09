import CI2ZF.Appendix.Girth.Covariance.Graph.ResponseBlock
import CI2ZF.Appendix.Girth.Covariance.Response.SeparatorSource
import CI2ZF.Appendix.Girth.Covariance.Response.Oscillation

/-! The full response step on an actual finite Potts graph. The only
inductive premises are responses in the root-deleted graph and variance
of the actual conditional full source on the second layer. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace WeightedSource
variable {I : PinningData (Option V) C} {χ : ℝ} (F : WeightedSource I χ)

def twoLayer : WeightedSource (GraphTwoLayer.data I) χ :=
  F.deleted.relabel (GraphTwoLayer.splitEquiv I)

theorem twoLayer_source (τ : GraphTwoLayer.Configuration I) :
    F.twoLayer.splitSource τ = F.deleted.observable ((GraphTwoLayer.configurationEquiv I).symm τ) := by
  obtain ⟨σ, rfl⟩ := (GraphTwoLayer.configurationEquiv I).surjective τ
  rw [Equiv.symm_apply_apply]
  change F.twoLayer.splitSource (Separator.coloringEquiv (relabelColouring (GraphTwoLayer.splitEquiv I) σ)) = _
  rw [splitSource_coloringEquiv]
  change (F.deleted.relabel (GraphTwoLayer.splitEquiv I)).observable _ = _
  rw [observable_relabel]
  congr 1
  funext v
  exact congrArg σ ((GraphTwoLayer.splitEquiv I).symm_apply_apply v)

theorem twoLayer_first_bound (u : GraphTwoLayer.First I) :
    F.twoLayer.weight (Sum.inl u) ≤ χ * F.weight none :=
  F.neighbour_bound none (some u.val) (GraphTwoLayer.first_adj I u)

theorem observable_additive : F.observable = GraphResponseRoot.additiveSource (F.term none) F.deleted.observable := by
  funext σ
  exact F.observable_option σ

variable (x : ℝ) (hx : 0 < x) (c₀ : C)

theorem actual_defect_decomposition (hg : 5 ≤ I.graph.egirth) (c : C) :
    RootInsertion.defect (GraphResponseRoot.deletedLaw I x hx) (GraphResponseRoot.coordinate I)
      (1-x) F.deleted.observable c =
    F.twoLayer.localDefect (GraphTwoLayer.model I x hx c₀) (1-x) c +
      covariance (GraphTwoLayer.model I x hx c₀).shell
        (F.twoLayer.shellSource (GraphTwoLayer.model I x hx c₀))
        ((GraphTwoLayer.model I x hx c₀).G (1-x) c) := by
  rw [GraphTwoLayer.defect_eq_model I x hx c₀ hg]
  simp_rw [← F.twoLayer_source]
  exact F.twoLayer.full_defect_decomposition _ _ _

theorem actual_local_source_bound (hg : 5 ≤ I.graph.egirth) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ))
    (hpq : p.q = (Fintype.card C : ℝ)) (hδ1 : p.δ ≤ 1) (ht : girthFiveThreshold p.δ ≤ Δ)
    (hχ : 0 ≤ χ) (c : C) :
    |F.term none c + F.twoLayer.localDefect (GraphTwoLayer.model I x hx c₀) (1-x) c| ≤
      (1 + p.ell * χ) * F.weight none := by
  apply F.twoLayer.localSource_bound _ _ p
    (GraphTwoLayer.actual_estimates I x hx c₀ hg hx1 hd p hpΔ hpq hδ1 ht)
    (by rw [hpΔ]; exact_mod_cast GraphTwoLayer.first_card_le I hd)
    (F.positive none).le hχ (F.twoLayer_first_bound) (F.term none) (F.term_bound none) c

end WeightedSource

namespace GraphResponseRoot
variable (I : PinningData (Option V) C) (x : ℝ) (hx : 0 < x) (c₀ : C)
  (p : CovarianceScale) (F : WeightedSource I (covarianceChi p.δ))

def deletedScore (u : Neighbour I) : C → ℝ :=
  instanceScore (optionMiddleData I) x hx F.deleted u.val

theorem weighted_response_recursion (hg : 5 ≤ I.graph.egirth) :
    instanceScore I x hx F none = fun c =>
      responseBlockAction (1-x) (rootLaw I x hx) (cavityMarginal I x hx) (deletedScore I x hx p F) c +
      scoreSource (1-x) (rootLaw I x hx)
        (fun d => (F.term none d + F.twoLayer.localDefect (GraphTwoLayer.model I x hx c₀) (1-x) d) +
          covariance (GraphTwoLayer.model I x hx c₀).shell
            (F.twoLayer.shellSource (GraphTwoLayer.model I x hx c₀))
            ((GraphTwoLayer.model I x hx c₀).G (1-x) d)) c := by
  unfold instanceScore
  change responseScore (1-x) (parentLaw I x hx) rootCoordinate F.observable = _
  rw [F.observable_additive, actual_response_recursion]
  simp_rw [F.actual_defect_decomposition x hx c₀ hg]
  simp only [add_assoc]
  rfl

theorem option_response_step (hg : 5 ≤ I.graph.egirth) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ))
    (hδ1 : p.δ ≤ 1) (ht : girthFiveThreshold p.δ ≤ Δ)
    (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ)
    (h₂ : ∀ u, colourNorm (deletedScore I x hx p F u) ≤ covarianceChi p.δ * p.responseU * F.weight none)
    (hinf : ∀ u c, |deletedScore I x hx p F u c| ≤
      Real.sqrt p.B * covarianceChi p.δ * p.responseV * F.weight none)
    (hvar : variance (GraphTwoLayer.model I x hx c₀).shell
      (F.twoLayer.shellSource (GraphTwoLayer.model I x hx c₀)) ≤
      (p.Δ * covarianceChi p.δ ^ 2 * F.weight none * p.responseU) ^ 2) :
    colourNorm (instanceScore I x hx F none) ≤ p.responseU * F.weight none ∧
    ∀ c, |instanceScore I x hx F none c| ≤ Real.sqrt p.B * p.responseV * F.weight none := by
  have hχ : 0 ≤ covarianceChi p.δ := (covarianceChi_gt_one p.delta_pos).le.trans' (by norm_num)
  have hU := p.responseU_nonneg hlarge
  have hV := p.responseV_nonneg hlarge
  have hA := (F.positive none).le
  have he := GraphTwoLayer.actual_estimates I x hx c₀ hg hx1 hd p hpΔ hpq hδ1 ht
  have hb := actual_block_contraction I x hx hg hx1 hd p hpΔ hpq hδ1 ht (deletedScore I x hx p F)
    (by positivity : 0 ≤ covarianceChi p.δ * p.responseU * F.weight none)
    (by positivity : 0 ≤ Real.sqrt p.B * covarianceChi p.δ * p.responseV * F.weight none) h₂ hinf
  have hstep := response_step_both p (1-x) (rootLaw I x hx)
    (GraphTwoLayer.model I x hx c₀).shell ((GraphTwoLayer.model I x hx c₀).G (1-x))
    (F.twoLayer.shellSource (GraphTwoLayer.model I x hx c₀))
    (fun d => F.term none d + F.twoLayer.localDefect (GraphTwoLayer.model I x hx c₀) (1-x) d)
    (responseBlockAction (1-x) (rootLaw I x hx) (cavityMarginal I x hx) (deletedScore I x hx p F))
    (instanceScore I x hx F none)
    (by linarith : 0 ≤ 1-x) (by linarith : 1-x ≤ 1)
    (root_atom_le I x hx hx1 hd p hpΔ hpq) hχ hA hU he.colour_covariance hvar
    (F.actual_local_source_bound x hx c₀ hg hx1 hd p hpΔ hpq hδ1 ht hχ)
    (by simpa only [mul_assoc] using hb.1)
    (fun c => by simpa only [mul_assoc] using hb.2 c)
    (weighted_response_recursion I x hx c₀ p F hg)
  exact response_step_supersolution p hlarge _ hstep.1 hstep.2

theorem weighted_child_expansion (hg : 5 ≤ I.graph.egirth) (c : C) :
    F.term none c + expectReal (childLaw I x hx c) F.deleted.observable =
      expectReal (deletedLaw I x hx) F.deleted.observable +
        (F.term none c + F.twoLayer.localDefect (GraphTwoLayer.model I x hx c₀) (1-x) c) +
        covariance (GraphTwoLayer.model I x hx c₀).shell
          (F.twoLayer.shellSource (GraphTwoLayer.model I x hx c₀))
          ((GraphTwoLayer.model I x hx c₀).G (1-x) c) -
        (1-x) * ∑ u, Real.sqrt ((cavityMarginal I x hx u).w c) * deletedScore I x hx p F u c := by
  rw [← insertionMean_eq_child]
  rw [RootInsertion.insertionMean_score _ _ _ _ _ (normalizer_pos I x hx c).ne'
    (fun u => deleted_marginal_pos I x hx u c) (fun u => (deleted_denominator_pos I x hx u c).ne')]
  rw [F.actual_defect_decomposition x hx c₀ hg]
  dsimp only [deletedScore, instanceScore, cavityMarginal, deletedLaw, positiveLaw, coordinate]
  ring_nf
  rfl

theorem option_child_oscillation (hg : 5 ≤ I.graph.egirth) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ))
    (hδ1 : p.δ ≤ 1) (ht : girthFiveThreshold p.δ ≤ Δ)
    (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ)
    (hinf : ∀ u c, |deletedScore I x hx p F u c| ≤
      Real.sqrt p.B * covarianceChi p.δ * p.responseV * F.weight none)
    (hvar : variance (GraphTwoLayer.model I x hx c₀).shell
      (F.twoLayer.shellSource (GraphTwoLayer.model I x hx c₀)) ≤
      (p.Δ * covarianceChi p.δ ^ 2 * F.weight none * p.responseU) ^ 2) (c d : C) :
    |(F.term none c + expectReal (childLaw I x hx c) F.deleted.observable) -
      (F.term none d + expectReal (childLaw I x hx d) F.deleted.observable)| ≤ p.responseM * F.weight none := by
  have hχ : 0 ≤ covarianceChi p.δ := (covarianceChi_gt_one p.delta_pos).le.trans' (by norm_num)
  have hU := p.responseU_nonneg hlarge
  have hV := p.responseV_nonneg hlarge
  have hA := (F.positive none).le
  have he := GraphTwoLayer.actual_estimates I x hx c₀ hg hx1 hd p hpΔ hpq hδ1 ht
  exact colour_oscillation_of_expansion p (1-x) (cavityMarginal I x hx) (deletedScore I x hx p F)
    (GraphTwoLayer.model I x hx c₀).shell ((GraphTwoLayer.model I x hx c₀).G (1-x))
    (F.twoLayer.shellSource (GraphTwoLayer.model I x hx c₀))
    (fun d => F.term none d + F.twoLayer.localDefect (GraphTwoLayer.model I x hx c₀) (1-x) d)
    (fun d => F.term none d + expectReal (childLaw I x hx d) F.deleted.observable)
    (expectReal (deletedLaw I x hx) F.deleted.observable)
    (by linarith) (by linarith) hχ hA hU hV
    (by rw [hpΔ]; exact_mod_cast GraphTwoLayer.first_card_le I hd)
    (cavity_atom_le I x hx hx1 hd p hpΔ hpq)
    (fun u c => by simpa only [mul_assoc] using hinf u c)
    he.colour_covariance hvar
    (F.actual_local_source_bound x hx c₀ hg hx1 hd p hpΔ hpq hδ1 ht hχ)
    (weighted_child_expansion I x hx c₀ p F hg) c d

end GraphResponseRoot
end
end CI2ZF.Appendix.Girth
