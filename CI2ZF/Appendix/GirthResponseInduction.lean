import CI2ZF.Appendix.GirthResponseOptionStep
import CI2ZF.Appendix.GirthResponseGraphShell
import CI2ZF.Appendix.GirthResponseRelabel

/-! Closure of the actual girth-five response induction. Both the
deleted-neighbour response and the full-source shell variance use only
the theorem on graphs with one fewer vertex. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v

theorem actual_response_bounds (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C]
    (p : CovarianceScale) {Δ : ℕ} (hpΔ : p.Δ = (Δ : ℝ))
    (hpq : p.q = (Fintype.card C : ℝ)) (hδ1 : p.δ ≤ 1)
    (ht : girthFiveThreshold p.δ ≤ Δ) (hlarge : covarianceDegreeThreshold p.δ ≤ p.Δ) :
    ∀ n, ResponseBoundsUpTo.{u,v} C Δ (covarianceChi p.δ) p.B p.responseU p.responseV n := by
  have hχ : 0 ≤ covarianceChi p.δ := (covarianceChi_gt_one p.delta_pos).le.trans' (by norm_num)
  have hU := p.responseU_nonneg hlarge
  have hV := p.responseV_nonneg hlarge
  intro n
  induction n with
  | zero => exact responseBoundsUpTo_zero C Δ _ _ _ _
  | succ n ih =>
    apply responseBoundsUpTo_of_option C Δ _ _ _ _ (n+1)
    intro V _ _ I hn hd hg x hx hx1 F
    have hsize : Fintype.card V ≤ n := by
      rw [Fintype.card_option] at hn
      omega
    have hmiddle : 5 ≤ (optionMiddleData I).graph.egirth := by
      let e : V ↪ Option V := ⟨Option.some, Option.some_injective V⟩
      exact hg.trans (SimpleGraph.Embedding.comap e I.graph).isContained.egirth_le
    have hi (u : GraphResponseRoot.Neighbour I) :=
      ih V (optionMiddleData I) hsize (GraphTwoLayer.middle_degreeBound I hd) hmiddle x hx hx1 F.deleted u.val
    have hw (u : GraphResponseRoot.Neighbour I) :
        F.deleted.weight u.val ≤ covarianceChi p.δ * F.weight none :=
      F.neighbour_bound none (some u.val) (GraphTwoLayer.first_adj I u)
    have h₂ (u : GraphResponseRoot.Neighbour I) :
        colourNorm (GraphResponseRoot.deletedScore I x hx p F u) ≤
          covarianceChi p.δ * p.responseU * F.weight none := by
      calc
        _ ≤ p.responseU * F.deleted.weight u.val := (hi u).1
        _ ≤ p.responseU * (covarianceChi p.δ * F.weight none) := mul_le_mul_of_nonneg_left (hw u) hU
        _ = _ := by ring
    have hinf (u : GraphResponseRoot.Neighbour I) (c : C) :
        |GraphResponseRoot.deletedScore I x hx p F u c| ≤
          Real.sqrt p.B * covarianceChi p.δ * p.responseV * F.weight none := by
      calc
        _ ≤ Real.sqrt p.B * p.responseV * F.deleted.weight u.val := (hi u).2 c
        _ ≤ Real.sqrt p.B * p.responseV * (covarianceChi p.δ * F.weight none) :=
          mul_le_mul_of_nonneg_left (hw u) (mul_nonneg (Real.sqrt_nonneg _) hV)
        _ = _ := by ring
    let c₀ : C := Classical.arbitrary C
    have hvar := GraphTwoLayer.shellVariance_of_response I x hx ih c₀ hsize hd hg hx1 hχ F
    apply GraphResponseRoot.option_response_step I x hx c₀ p F hg hx1.le hd hpΔ hpq hδ1 ht hlarge h₂ hinf
    simpa only [WeightedSource.twoLayer, WeightedSource.shellSource, GraphTwoLayer.data, hpΔ] using hvar

end
end CI2ZF.Appendix.Girth
