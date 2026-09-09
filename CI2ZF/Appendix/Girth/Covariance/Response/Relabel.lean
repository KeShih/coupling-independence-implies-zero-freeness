import CI2ZF.Appendix.Girth.Covariance.Response.Instance
import CI2ZF.Appendix.Girth.Covariance.Doob.PinningVertex

/-! Root response is invariant under genuine vertex relabeling, so the
size induction may use an Option root without restricting the graph. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {V W C : Type*} [Fintype V] [Fintype W] [Fintype C]
  [DecidableEq V] [DecidableEq W] [DecidableEq C] [Nonempty C]

theorem positiveLaw_relabel (I : PinningData V C) (e : V ≃ W) (x : ℝ) (hx : 0 < x) :
    positiveLaw (relabelData I e) x hx = mapLaw (positiveLaw I x hx) (relabelColouring e) :=
  gibbs_relabel I e x hx.le (I.partition_pos_of_parameter_pos hx)
    ((relabelData I e).partition_pos_of_parameter_pos hx)

theorem instanceScore_relabel (I : PinningData V C) (e : V ≃ W) (x : ℝ) (hx : 0 < x)
    {χ : ℝ} (F : WeightedSource I χ) (v : V) :
    instanceScore (relabelData I e) x hx (F.relabel e) (e v) = instanceScore I x hx F v := by
  funext c
  unfold instanceScore
  rw [positiveLaw_relabel, responseScore_map]
  have hk : (fun σ : V → C => relabelColouring e σ (e v)) = fun σ => σ v := by
    funext σ
    simp [relabelColouring]
  have hf : (fun σ : V → C => (F.relabel e).observable (relabelColouring e σ)) = F.observable := by
    funext σ
    rw [F.observable_relabel]
    congr 1
    funext w
    simp [relabelColouring]
  rw [hk, hf]

def OptionResponseBoundsUpTo (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C]
    (Δ : ℕ) (χ B U R : ℝ) (n : ℕ) : Prop :=
  ∀ (O : Type u) [Fintype O] [DecidableEq O] (I : PinningData (Option O) C),
    Fintype.card (Option O) ≤ n → I.DegreeBound Δ → 5 ≤ I.graph.egirth →
    ∀ (x : ℝ) (hx : 0 < x), x < 1 → ∀ F : WeightedSource I χ,
      colourNorm (instanceScore I x hx F none) ≤ U * F.weight none ∧
      ∀ c, |instanceScore I x hx F none c| ≤ Real.sqrt B * R * F.weight none

theorem responseBoundsUpTo_of_option (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C]
    (Δ : ℕ) (χ B U R : ℝ) (n : ℕ) (h : OptionResponseBoundsUpTo.{u,v} C Δ χ B U R n) :
    ResponseBoundsUpTo.{u,v} C Δ χ B U R n := by
  intro V _ _ I hn hd hg x hx hx1 F v
  let e := DoobPinning.rootIndex v
  have hcard : Fintype.card (Option (DoobPinning.Remaining v)) ≤ n := by
    rw [← Fintype.card_congr e]
    exact hn
  have hh := h (DoobPinning.Remaining v) (relabelData I e) hcard
    (relabelData_degreeBound I e hd) (DoobPinning.root_girth I hg v) x hx hx1 (F.relabel e)
  have hev : e v = none := by simp only [e, DoobPinning.rootIndex, Equiv.optionSubtypeNe_symm_self]
  have hs := instanceScore_relabel I e x hx F v
  rw [hev] at hs
  have hw : (F.relabel e).weight none = F.weight v := by
    change F.weight (e.symm none) = _
    rw [← hev, Equiv.symm_apply_apply]
  simpa only [hs, hw] using hh

end
end CI2ZF.Appendix.Girth
