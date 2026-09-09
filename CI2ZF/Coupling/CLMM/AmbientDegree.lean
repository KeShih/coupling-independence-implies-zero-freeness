import CI2ZF.Potts.Model.PinningRestriction
import CI2ZF.Potts.Geometry.SeparatorDegree
import Mathlib.Combinatorics.SimpleGraph.Girth

/-! A genuine further pinning preserves the full constraint degree:
each removed free neighbour contributes one new boundary constraint. -/
namespace CI2ZF.Appendix.CLMM
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {A O : Type u} {C : Type v} [Fintype A] [Fintype O] [Fintype C]

theorem restrict_constraintDegree (J : PinningData A C) (e : O ↪ A) (pin : A → Option C)
    (hdom : ∀ a, pin a = none ↔ a ∈ Set.range e) (w : O) :
    (restrictPinningData J e pin).constraintDegree w = J.constraintDegree (e w) := by
  have hset : (univ : Finset O).map e = univ.filter (fun a => pin a = none) := by
    ext a
    simp only [mem_map, mem_univ, true_and, mem_filter]
    exact (hdom a).symm
  have hdegree : (restrictPinningData J e pin).graph.degree w =
      ∑ a : A, if pin a = none then (if J.graph.Adj (e w) a then 1 else 0) else 0 := by
    rw [graph_degree_eq_adj_sum]
    change (∑ o : O, if J.graph.Adj (e w) (e o) then 1 else 0) = _
    rw [← Finset.sum_map (f := fun a => if J.graph.Adj (e w) a then 1 else 0), hset, Finset.sum_filter]
  have hboundary : (∑ c, (restrictPinningData J e pin).boundaryCount w c) =
      (∑ c, J.boundaryCount (e w) c) +
        ∑ a : A, ∑ c : C, if J.graph.Adj (e w) a ∧ pin a = some c then 1 else 0 := by
    simp only [restrictPinningData_count, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  have hpoint (a : A) :
      (if pin a = none then (if J.graph.Adj (e w) a then 1 else 0) else 0) +
        (∑ c : C, if J.graph.Adj (e w) a ∧ pin a = some c then 1 else 0) =
          (if J.graph.Adj (e w) a then 1 else 0) := by
    cases pin a with
    | none => simp
    | some c => by_cases ha : J.graph.Adj (e w) a <;> simp [ha, eq_comm]
  unfold PinningData.constraintDegree
  rw [hdegree, hboundary, graph_degree_eq_adj_sum]
  have hsum := congrArg (fun f : A → ℕ => ∑ a, f a) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  omega

theorem restrict_degreeBound (J : PinningData A C) (e : O ↪ A) (pin : A → Option C)
    (hdom : ∀ a, pin a = none ↔ a ∈ Set.range e) {Δ : ℕ} (hd : J.DegreeBound Δ) :
    (restrictPinningData J e pin).DegreeBound Δ := by
  intro w
  rw [restrict_constraintDegree J e pin hdom]
  exact hd (e w)

theorem restrict_girth (J : PinningData A C) (e : O ↪ A) (pin : A → Option C)
    {g : ℕ∞} (hg : g ≤ J.graph.egirth) :
    g ≤ (restrictPinningData J e pin).graph.egirth :=
  hg.trans (SimpleGraph.Embedding.comap e J.graph).isContained.egirth_le

end
end CI2ZF.Appendix.CLMM
