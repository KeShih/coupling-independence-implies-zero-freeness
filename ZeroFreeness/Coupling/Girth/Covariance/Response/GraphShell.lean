import ZeroFreeness.Coupling.Girth.Covariance.Response.Shell
import ZeroFreeness.Coupling.Girth.Covariance.Graph.InsertionTransport

/-! The actual root-deleted graph satisfies the full-source shell
variance bound needed in the response recursion. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {V : Type u} {C : Type v} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphTwoLayer
variable (I : PinningData (Option V) C) (x : ℝ) (hx : 0 < x)

theorem shellVariance_of_response {Δ n : ℕ} {χ B U R : ℝ}
    (hglobal : ResponseBoundsUpTo.{u,v} C Δ χ B U R n)
    (c₀ : C) (hsize : Fintype.card V ≤ n) (hd : I.DegreeBound Δ)
    (hg : 5 ≤ I.graph.egirth) (hx1 : x < 1) (hχ : 0 ≤ χ) (F : WeightedSource I χ) :
    variance (model I x hx c₀).shell
      ((F.deleted.relabel (splitEquiv I)).shellSource (model I x hx c₀)) ≤
        ((Δ : ℝ) * χ ^ 2 * F.weight none * U) ^ 2 := by
  have hsize' : Fintype.card (Vertex I) ≤ n := by
    rw [← Fintype.card_congr (splitEquiv I)]
    exact hsize
  have hcard : (Fintype.card (Second I) : ℝ) ≤ (Δ : ℝ) ^ 2 := by
    exact_mod_cast second_card_le I hd
  apply InsertionGraph.shellSource_variance_radius_two (data I) x hx hglobal
    (independent I hg) (separates I) c₀ hsize' (degreeBound I hd) (girth I hg) hx1
    (F.deleted.relabel (splitEquiv I)) (F.positive none).le hcard
  intro w
  change F.weight (some w.val) ≤ χ ^ 2 * F.weight none
  exact F.second_bound none (some (owner I w).val) (some w.val)
    (first_adj I (owner I w)) (owner_adj I w) hχ

end GraphTwoLayer
end
end ZeroFreeness.Appendix.Girth
