import ZeroFreeness.Coupling.Edge.Slots.ConditionalLimit
import ZeroFreeness.Coupling.Edge.Slots.RootSemantics
import ZeroFreeness.Coupling.Edge.Slots.SlotLift
import ZeroFreeness.Coupling.Edge.Finite.CI
import ZeroFreeness.Coupling.Vigoda.RootCoupling

/-!
# Edge-Potts coupling independence at q ≥ 3Δ

The proof uses constructed finite slot laws, the internally proved weighted
endpoint-label recursion, exact root-colour disintegration, and a finite
colour-space limit. The hard endpoint follows by Gibbs-weight continuity.
-/

namespace ZeroFreeness.Appendix.Edge
open PottsCI PottsCI.FinDist ZeroFreeness.Potts EndpointGeometry FiniteSystem
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq C := Classical.decEq C

/-- The strict positive-temperature edge-Potts CI bound, for actual root
children under every arbitrary edge-colour pinning. -/
theorem root_children_ci_open (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (r : τ.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    W ham ((rootChildData τ G.lineGraph r a).gibbs x hx.le
      ((rootChildData τ G.lineGraph r a).partition_pos_of_parameter_pos hx))
      ((rootChildData τ G.lineGraph r b).gibbs x hx.le
        ((rootChildData τ G.lineGraph r b).partition_pos_of_parameter_pos hx)) ≤ (Δ : ℝ) - 1 := by
  apply (W_rootChildren_le_rootExcluded τ G.lineGraph r a b x hx).trans
  rw [← freeEdgeGeometry_targetLaw G τ x hx]
  apply targetRootExcludedColourLaw_W_le (freeEdgeGeometry G τ) x hx hx1
    (τ.boundaryCount G.lineGraph) r a b
  intro n
  have hB := freeEdgeGeometry_approxSlotSystem_bounds G τ x hx hx1 hdegree hq n
  apply approxRootExcludedColourLaw_W_le (freeEdgeGeometry G τ) x hx hx1
    (τ.boundaryCount G.lineGraph) n hB r a b
  intro ξ η hξ hη
  exact ((freeEdgeGeometry G τ).approxSlotSystem x hx hx1 (τ.boundaryCount G.lineGraph) n).root_state_ci
    hΔ (fun _ => ∅) hB r ξ η hξ hη

lemma pinningWeight_one {E : Type*} [Fintype E] (I : PinningData E C) (σ : E → C) :
    I.weight 1 σ = 1 := by
  have he (z : Sym2 E) : PinningData.edgeFactor 1 σ z = 1 := by
    induction z using Sym2.ind with
    | _ e f => simp [PinningData.edgeFactor_mk]
  simp only [PinningData.weight, one_pow, Finset.prod_const_one, he, mul_one]

lemma pinningGibbs_one_eq {E : Type*} [Fintype E] (I J : PinningData E C) :
    I.gibbs 1 (by norm_num) (I.partition_pos_of_parameter_pos (by norm_num)) =
      J.gibbs 1 (by norm_num) (J.partition_pos_of_parameter_pos (by norm_num)) := by
  apply FinDist.ext
  funext σ
  simp only [PinningData.gibbs, PinningData.partition, pinningWeight_one]

theorem root_children_ci_positive (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (r : τ.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    W ham ((rootChildData τ G.lineGraph r a).gibbs x hx.le
      ((rootChildData τ G.lineGraph r a).partition_pos_of_parameter_pos hx))
      ((rootChildData τ G.lineGraph r b).gibbs x hx.le
        ((rootChildData τ G.lineGraph r b).partition_pos_of_parameter_pos hx)) ≤ (Δ : ℝ) - 1 := by
  rcases eq_or_lt_of_le hx1 with rfl | hlt
  · rw [pinningGibbs_one_eq (rootChildData τ G.lineGraph r a) (rootChildData τ G.lineGraph r b),
      W_self ham_nonneg ham_self]
    exact sub_nonneg.mpr (by exact_mod_cast hΔ)
  · exact root_children_ci_open G τ r a b hΔ hdegree hq x hx hlt

lemma lineGraph_degree_le (G : SimpleGraph V) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) : ∀ e, G.lineGraph.degree e ≤ 2 * Δ - 2 := by
  intro e
  exact Nat.le_sub_of_add_le (lineGraph_degree_bound G hdegree e)

lemma lineGraph_colours_slack {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hq : 3 * Δ ≤ Fintype.card C) : (2 * Δ - 2) + 2 ≤ Fintype.card C := by
  have hh : 2 ≤ 2 * Δ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hΔ
  rw [Nat.sub_add_cancel hh]
  exact (Nat.mul_le_mul_right Δ (by decide : 2 ≤ 3)).trans hq

/-- `thm:soft-edge-ci`: the bound Δ−1 holds on the full closed interval,
including hard edge colourings and arbitrary normalized partial pinnings. -/
theorem root_children_ci (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (r : τ.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham ((rootChildData τ G.lineGraph r a).gibbs x x.property
      ((rootChildData τ G.lineGraph r a).partition_pos x.property
        (rootChildData_degreeBound τ G.lineGraph r a (lineGraph_degree_le G hdegree))
        (lineGraph_colours_slack hΔ hq)))
      ((rootChildData τ G.lineGraph r b).gibbs x x.property
        ((rootChildData τ G.lineGraph r b).partition_pos x.property
          (rootChildData_degreeBound τ G.lineGraph r b (lineGraph_degree_le G hdegree))
          (lineGraph_colours_slack hΔ hq))) ≤ (Δ : ℝ) - 1 := by
  by_cases hz : (x : ℝ) = 0
  · have hx : x = PinningData.hardParameter := Subtype.ext hz
    subst x
    apply (rootChildData τ G.lineGraph r a).hard_W_le_of_positive_parameter_bound
      (rootChildData τ G.lineGraph r b)
      (rootChildData_degreeBound τ G.lineGraph r a (lineGraph_degree_le G hdegree))
      (rootChildData_degreeBound τ G.lineGraph r b (lineGraph_degree_le G hdegree))
      (lineGraph_colours_slack hΔ hq) ZeroFreeness.hardApproach ZeroFreeness.tendsto_hardApproach
      (Filter.Eventually.of_forall ZeroFreeness.hardApproach_pos)
      (Filter.Eventually.of_forall ZeroFreeness.hardApproach_le_one)
      ham_nonneg ham_self ham_triangle ham_le_card
    intro y hy hy1
    exact root_children_ci_positive G τ r a b hΔ hdegree hq y hy hy1
  · exact root_children_ci_positive G τ r a b hΔ hdegree hq x
      (lt_of_le_of_ne x.property (Ne.symm hz)) hx1

end
end ZeroFreeness.Appendix.Edge
