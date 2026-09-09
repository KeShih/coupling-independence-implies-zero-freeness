import CI2ZF.Appendix.Girth.Spectral.Graph.StarLaw
import CI2ZF.Appendix.Girth.Spectral.HeatBath

/-! Actual graph heat baths restrict to the centre and leaf conditional-star operators. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace ConditionalStar
variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

theorem centreConditionalLaw_weight (S : ConditionalStar C D) (τ : D → C) (c : C) :
    (S.centreConditionalLaw τ).w c =
      messageWeight S.unary (fun i c => S.s * colourIndicator c (τ i)) c /
        messagePartition S.unary (fun i c => S.s * colourIndicator c (τ i)) := by
  have hn : S.centreLaw.w c * (∏ i, edgeLikelihood S.s (S.cavity i) c (τ i)) =
      messageWeight S.unary (fun i c => S.s * colourIndicator c (τ i)) c / S.normalizer := by
    change ((S.unary c * ∏ i, (1 - S.s * (S.cavity i).w c)) / S.normalizer) * _ = _
    unfold edgeLikelihood messageWeight
    have hp : (∏ i, (1 - S.s * (S.cavity i).w c)) ≠ 0 :=
      (Finset.prod_pos fun i _ => S.edge_positive i c).ne'
    rw [Finset.prod_div_distrib]
    field_simp [hp, S.normalizer_pos.ne']
  change (_ * _) / S.leafDensity τ = _
  rw [hn, S.leafDensity_eq]
  exact div_div_div_cancel_right₀ S.normalizer_pos.ne' _ _

end ConditionalStar

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
namespace GraphStar
local instance (priority := 2000) graphStarLocalLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _

variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
  (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (v : V)

theorem edge_indicator (c d : C) : 1 - (1-x) * colourIndicator c d = edge x c d := by
  by_cases h : c = d <;> simp [colourIndicator, edge, h, eq_comm]

theorem root_siteLaw (σ : V → C) (τ : Configuration I v) :
    GraphHeatBath.siteLaw I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq)
      (extend I v σ τ) v =
    (model I x hx hx1 hd hq v σ).centreConditionalLaw (fun u => τ (some u)) := by
  have he (c : C) : messageWeight (model I x hx hx1 hd hq v σ).unary
      (fun i d => (model I x hx hx1 hd hq v σ).s * colourIndicator d (τ (some i))) c =
      GraphHeatBath.siteWeight I x (extend I v σ τ) v c := by
    rw [siteWeight_root]
    change unary I x v c * (∏ i, (1 - (1-x) * colourIndicator c (τ (some i)))) = _
    simp_rw [edge_indicator]
  apply FinDist.ext
  funext c
  rw [ConditionalStar.centreConditionalLaw_weight]
  simp only [messagePartition, he]
  rfl

theorem leaf_siteLaw (hg : 5 ≤ I.graph.egirth) (σ : V → C) (τ : Configuration I v) (u : Leaf I v) :
    GraphHeatBath.siteLaw I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq)
      (extend I v σ τ) u.val =
    edgeChannel ((model I x hx hx1 hd hq v σ).cavity u)
      (model I x hx hx1 hd hq v σ).s (model I x hx hx1 hd hq v σ).s_le_one
      (τ none) ((model I x hx hx1 hd hq v σ).edge_positive u (τ none)) := by
  let S := model I x hx hx1 hd hq v σ
  let p := edgeChannel (S.cavity u) S.s S.s_le_one (τ none) (S.edge_positive u (τ none))
  let Z := cavityPartition I x v σ u
  let k := Z * (1 - S.s * (S.cavity u).w (τ none))
  have hZ : 0 < Z := by dsimp [Z]; linarith [cavityPartition_ge_two I hx hd hq v σ u]
  have he : 0 < 1 - S.s * (S.cavity u).w (τ none) := S.edge_positive u (τ none)
  have hk : 0 < k := mul_pos hZ he
  have hp (c : C) : GraphHeatBath.siteWeight I x (extend I v σ τ) u.val c = k * p.w c := by
    rw [siteWeight_leaf I hg]
    change cavityWeight I x v σ u c * edge x (τ none) c =
      (Z * (1 - S.s * (S.cavity u).w (τ none))) *
        ((cavityWeight I x v σ u c / Z) *
          ((1 - (1-x) * colourIndicator (τ none) c) / (1 - S.s * (S.cavity u).w (τ none))))
    rw [edge_indicator]
    field_simp [hZ.ne', he.ne']
  have hz : GraphHeatBath.sitePartition I x (extend I v σ τ) u.val = k := by
    unfold GraphHeatBath.sitePartition
    simp_rw [hp]
    rw [← Finset.mul_sum, p.sum_one, mul_one]
  apply FinDist.ext
  funext c
  change GraphHeatBath.siteWeight I x (extend I v σ τ) u.val c /
      GraphHeatBath.sitePartition I x (extend I v σ τ) u.val = p.w c
  rw [hp, hz]
  exact mul_div_cancel_left₀ _ hk.ne'

def pull (σ : V → C) (f : (V → C) → ℝ) : C × (Leaf I v → C) → ℝ :=
  fun z => f (extend I v σ (Equiv.piOptionEquivProd.symm z))

theorem pair_root_update (τ : Configuration I v) (c : C) :
    Equiv.piOptionEquivProd.symm (c, fun u => τ (some u)) = Function.update τ none c := by
  funext i
  cases i <;> simp [Equiv.piOptionEquivProd]

theorem pair_leaf_update (τ : Configuration I v) (u : Leaf I v) (c : C) :
    Equiv.piOptionEquivProd.symm (τ none, Function.update (fun u => τ (some u)) u c) =
      Function.update τ (some u) c := by
  funext i
  cases i with
  | none => simp [Equiv.piOptionEquivProd]
  | some j => simp [Equiv.piOptionEquivProd, Function.update_apply]

theorem projection_root_at (σ : V → C) (f : (V → C) → ℝ) (τ : Configuration I v) :
    GraphHeatBath.projection I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) v f (extend I v σ τ) =
      (model I x hx hx1 hd hq v σ).centreProjection (pull I v σ f) (τ none, fun u => τ (some u)) := by
  unfold GraphHeatBath.projection ConditionalStar.centreProjection
  rw [ConditionalStar.centreAverage_expectation, root_siteLaw I x hx hx1 hd hq v]
  apply congrArg (expectReal _)
  funext c
  simp only [pull, pair_root_update, extend_update, vertex]

theorem projection_leaf_at (hg : 5 ≤ I.graph.egirth) (σ : V → C)
    (f : (V → C) → ℝ) (τ : Configuration I v) (u : Leaf I v) :
    GraphHeatBath.projection I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) u.val f (extend I v σ τ) =
      (model I x hx hx1 hd hq v σ).leafProjection u (pull I v σ f) (τ none, fun u => τ (some u)) := by
  unfold GraphHeatBath.projection ConditionalStar.leafProjection productProjection
  rw [leaf_siteLaw I x hx hx1 hd hq v hg]
  apply congrArg (expectReal _)
  funext c
  simp only [pull, pair_leaf_update, extend_update, vertex]

theorem pull_root_projection (σ : V → C) (f : (V → C) → ℝ) :
    pull I v σ (GraphHeatBath.projection I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) v f) =
      (model I x hx hx1 hd hq v σ).centreProjection (pull I v σ f) := by
  funext z
  have h := projection_root_at I x hx hx1 hd hq v σ f (Equiv.piOptionEquivProd.symm z)
  exact h

theorem pull_leaf_projection (hg : 5 ≤ I.graph.egirth) (σ : V → C) (f : (V → C) → ℝ) (u : Leaf I v) :
    pull I v σ (GraphHeatBath.projection I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) u.val f) =
      (model I x hx hx1 hd hq v σ).leafProjection u (pull I v σ f) := by
  funext z
  have h := projection_leaf_at I x hx hx1 hd hq v hg σ f (Equiv.piOptionEquivProd.symm z) u
  exact h

end GraphStar
end
end CI2ZF.Appendix.Girth
