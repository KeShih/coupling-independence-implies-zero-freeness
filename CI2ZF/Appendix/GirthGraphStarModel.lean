import CI2ZF.Appendix.GirthGraphStarWeights
import CI2ZF.Appendix.GirthStarL2

/-! The conditional-star data are obtained from genuine pinned graph constraints. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace GraphStar
local instance (priority := 2000) graphStarModelLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _

theorem cavityPartition_ge_two (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (v : V) (σ : V → C) (u : Leaf I v) : 2 ≤ cavityPartition I x v σ u := by
  have hl := cavityPartition_lower I hx v σ u
  have hv : (I.constraintDegree u.val : ℝ) ≤ Δ := by exact_mod_cast hd u.val
  have hq' : (Δ : ℝ) + 1 ≤ Fintype.card C := by exact_mod_cast hq
  have hp : (1 : ℝ) ≤ I.constraintDegree u.val := by
    have hh := cavityCount_sum I v σ u
    exact_mod_cast (show 1 ≤ I.constraintDegree u.val by omega)
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hp)]

def cavityLaw (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (v : V) (σ : V → C) (u : Leaf I v) : FinDist C where
  w c := cavityWeight I x v σ u c / cavityPartition I x v σ u
  nonneg c := div_nonneg (pow_nonneg hx _) (by linarith [cavityPartition_ge_two I hx hd hq v σ u])
  sum_one := by
    rw [← Finset.sum_div]
    have hp : 0 < cavityPartition I x v σ u := by
      linarith [cavityPartition_ge_two I hx hd hq v σ u]
    exact div_self hp.ne' 

theorem cavityLaw_le_half (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (v : V) (σ : V → C) (u : Leaf I v) (c : C) :
    (cavityLaw I x hx hd hq v σ u).w c ≤ 1/2 := by
  have hz := cavityPartition_ge_two I hx hd hq v σ u
  have hn : cavityWeight I x v σ u c ≤ 1 := pow_le_one₀ hx hx1
  change cavityWeight I x v σ u c / cavityPartition I x v σ u ≤ _
  apply (div_le_iff₀ (by linarith : 0 < cavityPartition I x v σ u)).mpr
  linarith

theorem unary_palette_budget (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (v : V) :
    (Fintype.card C : ℝ) - (1-x) * Δ ≤
      (∑ c, unary I x v c) - (Fintype.card (Leaf I v) : ℝ) * (1-x) := by
  have hb := palette_mass_lower hx (I.boundaryCount v)
  have hc : Fintype.card (Leaf I v) = I.graph.degree v := I.graph.card_neighborSet_eq_degree v
  rw [hc]
  have hv : (I.graph.degree v : ℝ) + ∑ c, (I.boundaryCount v c : ℝ) ≤ Δ := by
    exact_mod_cast hd v
  have hm := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hx1)
  change _ ≤ (∑ c, paletteWeight x (I.boundaryCount v) c) - _
  nlinarith

def model (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (v : V) (σ : V → C) : ConditionalStar C (Leaf I v) where
  s := 1-x
  s_nonneg := sub_nonneg.mpr hx1
  s_le_one := by linarith
  unary := unary I x v
  unary_nonneg c := pow_nonneg hx _
  unary_le_one c := pow_le_one₀ hx hx1
  cavity := cavityLaw I x hx hd hq v σ
  edge_positive u c := by
    have hh := cavityLaw_le_half I x hx hx1 hd hq v σ u c
    have hn := (cavityLaw I x hx hd hq v σ u).nonneg c
    nlinarith [mul_nonneg hx hn]
  palette_slack := by
    have hl := unary_palette_budget I x hx hx1 hd v
    have hq' : (Δ : ℝ) + 1 ≤ Fintype.card C := by exact_mod_cast hq
    nlinarith [mul_nonneg hx (Nat.cast_nonneg Δ : (0:ℝ) ≤ Δ)]

theorem cavityLaw_extend (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (x : ℝ) (hx : 0 ≤ x) {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (v : V) (σ : V → C) (τ : Configuration I v) (u : Leaf I v) :
    cavityLaw I x hx hd hq v (extend I v σ τ) u = cavityLaw I x hx hd hq v σ u := by
  apply FinDist.ext
  funext c
  simp only [cavityLaw, cavityPartition, cavityWeight, cavityCount_extend I hg]

theorem model_extend (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (v : V) (σ : V → C) (τ : Configuration I v) :
    model I x hx hx1 hd hq v (extend I v σ τ) = model I x hx hx1 hd hq v σ := by
  have hc : cavityLaw I x hx hd hq v (extend I v σ τ) = cavityLaw I x hx hd hq v σ :=
    funext (cavityLaw_extend I hg x hx hd hq v σ τ)
  unfold model
  congr 1

def normalizer (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (v : V) (σ : V → C) : ℝ :=
  (∏ u : Leaf I v, cavityPartition I x v σ u) * (model I x hx hx1 hd hq v σ).normalizer

theorem normalizer_pos (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (v : V) (σ : V → C) :
    0 < normalizer I x hx hx1 hd hq v σ := by
  apply mul_pos _ (ConditionalStar.normalizer_pos _)
  exact Finset.prod_pos fun u _ => by linarith [cavityPartition_ge_two I hx hd hq v σ u]

theorem jointLaw_weight (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (v : V) (σ : V → C)
    (τ : Configuration I v) :
    (model I x hx hx1 hd hq v σ).jointLaw.w (τ none, fun u => τ (some u)) =
      rawWeight I x v σ τ / normalizer I x hx hx1 hd hq v σ := by
  rw [ConditionalStar.jointLaw_weight]
  have he (c d : C) : 1 - (1-x) * colourIndicator c d = edge x c d := by
    by_cases h : c = d <;> simp [colourIndicator, edge, h, eq_comm]
  change (unary I x v (τ none) / (model I x hx hx1 hd hq v σ).normalizer) *
    (∏ u : Leaf I v, (cavityWeight I x v σ u (τ (some u)) / cavityPartition I x v σ u) *
      (1 - (1-x) * colourIndicator (τ none) (τ (some u)))) = _
  simp_rw [he, div_mul_eq_mul_div]
  rw [Finset.prod_div_distrib]
  unfold rawWeight normalizer
  ring

end GraphStar
end
end CI2ZF.Appendix.Girth
