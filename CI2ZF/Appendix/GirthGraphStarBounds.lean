import CI2ZF.Appendix.GirthGraphStarModel

/-! Every conditional star of the actual graph satisfies the local analytic budgets. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
namespace GraphStar
local instance (priority := 2000) graphStarBoundsLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _

variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
  (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (v : V)

include hd in
theorem leaf_card_le : Fintype.card (Leaf I v) ≤ Δ := by
  have hc : Fintype.card (Leaf I v) = I.graph.degree v := I.graph.card_neighborSet_eq_degree v
  rw [hc]
  have hh := hd v
  unfold PinningData.constraintDegree at hh
  omega

theorem palette_budget {δ : ℝ} (hδ : 0 < δ)
    (hcol : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (σ : V → C) :
    (model I x hx hx1 hd hq v σ).s * ((Fintype.card (Leaf I v) : ℝ) + δ * Δ) ≤
      (model I x hx hx1 hd hq v σ).palette := by
  have hl := unary_palette_budget I x hx hx1 hd v
  change (1-x) * ((Fintype.card (Leaf I v) : ℝ) + δ * Δ) ≤ ∑ c, unary I x v c
  have hp : 0 ≤ x * ((1+δ) * Δ) := mul_nonneg hx (by positivity)
  nlinarith

theorem model_normalizer_lower {δ : ℝ}
    (hcol : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (σ : V → C) :
    δ * Δ ≤ (model I x hx hx1 hd hq v σ).normalizer := by
  have hl := unary_palette_budget I x hx hx1 hd v
  have hn := (model I x hx hx1 hd hq v σ).normalizer_lower
  change (∑ c, unary I x v c) - (Fintype.card (Leaf I v) : ℝ) * (1-x) ≤ _ at hn
  nlinarith [mul_nonneg hx (Nat.cast_nonneg Δ : (0:ℝ) ≤ Δ)]

include hx hx1 hd in
theorem cavity_normalizer_lower {δ : ℝ}
    (hcol : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (σ : V → C) (u : Leaf I v) :
    δ * Δ ≤ cavityPartition I x v σ u := by
  have hl := cavityPartition_lower I hx v σ u
  have hv : (I.constraintDegree u.val : ℝ) ≤ Δ := by exact_mod_cast hd u.val
  have hm := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hx1)
  nlinarith [mul_nonneg hx (Nat.cast_nonneg Δ : (0:ℝ) ≤ Δ)]

theorem cavity_scaled_le {δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hcol : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (σ : V → C) (u : Leaf I v) (c : C) :
    (model I x hx hx1 hd hq v σ).s * ((model I x hx hx1 hd hq v σ).cavity u).w c ≤
      1 / (δ * Δ) := by
  have hD : (0:ℝ) < Δ := by exact_mod_cast hΔ
  have hpos : 0 < δ * Δ := mul_pos hδ hD
  have hl := cavity_normalizer_lower I x hx hx1 hd v hcol σ u
  have hn : cavityWeight I x v σ u c ≤ 1 := pow_le_one₀ hx hx1
  have hc : (cavityLaw I x hx hd hq v σ u).w c ≤ 1 / (δ * Δ) := by
    change cavityWeight I x v σ u c / cavityPartition I x v σ u ≤ _
    calc
      _ ≤ 1 / cavityPartition I x v σ u := div_le_div_of_nonneg_right hn (hpos.le.trans hl)
      _ ≤ _ := div_le_div_of_nonneg_left zero_le_one hpos hl
  have hp := (cavityLaw I x hx hd hq v σ u).nonneg c
  change (1-x) * (cavityLaw I x hx hd hq v σ u).w c ≤ _
  nlinarith [mul_nonneg hx hp]

theorem centre_scaled_le {δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hcol : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (σ : V → C) (c : C) :
    (model I x hx hx1 hd hq v σ).s * (model I x hx hx1 hd hq v σ).centreLaw.w c ≤
      1 / (δ * Δ) := by
  let S := model I x hx hx1 hd hq v σ
  have hD : (0:ℝ) < Δ := by exact_mod_cast hΔ
  have hpos : 0 < δ * Δ := mul_pos hδ hD
  have hl := model_normalizer_lower I x hx hx1 hd hq v hcol σ
  have hn : messageWeight S.unary (fun i c => S.s * (S.cavity i).w c) c ≤ 1 :=
    messageWeight_le_one (fun c => ⟨S.unary_nonneg c, S.unary_le_one c⟩)
      (fun i c => ⟨mul_nonneg S.s_nonneg ((S.cavity i).nonneg c), by linarith [S.edge_positive i c]⟩) c
  have hc : S.centreLaw.w c ≤ 1 / (δ * Δ) := by
    change messageWeight S.unary (fun i c => S.s * (S.cavity i).w c) c / S.normalizer ≤ _
    calc
      _ ≤ 1 / S.normalizer := div_le_div_of_nonneg_right hn S.normalizer_pos.le
      _ ≤ _ := div_le_div_of_nonneg_left zero_le_one hpos hl
  have hm := mul_le_mul_of_nonneg_right S.s_le_one (S.centreLaw.nonneg c)
  change S.s * S.centreLaw.w c ≤ _
  nlinarith

end GraphStar
end
end CI2ZF.Appendix.Girth
