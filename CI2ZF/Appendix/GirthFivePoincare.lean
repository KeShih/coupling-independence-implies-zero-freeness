import CI2ZF.Appendix.GirthGraphStarTransfer
import CI2ZF.Appendix.GirthStarRaw

/-! The proved all-instance girth-five Poincaré inequality, with every
local projection and probability estimate discharged internally. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Type*} [Fintype C]

theorem girthFive_colour_slack {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hq : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) : Δ + 2 ≤ Fintype.card C := by
  have hh := (girthFiveThreshold_bounds hδ hδ1 hΔ).2.1
  have hreal : (Δ : ℝ) + 2 ≤ Fintype.card C := by nlinarith
  exact_mod_cast hreal

namespace ConditionalStar
variable {D : Type*} [Fintype D] [DecidableEq C]

theorem localForm_expectation (S : ConditionalStar C D) (β : D → ℝ) (δ : ℝ)
    (f : C × (D → C) → ℝ) :
    expectReal S.jointLaw (S.localForm β (StarData.theta δ) f) = S.rawStarDefect β δ f := by
  have he (g : C × (D → C) → ℝ) :
      expectReal S.jointLaw (fun σ => g σ / 2) = expectReal S.jointLaw g / 2 := by
    simp only [expectReal, mul_div_assoc, Finset.sum_div]
  unfold localForm rawStarDefect centreDifference leafDifference weightedDifference
  simp only [leafDifference, one_mul, expectReal_add, expectReal_sub, expectReal_const_mul,
    expectReal_finset_sum, he]

end ConditionalStar

variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
namespace GraphStar
local instance (priority := 2000) girthFivePoincareLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _

variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
  (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)

def schurParameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hΔ : girthFiveThreshold δ ≤ Δ) (hcol : (1+δ) * Δ ≤ (Fintype.card C : ℝ))
    (v : V) (σ : V → C) : (model I x hx hx1 hd hq v σ).SchurParameters where
  δ := δ
  Δ := Δ
  delta_pos := hδ
  delta_le_one := hδ1
  threshold := hΔ
  degree_le := leaf_card_le I hd v
  palette_budget := palette_budget I x hx hx1 hd hq v hδ hcol σ
  cavity_cap u c := by
    have hd0 : 0 < Δ := by exact_mod_cast (girthFiveThreshold_bounds hδ hδ1 hΔ).1
    exact cavity_scaled_le I x hx hx1 hd hq v hδ hd0 hcol σ u c
  centre_cap c := by
    have hd0 : 0 < Δ := by exact_mod_cast (girthFiveThreshold_bounds hδ hδ1 hΔ).1
    exact centre_scaled_le I x hx hx1 hd hq v hδ hd0 hcol σ c

theorem actual_localStarBound (hg : 5 ≤ I.graph.egirth) (hx0 : 0 < x)
    (hZ : 0 < I.partition x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hΔ : girthFiveThreshold δ ≤ Δ) (hcol : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) :
    (GraphHeatBath.system I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) hZ).LocalStarBound
      (StarData.theta δ) := by
  apply localStarBound_of_conditional I x hx hx1 hd hq hg hx0 hZ (StarData.theta δ)
  intro v σ f
  rw [ConditionalStar.localForm_expectation]
  exact (schurParameters I x hx hx1 hd hq hδ hδ1 hΔ hcol v σ).raw_star_inequality
    (beta I v) (fun u => ⟨beta_pos I v u, beta_lt_two I v u⟩) (pull I v σ f)

end GraphStar

/-- Uniform Poincaré for the actual normalized Gibbs law of every residual
instance. Its hypotheses are only the appendix's graph and scalar assumptions. -/
theorem girth_five_positive_poincare [Nonempty C] (I : PinningData V C)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (hZ : 0 < I.partition x)
    (f : (V → C) → ℝ) :
    GraphProjections.spectralGap δ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ) (fun σ =>
        (f σ - GraphHeatBath.projection I x hx.le
          (GraphHeatBath.sitePartition_pos I hx.le hx1 hdegree
            (show Δ + 1 ≤ Fintype.card C from by have hh := girthFive_colour_slack hδ hδ1 hΔ hq; omega)) v f σ) ^ 2) := by
  have hq1 : Δ + 1 ≤ Fintype.card C := by
    have hh := girthFive_colour_slack hδ hδ1 hΔ hq
    omega
  exact GraphHeatBath.positive_poincare I x hx
    (GraphHeatBath.sitePartition_pos I hx.le hx1 hdegree hq1) hZ hδ hg
    (GraphStar.actual_localStarBound I x hx.le hx1 hdegree hq1 hg hx hZ hδ hδ1 hΔ hq) f

end
end CI2ZF.Appendix.Girth
