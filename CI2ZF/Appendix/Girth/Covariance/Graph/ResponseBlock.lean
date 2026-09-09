import CI2ZF.Appendix.Girth.Covariance.Graph.InsertionTransport
import CI2ZF.Appendix.Girth.Covariance.Graph.ReferenceRoot
import CI2ZF.Appendix.Girth.Spectral.Graph.Marginal
import CI2ZF.Appendix.Girth.Covariance.Reference.Response
import CI2ZF.Appendix.Girth.Covariance.Threshold

/-! Both contraction bounds for the actual graph response block. The
palette mass, root cap, cavity caps, and insertion comparison are proved
from the graph degree and colour budgets. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphResponseRoot
variable (I : PinningData (Option V) C) (x : ℝ) (hx : 0 < x)

include hx in
theorem unary_palette_bound (_hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ)) :
    p.m + (Fintype.card (Neighbour I) : ℝ) ≤ ∑ c, unary I x c := by
  have hpalette := palette_mass_lower hx.le (I.boundaryCount none)
  have hcard : Fintype.card (Neighbour I) = I.graph.degree none := by
    simpa only [Neighbour, Fintype.card_coe] using optionRootNeighbours_card I
  have hbudget := hd none
  rw [PinningData.constraintDegree, ← hcard] at hbudget
  have hbudget' : (Fintype.card (Neighbour I) : ℝ) + ∑ c, (I.boundaryCount none c : ℝ) ≤ p.Δ := by
    rw [hpΔ]
    exact_mod_cast hbudget
  have hmass : 0 ≤ ∑ c, (I.boundaryCount none c : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hmx : 0 ≤ x * ∑ c, (I.boundaryCount none c : ℝ) := mul_nonneg hx.le hmass
  unfold CovarianceScale.m
  rw [hpq]
  change _ ≤ ∑ c, paletteWeight x (I.boundaryCount none) c
  nlinarith

theorem root_atom_le (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ)) (c : C) :
    (rootLaw I x hx).w c ≤ p.B := by
  rw [← rootMarginal_eq]
  exact GraphHeatBath.gibbs_marginal_atom_le I x hx hx1 hd p.m_pos
    (by rw [CovarianceScale.m, hpq, hpΔ]) (I.partition_pos_of_parameter_pos hx) none c

theorem cavity_atom_le (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ))
    (u : Neighbour I) (c : C) : (cavityMarginal I x hx u).w c ≤ p.B :=
  GraphHeatBath.gibbs_marginal_atom_le (optionMiddleData I) x hx hx1 (GraphTwoLayer.middle_degreeBound I hd)
    p.m_pos (by rw [CovarianceScale.m, hpq, hpΔ])
    ((optionMiddleData I).partition_pos_of_parameter_pos hx) u.val c

theorem actual_block_contraction (hg : 5 ≤ I.graph.egirth) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ))
    (hpq : p.q = (Fintype.card C : ℝ)) (hδ1 : p.δ ≤ 1) (ht : girthFiveThreshold p.δ ≤ Δ)
    (h : Neighbour I → C → ℝ) {H₂ Hinf : ℝ} (hH₂ : 0 ≤ H₂) (hHinf : 0 ≤ Hinf)
    (hh₂ : ∀ u, colourNorm (h u) ≤ H₂) (hhinf : ∀ u c, |h u c| ≤ Hinf) :
    colourNorm (responseBlockAction (1-x) (rootLaw I x hx) (cavityMarginal I x hx) h) ≤
      p.responseCoefficient * H₂ ∧
    ∀ c, |responseBlockAction (1-x) (rootLaw I x hx) (cavityMarginal I x hx) h c| ≤
      p.responseCoefficient * (Hinf + Real.sqrt p.B * H₂) := by
  have hdU : (Fintype.card (Neighbour I) : ℝ) ≤ p.Δ := by
    rw [hpΔ]
    exact_mod_cast GraphTwoLayer.first_card_le I hd
  have hA : 0 < p.m + (Fintype.card (Neighbour I) : ℝ) := add_pos_of_pos_of_nonneg p.m_pos (Nat.cast_nonneg _)
  have htδ : (Fintype.card (Neighbour I) : ℝ) / (p.m + (Fintype.card (Neighbour I) : ℝ)) ≤ covarianceT p.δ := by
    unfold covarianceT
    apply (div_le_div_iff₀ hA (by linarith [p.delta_pos] : 0 < 1 + p.δ)).mpr
    have hdm := p.colour_budget
    change p.δ * p.Δ ≤ p.m at hdm
    have hδd := mul_le_mul_of_nonneg_left hdU p.delta_pos.le
    nlinarith
  have hb : p.B < 1 := by linarith [p.B_le_half]
  have hs0 : 0 ≤ 1-x := by linarith
  have hs1 : 1-x ≤ 1 := by linarith
  have hcap (u : Neighbour I) (c : C) : (1-x) * (cavityMarginal I x hx u).w c ≤ p.B :=
    (mul_le_of_le_one_left ((cavityMarginal I x hx u).nonneg c) hs1).trans
      (cavity_atom_le I x hx hx1 hd p hpΔ hpq u c)
  have hreference (c : C) : (rootLaw I x hx).w c ≤ Real.exp (2 * p.E) *
      messageMarginal (unary I x) (fun u c => (1-x) * (cavityMarginal I x hx u).w c) c := by
    apply root_reference_bound I x hx
    exact GraphTwoLayer.actual_log_quotient I x hx (Classical.arbitrary C) hg hx1 hd p hpΔ hpq hδ1 ht
  exact reference_response_both (unary I x) (cavityMarginal I x hx) (rootLaw I x hx) h hs0 hs1
    (fun c => ⟨(pow_pos hx _).le, pow_le_one₀ hx.le hx1⟩) hA
    (unary_palette_bound I x hx hx1 hd p hpΔ hpq) p.B_pos hb hcap htδ
    (root_atom_le I x hx hx1 hd p hpΔ hpq) hreference hH₂ hHinf hh₂ hhinf

end GraphResponseRoot
end
end CI2ZF.Appendix.Girth
