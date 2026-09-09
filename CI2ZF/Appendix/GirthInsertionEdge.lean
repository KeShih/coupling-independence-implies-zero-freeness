import CI2ZF.Appendix.GirthInsertionGraph
import CI2ZF.Appendix.GirthInsertionAffine

/-! The cavity law after one incident constraint is removed, with its
actual degree slack and exact edge-update formula. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 < x)

def cavityCount (σ : V → C) (v w : V) (c : C) : ℕ :=
  I.boundaryCount v c + (((I.graph.neighborFinset v).erase w).filter (fun u => σ u = c)).card

def cavityWeight (σ : V → C) (v w : V) (c : C) : ℝ := x ^ cavityCount I σ v w c

def cavityPartition (σ : V → C) (v w : V) : ℝ := ∑ c, cavityWeight I x σ v w c

include hx in
theorem cavityPartition_pos (σ : V → C) (v w : V) : 0 < cavityPartition I x σ v w := by
  apply Finset.sum_pos
  · intro c _
    exact pow_pos hx _
  · exact Finset.univ_nonempty

def cavityLaw (σ : V → C) (v w : V) : FinDist C where
  w c := cavityWeight I x σ v w c / cavityPartition I x σ v w
  nonneg c := div_nonneg (pow_nonneg hx.le _) (cavityPartition_pos I x hx σ v w).le
  sum_one := by rw [← Finset.sum_div]; exact div_self (cavityPartition_pos I x hx σ v w).ne'

theorem cavityCount_sum (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) :
    (∑ c, cavityCount I σ v w c) + 1 = I.constraintDegree v := by
  unfold cavityCount PinningData.constraintDegree
  rw [Finset.sum_add_distrib]
  have h := Finset.sum_card_fiberwise_eq_card_filter ((I.graph.neighborFinset v).erase w)
    (Finset.univ : Finset C) σ
  simp only [Finset.mem_univ, Finset.filter_true] at h
  rw [h]
  have hc : ((I.graph.neighborFinset v).erase w).card + 1 = I.graph.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_erase_add_one (by simpa using hvw)
  omega

theorem cavityLaw_atom_le (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ) {m : ℝ}
    (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) (c : C) :
    (cavityLaw I x hx σ v w).w c ≤ 1 / (m + 1) := by
  have hb := palette_mass_lower hx.le (cavityCount I σ v w)
  have hs : (∑ c, (cavityCount I σ v w c : ℝ)) + 1 ≤ (Δ : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (by rw [cavityCount_sum I σ v w hvw]; exact hd v)
  have hn : 0 ≤ ∑ c, (cavityCount I σ v w c : ℝ) := Finset.sum_nonneg fun c _ => Nat.cast_nonneg _
  have hZ : m + 1 ≤ cavityPartition I x σ v w := by
    change (Fintype.card C : ℝ) - (1 - x) * ∑ c, (cavityCount I σ v w c : ℝ) ≤
      cavityPartition I x σ v w at hb
    nlinarith
  have hnum : cavityWeight I x σ v w c ≤ 1 := pow_le_one₀ hx.le hx1
  change cavityWeight I x σ v w c / cavityPartition I x σ v w ≤ 1 / (m + 1)
  apply (div_le_div_iff₀ (cavityPartition_pos I x hx σ v w) (by linarith)).mpr
  nlinarith

theorem siteCount_update_cavity (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) (t c : C) :
    siteCount I (Function.update σ w t) v c = cavityCount I σ v w c + if t = c then 1 else 0 := by
  have hw : w ∈ I.graph.neighborFinset v := by simpa using hvw
  unfold siteCount cavityCount
  rw [Finset.card_filter, Finset.card_filter,
    ← Finset.sum_erase_add _ _ hw, Function.update_self]
  have he : (∑ u ∈ (I.graph.neighborFinset v).erase w, if Function.update σ w t u = c then 1 else 0) =
      ∑ u ∈ (I.graph.neighborFinset v).erase w, if σ u = c then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  rw [he]
  omega

theorem siteWeight_update_cavity (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) (t c : C) :
    siteWeight I x (Function.update σ w t) v c =
      cavityWeight I x σ v w c * (1 - (1 - x) * colourIndicator t c) := by
  rw [siteWeight, siteCount_update_cavity I σ v w hvw, pow_add]
  unfold cavityWeight
  by_cases hc : t = c
  · subst t
    simp only [if_true, pow_one, colourIndicator, mul_one]
    ring
  · simp only [if_neg hc, pow_zero, colourIndicator, if_neg (Ne.symm hc), mul_zero, sub_zero]

theorem sitePartition_update_cavity (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) (t : C) :
    sitePartition I x (Function.update σ w t) v =
      cavityPartition I x σ v w * (1 - (1 - x) * (cavityLaw I x hx σ v w).w t) := by
  unfold sitePartition
  simp_rw [siteWeight_update_cavity I x σ v w hvw]
  simp only [colourIndicator, mul_sub, mul_one, Finset.sum_sub_distrib,
    mul_ite, mul_zero, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  change cavityPartition I x σ v w - (cavityWeight I x σ v w t - cavityWeight I x σ v w t * x) = _
  unfold cavityLaw
  field_simp [(cavityPartition_pos I x hx σ v w).ne']

theorem siteLaw_update_cavity (hlocal : ∀ σ v, 0 < sitePartition I x σ v)
    (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) (t c : C) :
    (siteLaw I x hx.le hlocal (Function.update σ w t) v).w c =
      (cavityLaw I x hx σ v w).w c * (1 - (1 - x) * colourIndicator t c) /
        (1 - (1 - x) * (cavityLaw I x hx σ v w).w t) := by
  have hz := cavityPartition_pos I x hx σ v w
  have hd : 1 - (1 - x) * (cavityLaw I x hx σ v w).w t ≠ 0 := by
    have h := hlocal (Function.update σ w t) v
    rw [sitePartition_update_cavity I x hx σ v w hvw t] at h
    exact (pos_of_mul_pos_right h hz.le).ne'
  change siteWeight I x (Function.update σ w t) v c / sitePartition I x (Function.update σ w t) v = _
  rw [siteWeight_update_cavity I x σ v w hvw, sitePartition_update_cavity I x hx σ v w hvw]
  change _ = (cavityWeight I x σ v w c / cavityPartition I x σ v w) * _ / _
  field_simp [hz.ne', hd]

end GraphHeatBath
end
end CI2ZF.Appendix.Girth
