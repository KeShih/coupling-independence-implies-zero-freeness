import CI2ZF.Coupling.CV.DiscountPointwise

/-! Pointwise loss accounting for the input root discount. Root, endpoint,
and newly created neighbour blockers are charged separately. -/
namespace CI2ZF.Appendix.CV
open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def rootFixed (X Y U Z : V → C) (v : V) : Prop := U v = X v ∧ Z v = Y v

def badAt (X Y U Z : V → C) (v u : V) : Prop :=
  ¬ (U u = Z u ∧ U u ≠ X v ∧ U u ≠ Y v)

def regularOtherNeighbours (I : PinningData V C) (X Y : V → C) (v u : V) : Finset V :=
  (I.graph.neighborFinset u).filter fun w => w ≠ v ∧
    X w = Y w ∧ X w ≠ X v ∧ X w ≠ Y v

def newTargetCount (I : PinningData V C) (X Y U Z : V → C) (v u : V) : ℕ :=
  ((regularOtherNeighbours I X Y v u).filter fun w => badAt X Y U Z v w).card

lemma blockerCount_le_add_newTargetCount (I : PinningData V C) (X Y U Z : V → C)
    (v u : V) (hfixed : rootFixed X Y U Z v)
    (hagree : ∀ w, w ≠ v → X w = Y w) :
    blockerCount I U Z v u ≤ blockerCount I X Y v u + newTargetCount I X Y U Z v u := by
  classical
  have hsub : freeBlockers I U Z v u ⊆ freeBlockers I X Y v u ∪
      ((regularOtherNeighbours I X Y v u).filter fun w => badAt X Y U Z v w) := by
    intro w hw
    obtain ⟨hadj, hwv, htarget⟩ := Finset.mem_filter.mp hw
    by_cases hold : w ∈ freeBlockers I X Y v u
    · exact Finset.mem_union_left _ hold
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      have hXw : X w ≠ X v ∧ X w ≠ Y v := by
        constructor
        · intro hh; exact hold (Finset.mem_filter.mpr ⟨hadj, hwv, Or.inl hh⟩)
        · intro hh; exact hold (Finset.mem_filter.mpr ⟨hadj, hwv, Or.inr (Or.inl hh)⟩)
      refine ⟨Finset.mem_filter.mpr ⟨hadj, hwv, hagree w hwv, hXw⟩, ?_⟩
      intro hgood
      rw [hfixed.1, hfixed.2] at htarget
      rcases htarget with ht | ht | ht | ht
      · exact hgood.2.1 ht
      · exact hgood.2.2 ht
      · exact hgood.2.1 (hgood.1.trans ht)
      · exact hgood.2.2 (hgood.1.trans ht)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  unfold blockerCount
  change (freeBlockers I U Z v u).card + _ ≤ (freeBlockers I X Y v u).card + _ + _
  rw [hfixed.1, hfixed.2]
  unfold newTargetCount
  omega

lemma power_decrease_le (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (old new added : ℕ)
    (hcount : new ≤ old + added) :
    (1 - x) * x^old - (1 - x) * x^new ≤
      ((1 - x) * x^old) * (1 - x) * added := by
  have hp : x^(old + added) ≤ x^new := pow_le_pow_of_le_one hx.1 hx.2 hcount
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ x - 1 by linarith [hx.1]) added
  simp only [add_sub_cancel] at hb
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg hx.1 old))
  have hm' := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hx.2)
  rw [pow_add] at hm'
  nlinarith

/-- Conservative loss charged to one original root-neighbour discount. -/
def discountLoss (I : PinningData V C) (x : ℝ) (X Y U Z : V → C) (v u : V) : ℝ :=
  (if rootFixed X Y U Z v then 0 else incidenceDiscount I x X Y v u) +
    (if rootFixed X Y U Z v ∧ badAt X Y U Z v u then incidenceDiscount I x X Y v u else 0) +
    (if rootFixed X Y U Z v then
      incidenceDiscount I x X Y v u * (1 - x) * newTargetCount I X Y U Z v u else 0)

lemma discountLoss_nonneg (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y U Z : V → C) (v u : V) :
    0 ≤ discountLoss I x X Y U Z v u := by
  have hs := incidenceDiscount_nonneg I hx X Y v u
  have ht : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  unfold discountLoss
  split_ifs <;> positivity

/-- If the root remains a disagreement, its output incidence retains the
input incidence after the explicit target-loss charges. -/
theorem incidenceDiscount_loss_le (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y U Z : V → C) (v u : V)
    (hagree : ∀ w, w ≠ v → X w = Y w) :
    incidenceDiscount I x X Y v u - discountLoss I x X Y U Z v u ≤
      if rootFixed X Y U Z v then incidenceDiscount I x U Z v u else 0 := by
  have hs := incidenceDiscount_nonneg I hx X Y v u
  have ht : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  by_cases hf : rootFixed X Y U Z v
  · rw [if_pos hf]
    by_cases hb : badAt X Y U Z v u
    · have hout := incidenceDiscount_nonneg I hx U Z v u
      simp only [discountLoss, hf, hb, and_self, if_true, zero_add]
      have hn : 0 ≤ incidenceDiscount I x X Y v u * (1 - x) * newTargetCount I X Y U Z v u := by
        positivity
      linarith
    · have hgood := not_not.mp hb
      have hout : U u = Z u ∧ U u ≠ U v ∧ U u ≠ Z v := by
        simpa only [hf.1, hf.2] using hgood
      by_cases hi : X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v
      · simp only [discountLoss, if_pos hf, and_iff_right hf, if_neg hb, add_zero, zero_add]
        simp only [incidenceDiscount, if_pos hi, if_pos hout]
        have hp := power_decrease_le x hx (blockerCount I X Y v u)
          (blockerCount I U Z v u) (newTargetCount I X Y U Z v u)
          (blockerCount_le_add_newTargetCount I X Y U Z v u hf hagree)
        linarith
      · have hh : incidenceDiscount I x X Y v u = 0 := if_neg hi
        simp only [discountLoss, hh, zero_mul, ite_self, add_zero, sub_zero]
        exact incidenceDiscount_nonneg I hx U Z v u
  · simp [discountLoss, hf]

/-- Summing the root-incidence charges is a true pointwise bound for the
root portion of the full output-score double sum. -/
theorem root_score_loss_le (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y U Z : V → C) (v : V)
    (hagree : ∀ w, w ≠ v → X w = Y w) :
    vertexScore I x X Y v - (∑ u ∈ I.graph.neighborFinset v, discountLoss I x X Y U Z v u) ≤
      if rootFixed X Y U Z v then vertexScore I x U Z v else 0 := by
  change (∑ u ∈ I.graph.neighborFinset v, incidenceDiscount I x X Y v u) - _ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ u ∈ I.graph.neighborFinset v,
      if rootFixed X Y U Z v then incidenceDiscount I x U Z v u else 0 :=
        Finset.sum_le_sum fun u _ => incidenceDiscount_loss_le I hx X Y U Z v u hagree
    _ = _ := by by_cases hf : rootFixed X Y U Z v <;> simp [hf, vertexScore, incidenceDiscount]

end
end CI2ZF.Appendix.CV
