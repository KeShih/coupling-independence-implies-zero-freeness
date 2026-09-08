import CI2ZF.Appendix.CVDiscountConstraints
import CI2ZF.Appendix.CVDiscountLoss

/-! Ordered-incidence credits occupy different first coordinates of the
actual output-score double sum. They are disjoint from every retained root score. -/
namespace CI2ZF.Appendix.CV
open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

lemma blockerCount_cross (I : PinningData V C) (X Y : V → C) (v u w : V)
    (hu : regularAt X Y v u) :
    blockerCount I (Function.update X u (Y v)) (Function.update Y u (X v)) u w =
      (targetConstraints I X Y v w).card := by
  classical
  rw [targetConstraints_card]
  unfold blockerCount
  simp only [Function.update_self]
  congr 1
  · congr 1
    ext t
    by_cases htu : t = u
    · subst t
      simp only [Finset.mem_filter, ne_eq, not_true_eq_false, false_and, and_false]
      exact ⟨False.elim, fun hh => regularAt_not_targetAt hu hh.2⟩
    · simp only [Finset.mem_filter, Function.update_of_ne htu, targetAt]
      tauto
  · apply Finset.sum_congr
    · ext c; simp only [Finset.mem_filter]; tauto
    · intro c _; rfl

lemma incidenceDiscount_cross (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u w : V)
    (hu : regularAt X Y v u) (hw : regularAt X Y v w) (hwu : w ≠ u) :
    incidenceDiscount I x (Function.update X u (Y v)) (Function.update Y u (X v)) u w =
      (1 - x) * x^(targetConstraints I X Y v w).card := by
  have hgood : Function.update X u (Y v) w = Function.update Y u (X v) w ∧
      Function.update X u (Y v) w ≠ Function.update X u (Y v) u ∧
      Function.update X u (Y v) w ≠ Function.update Y u (X v) u := by
    simp only [Function.update_of_ne hwu, Function.update_self]
    exact ⟨hw.1, hw.2.2, hw.2.1⟩
  unfold incidenceDiscount
  rw [if_pos hgood, blockerCount_cross I X Y v u w hu]

def crossCreditAt (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V) (U Z : V → C) : ℝ :=
  if regularAt X Y v u ∧ I.graph.Adj v u ∧
      U = Function.update X u (Y v) ∧ Z = Function.update Y u (X v) then
    ∑ w ∈ regularOtherNeighbours I X Y v u, (1 - x) * x^(targetConstraints I X Y v w).card
  else 0

def crossCredit (I : PinningData V C) (x : ℝ) (X Y : V → C) (v : V) (U Z : V → C) : ℝ :=
  ∑ u, crossCreditAt I x X Y v u U Z

lemma crossCreditAt_nonneg (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y : V → C) (v u : V) (U Z : V → C) :
    0 ≤ crossCreditAt I x X Y v u U Z := by
  unfold crossCreditAt
  split
  · exact Finset.sum_nonneg fun w _ => mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg hx.1 _)
  · rfl

/-- One ordered-incidence credit is a subset of the actual score terms
whose disagreement is its first vertex. -/
theorem crossCreditAt_le_output_vertex (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y : V → C) (v u : V) (U Z : V → C)
    (hroot : X v ≠ Y v) :
    crossCreditAt I x X Y v u U Z ≤
      if u ≠ v ∧ U u ≠ Z u then vertexScore I x U Z u else 0 := by
  unfold crossCreditAt
  split_ifs with hm hout
  · obtain ⟨hu, _, rfl, rfl⟩ := hm
    calc
      _ = ∑ w ∈ regularOtherNeighbours I X Y v u,
          incidenceDiscount I x (Function.update X u (Y v)) (Function.update Y u (X v)) u w := by
        apply Finset.sum_congr rfl
        intro w hw
        obtain ⟨hadj, _, hw⟩ := Finset.mem_filter.mp hw
        symm
        exact incidenceDiscount_cross I x X Y v u w hu hw
          (show w ≠ u from (show I.graph.Adj u w by simpa using hadj).ne.symm)
      _ ≤ ∑ w ∈ I.graph.neighborFinset u,
          incidenceDiscount I x (Function.update X u (Y v)) (Function.update Y u (X v)) u w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun w _ _ =>
          incidenceDiscount_nonneg I hx _ _ u w)
      _ = _ := rfl
  · obtain ⟨_, hadj, rfl, rfl⟩ := hm
    exact (hout ⟨hadj.ne.symm, by simpa only [Function.update_self] using hroot.symm⟩).elim
  · exact vertexScore_nonneg I hx U Z u
  · rfl

lemma outputScore_split_root (I : PinningData V C) (x : ℝ) (U Z : V → C) (v : V) :
    outputScore I x U Z = (if U v ≠ Z v then vertexScore I x U Z v else 0) +
      ∑ u, if u ≠ v ∧ U u ≠ Z u then vertexScore I x U Z u else 0 := by
  classical
  have hpoint (u : V) :
      (if U u ≠ Z u then vertexScore I x U Z u else 0) =
      (if u = v then (if U v ≠ Z v then vertexScore I x U Z v else 0) else 0) +
      (if u ≠ v ∧ U u ≠ Z u then vertexScore I x U Z u else 0) := by
    by_cases hu : u = v
    · subst u; simp
    · simp [hu]
  unfold outputScore
  calc
    _ = ∑ u, ((if u = v then (if U v ≠ Z v then vertexScore I x U Z v else 0) else 0) +
        (if u ≠ v ∧ U u ≠ Z u then vertexScore I x U Z u else 0)) :=
      Finset.sum_congr rfl fun u _ => hpoint u
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- All cross credits and the retained root score use disjoint entries of
`outputScore`, on every output pair. -/
theorem retained_root_add_crossCredit_le_outputScore (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y U Z : V → C) (v : V)
    (hroot : X v ≠ Y v) :
    (if rootFixed X Y U Z v then vertexScore I x U Z v else 0) + crossCredit I x X Y v U Z ≤
      outputScore I x U Z := by
  rw [outputScore_split_root I x U Z v]
  apply add_le_add
  · by_cases hf : rootFixed X Y U Z v
    · have hne : U v ≠ Z v := by rw [hf.1, hf.2]; exact hroot
      rw [if_pos hf, if_pos hne]
    · rw [if_neg hf]
      split_ifs
      · exact vertexScore_nonneg I hx U Z v
      · rfl
  · exact Finset.sum_le_sum fun u _ => crossCreditAt_le_output_vertex I hx X Y v u U Z hroot

end
end CI2ZF.Appendix.CV
