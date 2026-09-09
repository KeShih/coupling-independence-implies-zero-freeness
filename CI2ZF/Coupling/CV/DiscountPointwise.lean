import CI2ZF.Coupling.CV.Geometry

/-! Deterministic union-blocker accounting for the geometric metric.
A common singleton change to a fresh colour removes each of its old
blocker incidences exactly once. -/
namespace CI2ZF.Appendix.CV
open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def freeBlockers (I : PinningData V C) (X Y : V → C) (v u : V) : Finset V :=
  (I.graph.neighborFinset u).filter fun s => s ≠ v ∧
    (X s = X v ∨ X s = Y v ∨ Y s = X v ∨ Y s = Y v)

def incidenceDiscount (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V) : ℝ :=
  if X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v then
    (1 - x) * x ^ blockerCount I X Y v u else 0

lemma incidenceDiscount_nonneg (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y : V → C) (v u : V) :
    0 ≤ incidenceDiscount I x X Y v u := by
  unfold incidenceDiscount
  split
  · exact mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg hx.1 _)
  · rfl

lemma freeBlockers_update_fresh (I : PinningData V C) (X Y : V → C) (v u s : V) (c : C)
    (hsv : s ≠ v) (hca : c ≠ X v) (hcb : c ≠ Y v) :
    freeBlockers I (Function.update X s c) (Function.update Y s c) v u =
      (freeBlockers I X Y v u).erase s := by
  classical
  ext t
  by_cases hts : t = s
  · subst t
    simp [freeBlockers, Function.update_of_ne hsv.symm, hca, hcb]
  · simp [freeBlockers, Function.update_of_ne hsv.symm, hts]

lemma blockerCount_update_fresh (I : PinningData V C) (X Y : V → C) (v u s : V) (c : C)
    (hsv : s ≠ v) (hca : c ≠ X v) (hcb : c ≠ Y v)
    (hst : X s = X v ∨ X s = Y v) :
    blockerCount I (Function.update X s c) (Function.update Y s c) v u +
      (if I.graph.Adj u s then 1 else 0) = blockerCount I X Y v u := by
  classical
  have hs := freeBlockers_update_fresh I X Y v u s c hsv hca hcb
  change (freeBlockers I (Function.update X s c) (Function.update Y s c) v u).card +
    (∑ d ∈ Finset.univ.filter (fun d => d = Function.update X s c v ∨ d = Function.update Y s c v),
      I.boundaryCount u d) + _ = _
  rw [hs, Function.update_of_ne hsv.symm, Function.update_of_ne hsv.symm]
  by_cases hadj : I.graph.Adj u s
  · have hm : s ∈ freeBlockers I X Y v u := by
      simp only [freeBlockers, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨hadj, hsv, hst.elim Or.inl (fun hh => Or.inr (Or.inl hh))⟩
    rw [Finset.card_erase_of_mem hm, if_pos hadj]
    have hc := Finset.card_pos.mpr ⟨s, hm⟩
    change (freeBlockers I X Y v u).card - 1 + _ + 1 = (freeBlockers I X Y v u).card + _
    omega
  · have hm : s ∉ freeBlockers I X Y v u := by
      simp only [freeBlockers, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact fun hh => hadj hh.1
    rw [Finset.erase_eq_of_notMem hm, if_neg hadj, add_zero]
    rfl

/-- The exact increment for one pre-existing regular incidence. -/
lemma incidenceDiscount_update_fresh (I : PinningData V C) (x : ℝ) (X Y : V → C)
    (v u s : V) (c : C) (hsv : s ≠ v) (hca : c ≠ X v) (hcb : c ≠ Y v)
    (hst : X s = X v ∨ X s = Y v)
    (hu : X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v) :
    incidenceDiscount I x (Function.update X s c) (Function.update Y s c) v u =
      incidenceDiscount I x X Y v u +
        if I.graph.Adj u s then (1 - x)^2 * x^(blockerCount I X Y v u - 1) else 0 := by
  have hus : u ≠ s := by
    intro hh
    subst u
    exact hst.elim hu.2.1 hu.2.2
  have hreg : Function.update X s c u = Function.update Y s c u ∧
      Function.update X s c u ≠ Function.update X s c v ∧
      Function.update X s c u ≠ Function.update Y s c v := by
    simpa only [Function.update_of_ne hus, Function.update_of_ne hsv.symm] using hu
  unfold incidenceDiscount
  rw [if_pos hu, if_pos hreg]
  have hb := blockerCount_update_fresh I X Y v u s c hsv hca hcb hst
  by_cases hadj : I.graph.Adj u s
  · rw [if_pos hadj] at hb ⊢
    have hm : blockerCount I X Y v u - 1 =
        blockerCount I (Function.update X s c) (Function.update Y s c) v u := by omega
    rw [hm, ← hb, pow_succ]
    ring
  · rw [if_neg hadj] at hb ⊢
    rw [add_zero] at hb
    rw [hb, add_zero]

/-- The fresh gain is indexed by physical blocker incidences, so a single
flip may legitimately increase several different summands. -/
def freshScoreGain (I : PinningData V C) (x : ℝ) (X Y : V → C) (v s : V) : ℝ :=
  ∑ u ∈ I.graph.neighborFinset v,
    if (X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v) ∧ I.graph.Adj u s then
      (1 - x)^2 * x^(blockerCount I X Y v u - 1) else 0

lemma freshScoreGain_nonneg (I : PinningData V C) {x : ℝ}
    (hx : 0 ≤ x) (X Y : V → C) (v s : V) : 0 ≤ freshScoreGain I x X Y v s := by
  apply Finset.sum_nonneg
  intro u _
  split
  · exact mul_nonneg (sq_nonneg _) (pow_nonneg hx _)
  · rfl

/-- The root's full output score retains its input score and all fresh
incidence increments, on each singleton output separately. -/
theorem vertexScore_update_fresh_ge (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y : V → C) (v s : V) (c : C)
    (hsv : s ≠ v) (hca : c ≠ X v) (hcb : c ≠ Y v)
    (hst : X s = X v ∨ X s = Y v) :
    vertexScore I x X Y v + freshScoreGain I x X Y v s ≤
      vertexScore I x (Function.update X s c) (Function.update Y s c) v := by
  change (∑ u ∈ I.graph.neighborFinset v, incidenceDiscount I x X Y v u) + _ ≤
    ∑ u ∈ I.graph.neighborFinset v,
      incidenceDiscount I x (Function.update X s c) (Function.update Y s c) v u
  unfold freshScoreGain
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v
  · rw [incidenceDiscount_update_fresh I x X Y v u s c hsv hca hcb hst hu]
    by_cases hadj : I.graph.Adj u s
    · rw [if_pos ⟨hu, hadj⟩, if_pos hadj]
    · rw [if_neg (fun hh => hadj hh.2), if_neg hadj]
  · simp only [incidenceDiscount, hu, false_and, if_false, zero_add]
    exact incidenceDiscount_nonneg I hx _ _ v u

end
end CI2ZF.Appendix.CV
