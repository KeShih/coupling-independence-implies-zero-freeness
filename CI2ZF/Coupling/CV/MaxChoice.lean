import CI2ZF.Coupling.CV.TwoFamily

/-! Existence and validity of synchronized maximum-component indices for
the two-incidence certificate. No permitted-choice assumption is postulated. -/
namespace CI2ZF.Appendix.CV
attribute [local instance] Classical.propDecidable
noncomputable section

lemma permitted_exists (a₀ a₁ b₀ b₁ : Branch) :
    ∃ i j : Bool, permitted a₀ a₁ b₀ b₁ i j = true := by
  by_cases hc₀ : branchSize a₁ ≤ branchSize a₀ ∧ branchSize b₁ ≤ branchSize b₀
  · exact ⟨false, false, by simp [permitted, hc₀.1, hc₀.2]⟩
  by_cases hc₁ : branchSize a₀ ≤ branchSize a₁ ∧ branchSize b₀ ≤ branchSize b₁
  · exact ⟨true, true, by simp [permitted, hc₁.1, hc₁.2]⟩
  by_cases ha : branchSize a₀ ≤ branchSize a₁
  · have hb : branchSize b₁ ≤ branchSize b₀ := by omega
    have han : ¬ branchSize a₁ ≤ branchSize a₀ := by omega
    have hbn : ¬ branchSize b₀ ≤ branchSize b₁ := by omega
    exact ⟨true, false, by simp [permitted, ha, hb, han, hbn]⟩
  · have hb : branchSize b₀ ≤ branchSize b₁ := by omega
    have ha' : branchSize a₁ ≤ branchSize a₀ := by omega
    have hbn : ¬ branchSize b₁ ≤ branchSize b₀ := by omega
    exact ⟨false, true, by simp [permitted, ha, ha', hb, hbn]⟩

lemma permitted_left_max {a₀ a₁ b₀ b₁ : Branch} {i j : Bool}
    (hp : permitted a₀ a₁ b₀ b₁ i j = true) :
    if i then branchSize a₀ ≤ branchSize a₁ else branchSize a₁ ≤ branchSize a₀ := by
  cases i <;> cases j <;> simp only [permitted, Bool.false_eq_true, if_false, if_true,
    Bool.and_eq_true, decide_eq_true_eq] at hp ⊢ <;> exact hp.1.1

lemma permitted_right_max {a₀ a₁ b₀ b₁ : Branch} {i j : Bool}
    (hp : permitted a₀ a₁ b₀ b₁ i j = true) :
    if j then branchSize b₀ ≤ branchSize b₁ else branchSize b₁ ≤ branchSize b₀ := by
  cases i <;> cases j <;> simp only [permitted, Bool.false_eq_true, if_false, if_true,
    Bool.and_eq_true, decide_eq_true_eq] at hp ⊢ <;> exact hp.1.2

/-- A zero repeated-component marker cannot be selected over a positive first branch. -/
lemma permitted_left_not_zero {a₀ a₁ b₀ b₁ : Branch} {i j : Bool}
    (hp : permitted a₀ a₁ b₀ b₁ i j = true) (hpos : 0 < branchSize a₀) :
    i = true → branchSize a₁ ≠ 0 := by
  intro hi hz
  have hm := permitted_left_max hp
  simp only [hi, if_true] at hm
  omega

lemma permitted_right_not_zero {a₀ a₁ b₀ b₁ : Branch} {i j : Bool}
    (hp : permitted a₀ a₁ b₀ b₁ i j = true) (hpos : 0 < branchSize b₀) :
    j = true → branchSize b₁ ≠ 0 := by
  intro hj hz
  have hm := permitted_right_max hp
  simp only [hj, if_true] at hm
  omega

end
end CI2ZF.Appendix.CV
