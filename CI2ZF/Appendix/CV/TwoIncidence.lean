import CI2ZF.Appendix.CV.Canonical

/-! Two-incidence canonical sums, with no assumptions on component equality.
The second copy of a repeated component has exactly zero residual allocation. -/
namespace CI2ZF.Appendix.CV.CanonicalMatching
open PottsCI PottsCI.FinDist
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {I A B : Type*} [Fintype I]

lemma sum_two {D : Type*} [AddCommMonoid D] (i₀ i₁ : I)
    (hne : i₀ ≠ i₁) (hall : ∀ i, i = i₀ ∨ i = i₁) (f : I → D) :
    (∑ i, f i) = f i₀ + f i₁ := by
  classical
  have hu : (Finset.univ : Finset I) = {i₀, i₁} := by
    ext i
    simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff] using hall i
  rw [hu, Finset.sum_pair hne]

lemma first_two_left (f : I → A) (i₀ i₁ : I) (hall : ∀ i, i = i₀ ∨ i = i₁)
    (horder : index i₀ ≤ index i₁) : IsFirst f i₀ := by
  intro j _
  rcases hall j with rfl | rfl
  · exact le_rfl
  · exact horder

lemma first_two_right (f : I → A) (i₀ i₁ : I) (hall : ∀ i, i = i₀ ∨ i = i₁)
    (horder : index i₀ < index i₁) : IsFirst f i₁ ↔ f i₀ ≠ f i₁ := by
  constructor
  · intro hfirst heq
    exact (not_le_of_gt horder) (hfirst i₀ heq)
  · intro hne j hj
    rcases hall j with rfl | rfl
    · exact (hne hj).elim
    · exact le_rfl

lemma share_two_left (f : I → A) (r : A → ℝ) (i₀ i₁ : I) (hall : ∀ i, i = i₀ ∨ i = i₁)
    (horder : index i₀ ≤ index i₁) : share f r i₀ = r (f i₀) := by
  exact if_pos (first_two_left f i₀ i₁ hall horder)

lemma share_two_right (f : I → A) (r : A → ℝ) (i₀ i₁ : I) (hall : ∀ i, i = i₀ ∨ i = i₁)
    (horder : index i₀ < index i₁) : share f r i₁ = if f i₀ = f i₁ then 0 else r (f i₁) := by
  unfold share
  rw [first_two_right f i₀ i₁ hall horder]
  by_cases heq : f i₀ = f i₁ <;> simp [heq]

theorem charge_two [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : I → A) (g : I → B) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (r aSize : A → ℝ) (s bSize : B → ℝ) (i₀ i₁ : I)
    (hall : ∀ i, i = i₀ ∨ i = i₁) (horder : index i₀ < index i₁) :
    (∑ a, aSize a * r a) + (∑ b, bSize b * s b) - ∑ i, atIncidence f g r s i =
      aSize (f i₀) * r (f i₀) +
      (if f i₀ = f i₁ then 0 else aSize (f i₁) * r (f i₁)) +
      bSize (g i₀) * s (g i₀) +
      (if g i₀ = g i₁ then 0 else bSize (g i₁) * s (g i₁)) -
      min (r (f i₀)) (s (g i₀)) -
      min (if f i₀ = f i₁ then 0 else r (f i₁)) (if g i₀ = g i₁ then 0 else s (g i₁)) := by
  rw [charge_as_incidence_sum f g hf hg]
  rw [sum_two i₀ i₁ (by intro heq; rw [heq] at horder; exact lt_irrefl _ horder) hall]
  simp only [atIncidence, share_two_left f r i₀ i₁ hall horder.le,
    share_two_left g s i₀ i₁ hall horder.le, share_two_right f r i₀ i₁ hall horder,
    share_two_right g s i₀ i₁ hall horder, mul_ite, mul_zero]
  ring

end
end CI2ZF.Appendix.CV.CanonicalMatching
