import CI2ZF.BoundaryActivation
import CI2ZF.CoinRestriction

/-! Single-occurrence boundary sensitivity for the actual soft Vigoda kernel.
The common random coins are restricted along the exact labelled-constraint
embedding.  Only the new coin can change a hard row, and its mean is `1-x`.
-/

namespace CI2ZF.Potts
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

lemma activated_hardStep_addBoundary_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (ω : (addBoundary I r a).Constraint → Bool) :
    W ham
      (hardStep (activeHardListInstance I (activatedSet I X
        (fun k => ω (boundaryConstraintEmbedding I r a k)))) X)
      (hardStep (activeHardListInstance (addBoundary I r a)
        (activatedSet (addBoundary I r a) X ω)) X) ≤
      if ω (freshBoundaryConstraint I r a) = true then
        1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0 := by
  rw [activeHardListInstance_addBoundary]
  by_cases h : ω (freshBoundaryConstraint I r a) = true ∧ X r ≠ a
  · rw [if_pos h, if_pos h.1]
    exact hardStep_deleteListColour_W_le _ X r a h.2
  · rw [if_neg h, W_self ham_nonneg ham_self]
    by_cases hf : ω (freshBoundaryConstraint I r a) = true
    · rw [if_pos hf]
      positivity
    · rw [if_neg hf]

/-- Adding one actual boundary-count occurrence changes each soft row by
at most `(1-x)/(|V||C|)` in Hamming Wasserstein distance. -/
theorem softVigodaKernel_addBoundary_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softVigodaKernel I x hx0 hx1 X)
      (softVigodaKernel (addBoundary I r a) x hx0 hx1 X) ≤
        (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  let p := commonCoinLaw (K := (addBoundary I r a).Constraint) (1 - x) ht
  let restrict := fun (ω : (addBoundary I r a).Constraint → Bool) (k : I.Constraint) =>
    ω (boundaryConstraintEmbedding I r a k)
  have hold : (commonCoinLaw (K := I.Constraint) (1 - x) ht).bind
      (fun ω => hardStep (activeHardListInstance I (activatedSet I X ω)) X) =
      p.bind (fun ω => hardStep (activeHardListInstance I (activatedSet I X (restrict ω))) X) := by
    rw [← map_commonCoinLaw_embedding (boundaryConstraintEmbedding I r a) (1 - x) ht]
    exact mapLaw_bind _ _ _
  rw [softVigodaKernel_eq_coin_mixture, softVigodaKernel_eq_coin_mixture]
  rw [hold]
  apply (W_bind_diag ham_nonneg p _ _).trans
  calc
    _ ≤ ∑ ω, p.w ω * (if ω (freshBoundaryConstraint I r a) = true then
          1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (activated_hardStep_addBoundary_W_le I r a X ω) (p.nonneg ω)
    _ = (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
      have h := expectReal_product_coordinate
        (fun _ : (addBoundary I r a).Constraint => bernoulliLaw (1 - x) ht)
        (freshBoundaryConstraint I r a)
        (fun b : Bool => if b = true then
          1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0)
      simpa [p, commonCoinLaw, expectReal, bernoulliLaw, div_eq_mul_inv] using h

private def reverseHamCoupling {mu nu : FinDist (V → C)} (gamma : Coupling mu nu) :
    Coupling nu mu where
  w Y X := gamma.w X Y
  nonneg Y X := gamma.nonneg X Y
  sum_row := gamma.sum_col
  sum_col := gamma.sum_row

private lemma reverseHamCoupling_cost {mu nu : FinDist (V → C)} (gamma : Coupling mu nu) :
    (reverseHamCoupling gamma).cost ham = gamma.cost ham := by
  unfold Coupling.cost reverseHamCoupling
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro Y _
  rw [ham_comm Y X]

lemma W_ham_comm (mu nu : FinDist (V → C)) : W ham mu nu = W ham nu mu := by
  apply le_antisymm
  · apply le_W
    intro gamma
    exact (W_le_cost ham_nonneg (reverseHamCoupling gamma)).trans_eq
      (reverseHamCoupling_cost gamma)
  · apply le_W
    intro gamma
    exact (W_le_cost ham_nonneg (reverseHamCoupling gamma)).trans_eq
      (reverseHamCoupling_cost gamma)

/-- The same concrete boundary sensitivity in the child-to-middle direction. -/
theorem softVigodaKernel_addBoundary_W_le_reverse [Nonempty V] [Nonempty C]
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softVigodaKernel (addBoundary I r a) x hx0 hx1 X)
      (softVigodaKernel I x hx0 hx1 X) ≤
        (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  rw [W_ham_comm]
  exact softVigodaKernel_addBoundary_W_le I r a X x hx0 hx1

end
end CI2ZF.Potts
