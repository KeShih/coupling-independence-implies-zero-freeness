import CI2ZF.PartialCoupling
import CI2ZF.HardConditionalCoupling
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max

/-! Canonical first-incidence matching for the CV construction. A repeated
component is allocated only at its first incidence, and its entire residual
capacity remains there. This differs from uniform incidence splitting. -/
namespace CI2ZF.Appendix.CV.CanonicalMatching
open PottsCI PottsCI.FinDist
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {I A B : Type*} [Fintype I]
variable [DecidableEq A] [DecidableEq B]

def index (i : I) : ℕ := (Fintype.equivFin I i).val

lemma index_injective : Function.Injective (index (I := I)) :=
  Fin.val_injective.comp (Fintype.equivFin I).injective

/-- The first incidence carrying this component output. -/
def IsFirst (f : I → A) (i : I) : Prop := ∀ j, f j = f i → index i ≤ index j

lemma first_unique (f : I → A) {i j : I} (hi : IsFirst f i) (hj : IsFirst f j)
    (he : f i = f j) : i = j :=
  index_injective (le_antisymm (hi j he.symm) (hj i he))

lemma first_exists (f : I → A) (a : A) (ha : ∃ i, f i = a) :
    ∃ i, f i = a ∧ IsFirst f i := by
  classical
  let s := Finset.univ.filter fun i => f i = a
  have hs : s.Nonempty := by obtain ⟨i, hi⟩ := ha; exact ⟨i, by simp [s, hi]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s index hs
  have hia : f i = a := (Finset.mem_filter.mp hi).2
  refine ⟨i, hia, ?_⟩
  intro j hj
  exact hmin j (by simp [s, hj, hia])

def share (f : I → A) (r : A → ℝ) (i : I) : ℝ := if IsFirst f i then r (f i) else 0

def atIncidence (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (i : I) : ℝ :=
  min (share f r i) (share g s i)

def matrix (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (a : A) (b : B) : ℝ :=
  ∑ i, if f i = a ∧ g i = b then atIncidence f g r s i else 0

lemma share_nonneg (f : I → A) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a) (i : I) :
    0 ≤ share f r i := by
  unfold share
  split
  · exact hr _
  · rfl

lemma atIncidence_nonneg (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b) (i : I) :
    0 ≤ atIncidence f g r s i :=
  le_min (share_nonneg f r hr i) (share_nonneg g s hs i)

lemma matrix_nonneg (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b) (a : A) (b : B) :
    0 ≤ matrix f g r s a b := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact atIncidence_nonneg f g r s hr hs i
  · exact le_rfl

lemma matrix_row [Fintype B] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (a : A) :
    (∑ b, matrix f g r s a b) = ∑ i, if f i = a then atIncidence f g r s i else 0 := by
  unfold matrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i = a <;> simp [h]

lemma matrix_col [Fintype A] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (b : B) :
    (∑ a, matrix f g r s a b) = ∑ i, if g i = b then atIncidence f g r s i else 0 := by
  unfold matrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : g i = b <;> simp [h]

lemma sum_share_fibre (f : I → A) (r : A → ℝ) (a : A) :
    (∑ i, if f i = a then share f r i else 0) = if ∃ i, f i = a then r a else 0 := by
  by_cases ha : ∃ i, f i = a
  · obtain ⟨i, hi, hfirst⟩ := first_exists f a ha
    rw [if_pos ha, Finset.sum_eq_single i]
    · simp [share, hi, hfirst]
    · intro j _ hji
      by_cases hj : f j = a
      · have hnot : ¬ IsFirst f j := fun h => hji (first_unique f h hfirst (hj.trans hi.symm))
        simp [share, hj, hnot]
      · simp [hj]
    · simp
  · have hnone (i : I) : f i ≠ a := fun h => ha ⟨i, h⟩
    simp [hnone]

lemma sum_share_fibre_le (f : I → A) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a) (a : A) :
    (∑ i, if f i = a then share f r i else 0) ≤ r a := by
  rw [sum_share_fibre]
  split
  · rfl
  · exact hr a

lemma matrix_row_le [Fintype B] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (a : A) : (∑ b, matrix f g r s a b) ≤ r a := by
  rw [matrix_row]
  calc
    (∑ i, if f i = a then atIncidence f g r s i else 0) ≤
        ∑ i, if f i = a then share f r i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    _ ≤ r a := sum_share_fibre_le f r hr a

lemma matrix_col_le [Fintype A] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hs : ∀ b, 0 ≤ s b) (b : B) : (∑ a, matrix f g r s a b) ≤ s b := by
  rw [matrix_col]
  calc
    (∑ i, if g i = b then atIncidence f g r s i else 0) ≤
        ∑ i, if g i = b then share g s i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact min_le_right _ _
      · exact le_rfl
    _ ≤ s b := sum_share_fibre_le g s hs b

/-- The incidence allocation as an actual partial coupling, whenever the
available residual capacities fit within the desired marginal laws. -/
def partialCoupling [Fintype A] [Fintype B] (μ : FinDist A) (ν : FinDist B)
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b)
    (hrμ : ∀ a, r a ≤ μ.w a) (hsν : ∀ b, s b ≤ ν.w b) : PartialCoupling μ ν where
  w := matrix f g r s
  nonneg := matrix_nonneg f g r s hr hs
  row_le a := (matrix_row_le f g r s hr a).trans (hrμ a)
  col_le b := (matrix_col_le f g r s hs b).trans (hsν b)

lemma total_matrix_mass [Fintype A] [Fintype B]
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) :
    (∑ a, ∑ b, matrix f g r s a b) = ∑ i, atIncidence f g r s i := by
  simp_rw [matrix_row]
  rw [Finset.sum_comm]
  simp

/-- A matrix entry may collect several incidences. Its cost is exactly the
sum of the costs of those incidences, so repeated component pairs are safe. -/
lemma matrix_weighted_sum [Fintype A] [Fintype B]
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (d : A → B → ℝ) :
    (∑ a, ∑ b, matrix f g r s a b * d a b) =
      ∑ i, atIncidence f g r s i * d (f i) (g i) := by
  simp_rw [matrix, Finset.sum_mul, ite_mul, zero_mul]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_and]
  simp

/-- Complete the actual incidence matrix to a coupling. Any saving proved
for each matched component pair survives the product completion exactly. -/
theorem complete_cost_le_charge_sub_saving [Fintype A] [Fintype B]
    (μ : FinDist A) (ν : FinDist B)
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b)
    (hrμ : ∀ a, r a ≤ μ.w a) (hsν : ∀ b, s b ≤ ν.w b)
    (d : A → B → ℝ) (aCharge : A → ℝ) (bCharge : B → ℝ) (saving : I → ℝ)
    (hd : ∀ a b, d a b ≤ aCharge a + bCharge b)
    (hmatch : ∀ i, d (f i) (g i) ≤ aCharge (f i) + bCharge (g i) - saving i) :
    (partialCoupling μ ν f g r s hr hs hrμ hsν).complete.cost d ≤
      (∑ a, μ.w a * aCharge a) + (∑ b, ν.w b * bCharge b) -
        ∑ i, atIncidence f g r s i * saving i := by
  let κ := partialCoupling μ ν f g r s hr hs hrμ hsν
  have hκcost (c : A → B → ℝ) : κ.cost c =
      ∑ i, atIncidence f g r s i * c (f i) (g i) :=
    matrix_weighted_sum f g r s c
  have hmatchCost : κ.cost d ≤ κ.cost (fun a b => aCharge a + bCharge b) -
      ∑ i, atIncidence f g r s i * saving i := by
    rw [hκcost, hκcost, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_sub] using
      mul_le_mul_of_nonneg_left (hmatch i) (atIncidence_nonneg f g r s hr hs i)
  have haccount : κ.cost (fun a b => aCharge a + bCharge b) +
      (∑ a, κ.leftResidual a * aCharge a) +
      (∑ b, κ.rightResidual b * bCharge b) =
      (∑ a, μ.w a * aCharge a) + (∑ b, ν.w b * bCharge b) := by
    have hleft : (∑ a, ∑ b, κ.w a b * aCharge a) =
        ∑ a, (∑ b, κ.w a b) * aCharge a := by simp_rw [Finset.sum_mul]
    have hright : (∑ a, ∑ b, κ.w a b * bCharge b) =
        ∑ b, (∑ a, κ.w a b) * bCharge b := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    simp only [PartialCoupling.cost, mul_add, Finset.sum_add_distrib,
      PartialCoupling.leftResidual, PartialCoupling.rightResidual,
      sub_mul, Finset.sum_sub_distrib]
    rw [hleft, hright]
    ring
  have hcomplete := κ.complete_cost_le_separable d aCharge bCharge hd
  change κ.complete.cost d ≤ _
  linarith

lemma sum_share [Fintype A] (f : I → A) (hf : Function.Surjective f) (r : A → ℝ) :
    (∑ i, share f r i) = ∑ a, r a := by
  calc
    (∑ i, share f r i) = ∑ i, ∑ a, if f i = a then share f r i else 0 := by simp
    _ = ∑ a, ∑ i, if f i = a then share f r i else 0 := Finset.sum_comm
    _ = ∑ a, r a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sum_share_fibre, if_pos (hf a)]

lemma sum_weighted_share [Fintype A] (f : I → A) (hf : Function.Surjective f)
    (r w : A → ℝ) : (∑ i, w (f i) * share f r i) = ∑ a, w a * r a := by
  have h := sum_share f hf (fun a => w a * r a)
  simpa only [share, mul_ite, mul_zero] using h

/-- Exactly the canonical residual terms of the CV record, including one
copy of each distinct component and one saving per same-incidence match. -/
theorem charge_as_incidence_sum [Fintype A] [Fintype B] (f : I → A) (g : I → B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (r aSize : A → ℝ) (s bSize : B → ℝ) :
    (∑ a, aSize a * r a) + (∑ b, bSize b * s b) -
        (∑ i, atIncidence f g r s i) =
      ∑ i, (aSize (f i) * share f r i + bSize (g i) * share g s i -
        atIncidence f g r s i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_weighted_share f hf, sum_weighted_share g hg]

end
end CI2ZF.Appendix.CV.CanonicalMatching
