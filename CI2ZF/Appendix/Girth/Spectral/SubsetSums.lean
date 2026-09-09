import CI2ZF.Appendix.Girth.Analysis.Entropy
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Exact subset sums and their first-moment bounds, used when the
orthogonal Hoeffding components are recombined. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {D : Type*}

theorem subset_power_sum (J : Finset D) (ω : ℝ) :
    (∑ I ∈ J.powerset, ω ^ I.card) = (1 + ω) ^ J.card := by
  have h := Finset.prod_one_add (f := fun _ : D => ω) J
  simpa only [Finset.prod_const] using h.symm

theorem subset_first_moment (J : Finset D) (ω : ℝ) :
    (∑ I ∈ J.powerset, (I.card : ℝ) * ω ^ (I.card - 1)) =
      (J.card : ℝ) * (1 + ω) ^ (J.card - 1) := by
  have hleft := HasDerivAt.sum (u := J.powerset) (fun I _ => hasDerivAt_pow I.card ω)
  have hright := ((hasDerivAt_id ω).const_add 1).pow J.card
  have he : (∑ I ∈ J.powerset, fun w : ℝ => w ^ I.card) = (fun w => (1 + w) ^ J.card) := by
    funext w
    simpa only [Finset.sum_apply] using subset_power_sum J w
  rw [he] at hleft
  simpa only [mul_one, id_eq] using hleft.unique hright

/-- Charging a nonempty subset to one of its members costs no more
than its cardinality, giving the exact first derivative of `(1+ω)^d`. -/
theorem nonempty_subset_sum_le (J : Finset D) {ω : ℝ} (hω : 0 ≤ ω) :
    (∑ I ∈ J.powerset, if I.Nonempty then ω ^ (I.card - 1) else 0) ≤
      (J.card : ℝ) * (1 + ω) ^ (J.card - 1) := by
  rw [← subset_first_moment]
  apply Finset.sum_le_sum
  intro I _
  by_cases hI : I.Nonempty
  · rw [if_pos hI]
    have hc : (1 : ℝ) ≤ I.card := by exact_mod_cast hI.card_pos
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (pow_nonneg hω _)
  · simp only [if_neg hI]
    positivity

/-- For a fixed distinguished leaf, the factor `|I|` is at most twice
the number of remaining leaves whenever `|I|≥2`. -/
theorem singleton_subset_sum_le (J : Finset D) {ω : ℝ} (hω : 0 ≤ ω) :
    (∑ I ∈ J.powerset, if I.Nonempty then ((I.card : ℝ) + 1) * ω ^ (I.card - 1) else 0) ≤
      2 * (J.card : ℝ) * (1 + ω) ^ (J.card - 1) := by
  have hb : (∑ I ∈ J.powerset, if I.Nonempty then ((I.card : ℝ) + 1) * ω ^ (I.card - 1) else 0) ≤
      ∑ I ∈ J.powerset, 2 * ((I.card : ℝ) * ω ^ (I.card - 1)) := by
    apply Finset.sum_le_sum
    intro I _
    by_cases hI : I.Nonempty
    · rw [if_pos hI]
      have hc : (1 : ℝ) ≤ I.card := by exact_mod_cast hI.card_pos
      have hp := mul_le_mul_of_nonneg_right (show (I.card : ℝ) + 1 ≤ 2 * I.card by linarith)
        (pow_nonneg hω (I.card - 1))
      nlinarith
    · simp only [if_neg hI]
      positivity
  rw [← Finset.mul_sum, subset_first_moment] at hb
  simpa only [mul_assoc] using hb

theorem marked_subset_sum (A : Finset D) {i : D} (hi : i ∈ A) (ω : ℝ) :
    (∑ J ∈ A.powerset, if i ∈ J ∧ 2 ≤ J.card then (J.card : ℝ) * ω ^ (J.card - 2) else 0) =
      ∑ K ∈ (A.erase i).powerset,
        if K.Nonempty then ((K.card : ℝ) + 1) * ω ^ (K.card - 1) else 0 := by
  conv_lhs => rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i A)]
  have hfirst : (∑ J ∈ (A.erase i).powerset,
      if i ∈ J ∧ 2 ≤ J.card then (J.card : ℝ) * ω ^ (J.card - 2) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro J hJ
    have hn : i ∉ J := fun h => Finset.notMem_erase i A ((Finset.mem_powerset.mp hJ) h)
    simp only [hn, false_and, ite_false]
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro K hK
  have hn : i ∉ K := fun h => Finset.notMem_erase i A ((Finset.mem_powerset.mp hK) h)
  rw [Finset.card_insert_of_notMem hn]
  by_cases hne : K.Nonempty
  · have hncard : 2 ≤ K.card + 1 := by have h := hne.card_pos; omega
    have he : K.card + 1 - 2 = K.card - 1 := by omega
    simp only [Finset.mem_insert_self, hncard, and_self, ite_true, hne, Nat.cast_add, Nat.cast_one, he]
  · have hempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst K
    simp

theorem marked_subset_sum_le (A : Finset D) {i : D} (hi : i ∈ A) {ω : ℝ} (hω : 0 ≤ ω) :
    (∑ J ∈ A.powerset, if i ∈ J ∧ 2 ≤ J.card then (J.card : ℝ) * ω ^ (J.card - 2) else 0) ≤
      2 * ((A.card - 1 : ℕ) : ℝ) * (1 + ω) ^ (A.card - 2) := by
  rw [marked_subset_sum A hi]
  have hb := singleton_subset_sum_le (A.erase i) hω
  have he : (A.erase i).card - 1 = A.card - 2 := by rw [Finset.card_erase_of_mem hi]; omega
  rw [he, Finset.card_erase_of_mem hi] at hb
  exact hb

/-- Recombining marked components counts each leaf energy with the same
uniform coefficient, regardless of which subsets contain that leaf. -/
theorem weighted_marked_subset_sum_le (A : Finset D) {ω : ℝ} (hω : 0 ≤ ω)
    (E : D → ℝ) (hE : ∀ i ∈ A, 0 ≤ E i) :
    (∑ J ∈ A.powerset, if 2 ≤ J.card then
      (J.card : ℝ) * ω ^ (J.card - 2) * ∑ i ∈ J, E i else 0) ≤
      (2 * ((A.card - 1 : ℕ) : ℝ) * (1 + ω) ^ (A.card - 2)) * ∑ i ∈ A, E i := by
  have he : (∑ J ∈ A.powerset, if 2 ≤ J.card then
      (J.card : ℝ) * ω ^ (J.card - 2) * ∑ i ∈ J, E i else 0) =
      ∑ i ∈ A, E i * ∑ J ∈ A.powerset,
        (if i ∈ J ∧ 2 ≤ J.card then (J.card : ℝ) * ω ^ (J.card - 2) else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : 2 ≤ J.card
    · simp only [hj, ite_true, and_true, mul_ite, mul_zero, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hJ)]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [hj, and_false, ite_false, mul_zero, Finset.sum_const_zero]
  rw [he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb := mul_le_mul_of_nonneg_left (marked_subset_sum_le A hi hω) (hE i hi)
  simpa only [mul_comm] using hb

/-- First-order expansion of a product of affine factors. The two exact
derivative formulas avoid any combinatorial multiplicity assumption. -/
theorem marked_product_expansion (A : Finset D) (ξ f : D → ℝ) :
    (∑ i ∈ A, f i * ∏ j ∈ A.erase i, (1 + ξ j)) =
      ∑ J ∈ A.powerset, ∑ i ∈ J, f i * ∏ j ∈ J.erase i, ξ j := by
  have hleft := HasDerivAt.fun_finsetProd (u := A) (fun i _ =>
    ((hasDerivAt_id (0 : ℝ)).mul_const (f i)).const_add (1 + ξ i))
  have hright := HasDerivAt.sum (u := A.powerset) (fun J _ =>
    HasDerivAt.fun_finsetProd (u := J) (fun i _ =>
      ((hasDerivAt_id (0 : ℝ)).mul_const (f i)).const_add (ξ i)))
  have he : (fun w : ℝ => ∏ i ∈ A, (1 + ξ i + w * f i)) =
      (∑ J ∈ A.powerset, fun w : ℝ => ∏ i ∈ J, (ξ i + w * f i)) := by
    funext w
    simp only [Finset.sum_apply]
    have h := Finset.prod_one_add (f := fun i => ξ i + w * f i) A
    simpa only [← add_assoc] using h
  have hleft' : HasDerivAt (fun w : ℝ => ∏ i ∈ A, (1 + ξ i + w * f i))
      (∑ i ∈ A, f i * ∏ j ∈ A.erase i, (1 + ξ j)) 0 := by
    simpa only [id_eq, zero_mul, mul_zero, add_zero, mul_one, smul_eq_mul, mul_comm] using hleft
  have hright' : HasDerivAt (∑ J ∈ A.powerset, fun w : ℝ => ∏ i ∈ J, (ξ i + w * f i))
      (∑ J ∈ A.powerset, ∑ i ∈ J, f i * ∏ j ∈ J.erase i, ξ j) 0 := by
    simpa only [id_eq, zero_mul, mul_zero, add_zero, mul_one, smul_eq_mul, mul_comm] using hright
  rw [he] at hleft'
  exact hleft'.unique hright'

end

end CI2ZF.Appendix.Girth
