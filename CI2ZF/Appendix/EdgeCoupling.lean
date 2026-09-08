import CI2ZF.FiniteCoupling

/-!
# The exposure-block coupling in the Edge-Potts appendix

This file constructs the four-row coupling table and verifies both marginals
and its transport cost. It also proves the occurrence-budget arithmetic and
the closed form of the one-label recursion. These are finite transport
lemmas; the countable slot representation and its conditional comparison
estimates are separate mathematical obligations.
-/

namespace CI2ZF.Appendix.Edge

open PottsCI PottsCI.FinDist
open scoped BigOperators

noncomputable section

variable {S T J : Type*} [Fintype S] [Fintype T] [Fintype J]

def exposureBudget (ρ σ : J → ℝ) : ℝ := ∑ j, max (ρ j) (σ j)

lemma exposureBudget_nonneg (ρ σ : J → ℝ) (hρ : ∀ j, 0 ≤ ρ j) :
    0 ≤ exposureBudget ρ σ :=
  Finset.sum_nonneg fun j _ => (hρ j).trans (le_max_left _ _)

lemma exposureBudget_left (ρ σ : J → ℝ) :
    exposureBudget ρ σ = (∑ j, ρ j) + ∑ j, max (σ j - ρ j) 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases le_total (ρ j) (σ j) with h | h
  · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]

lemma exposureBudget_right (ρ σ : J → ℝ) :
    exposureBudget ρ σ = (∑ j, σ j) + ∑ j, max (ρ j - σ j) 0 := by
  have h := exposureBudget_left σ ρ
  simpa [exposureBudget, max_comm] using h

lemma min_add_positive_difference (a b : ℝ) :
    min a b + max (a - b) 0 = a := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

lemma exposure_table_row_identity (ρ σ f : J → ℝ) (u₀ u : ℝ)
    (h : u₀ + ∑ j, ρ j * f j = (1 + ∑ j, ρ j) * u) :
    u₀ + ∑ j, (min (ρ j) (σ j) * f j +
      max (ρ j - σ j) 0 * f j + max (σ j - ρ j) 0 * u) =
      (1 + exposureBudget ρ σ) * u := by
  simp_rw [← add_mul, min_add_positive_difference]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, exposureBudget_left]
  linarith

/-- The four table rows are added as actual coupling matrices. The two
decomposition identities are pointwise equalities of the exposure laws. -/
def exposureCoupling (μ : FinDist S) (ν : FinDist T)
    (μ₀ : FinDist S) (ν₀ : FinDist T)
    (μj : J → FinDist S) (νj : J → FinDist T)
    (ρ σ : J → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (hσ : ∀ j, 0 ≤ σ j)
    (hμ : ∀ x, μ₀.w x + ∑ j, ρ j * (μj j).w x =
      (1 + ∑ j, ρ j) * μ.w x)
    (hν : ∀ y, ν₀.w y + ∑ j, σ j * (νj j).w y =
      (1 + ∑ j, σ j) * ν.w y)
    (π₀ : Coupling μ₀ ν₀) (πm : ∀ j, Coupling (μj j) (νj j))
    (πl : ∀ j, Coupling (μj j) ν) (πr : ∀ j, Coupling μ (νj j)) :
    Coupling μ ν where
  w x y := (π₀.w x y + ∑ j,
    (min (ρ j) (σ j) * (πm j).w x y +
     max (ρ j - σ j) 0 * (πl j).w x y +
     max (σ j - ρ j) 0 * (πr j).w x y)) / (1 + exposureBudget ρ σ)
  nonneg x y := div_nonneg
    (add_nonneg (π₀.nonneg x y) (Finset.sum_nonneg fun j _ =>
      add_nonneg (add_nonneg (mul_nonneg (le_min (hρ j) (hσ j)) ((πm j).nonneg x y))
        (mul_nonneg (le_max_right _ _) ((πl j).nonneg x y)))
        (mul_nonneg (le_max_right _ _) ((πr j).nonneg x y))))
    (by have := exposureBudget_nonneg ρ σ hρ; linarith)
  sum_row x := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, π₀.sum_row, Finset.sum_comm]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Coupling.sum_row]
    have hrow := exposure_table_row_identity ρ σ (fun j => (μj j).w x) _ _ (hμ x)
    simp only [Finset.sum_add_distrib] at hrow
    rw [hrow]
    exact mul_div_cancel_left₀ _ (by have := exposureBudget_nonneg ρ σ hρ; linarith)
  sum_col y := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, π₀.sum_col, Finset.sum_comm]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Coupling.sum_col]
    have hbudget : exposureBudget σ ρ = exposureBudget ρ σ := by
      simp only [exposureBudget, max_comm]
    have hcol := exposure_table_row_identity σ ρ (fun j => (νj j).w y) _ _ (hν y)
    simp only [Finset.sum_add_distrib, min_comm, hbudget] at hcol
    have hcol' : ν₀.w y + (∑ j, min (ρ j) (σ j) * (νj j).w y) +
        (∑ j, max (ρ j - σ j) 0 * ν.w y) +
        (∑ j, max (σ j - ρ j) 0 * (νj j).w y) =
        (1 + exposureBudget ρ σ) * ν.w y := by linarith
    rw [← add_assoc, ← add_assoc, hcol']
    exact mul_div_cancel_left₀ _ (by have := exposureBudget_nonneg ρ σ hρ; linarith)

lemma exposureCoupling_cost (μ : FinDist S) (ν : FinDist T)
    (μ₀ : FinDist S) (ν₀ : FinDist T)
    (μj : J → FinDist S) (νj : J → FinDist T)
    (ρ σ : J → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (hσ : ∀ j, 0 ≤ σ j)
    (hμ : ∀ x, μ₀.w x + ∑ j, ρ j * (μj j).w x =
      (1 + ∑ j, ρ j) * μ.w x)
    (hν : ∀ y, ν₀.w y + ∑ j, σ j * (νj j).w y =
      (1 + ∑ j, σ j) * ν.w y)
    (π₀ : Coupling μ₀ ν₀) (πm : ∀ j, Coupling (μj j) (νj j))
    (πl : ∀ j, Coupling (μj j) ν) (πr : ∀ j, Coupling μ (νj j))
    (d : S → T → ℝ) :
    (exposureCoupling μ ν μ₀ ν₀ μj νj ρ σ hρ hσ hμ hν π₀ πm πl πr).cost d =
      (π₀.cost d + ∑ j,
        (min (ρ j) (σ j) * (πm j).cost d +
        max (ρ j - σ j) 0 * (πl j).cost d +
        max (σ j - ρ j) 0 * (πr j).cost d)) / (1 + exposureBudget ρ σ) := by
  have reorder (f : J → S → T → ℝ) :
      (∑ x, ∑ y, ∑ j, f j x y) = ∑ j, ∑ x, ∑ y, f j x y := by
    calc
      _ = ∑ x, ∑ j, ∑ y, f j x y := by
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold Coupling.cost exposureCoupling
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, add_mul, Finset.sum_mul,
    Finset.sum_add_distrib]
  simp only [reorder, mul_assoc, ← Finset.mul_sum]

lemma exposure_cost_numerator_bound (ρ σ : J → ℝ)
    (hρ : ∀ j, 0 ≤ ρ j) (hσ : ∀ j, 0 ≤ σ j) {t : ℝ} (ht : 0 ≤ t) :
    (∑ j, (min (ρ j) (σ j) * (1 + t) + |ρ j - σ j| * (1 + 2 * t))) ≤
      exposureBudget ρ σ * (1 + 2 * t) := by
  rw [exposureBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rcases le_total (ρ j) (σ j) with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith [mul_nonneg (hρ j) ht]
  · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith [mul_nonneg (hσ j) ht]

lemma exposure_table_weighted_bound (ρ σ cm cl cr : J → ℝ)
    (hρ : ∀ j, 0 ≤ ρ j) (hσ : ∀ j, 0 ≤ σ j) {t : ℝ} (ht : 0 ≤ t)
    (hm : ∀ j, cm j ≤ 1 + t) (hl : ∀ j, cl j ≤ 1 + 2 * t)
    (hr : ∀ j, cr j ≤ 1 + 2 * t) :
    (∑ j, (min (ρ j) (σ j) * cm j + max (ρ j - σ j) 0 * cl j +
      max (σ j - ρ j) 0 * cr j)) ≤ exposureBudget ρ σ * (1 + 2 * t) := by
  calc
    _ ≤ ∑ j, (min (ρ j) (σ j) * (1 + t) + |ρ j - σ j| * (1 + 2 * t)) := by
      apply Finset.sum_le_sum
      intro j _
      have hm' := mul_le_mul_of_nonneg_left (hm j) (le_min (hρ j) (hσ j))
      have hl' := mul_le_mul_of_nonneg_left (hl j) (le_max_right (ρ j - σ j) 0)
      have hr' := mul_le_mul_of_nonneg_left (hr j) (le_max_right (σ j - ρ j) 0)
      have hparts : max (ρ j - σ j) 0 + max (σ j - ρ j) 0 = |ρ j - σ j| := by
        rcases le_total (ρ j) (σ j) with h | h
        · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h),
            abs_of_nonpos (sub_nonpos.mpr h)]
          ring
        · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
            abs_of_nonneg (sub_nonneg.mpr h), add_zero]
      nlinarith [hparts]
    _ ≤ _ := exposure_cost_numerator_bound ρ σ hρ hσ ht

/-- With the three conditional coupling costs supplied, the actual table
coupling has the cost claimed in the appendix. -/
lemma exposureCoupling_cost_le (μ : FinDist S) (ν : FinDist T)
    (μ₀ : FinDist S) (ν₀ : FinDist T)
    (μj : J → FinDist S) (νj : J → FinDist T)
    (ρ σ : J → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (hσ : ∀ j, 0 ≤ σ j)
    (hμ : ∀ x, μ₀.w x + ∑ j, ρ j * (μj j).w x =
      (1 + ∑ j, ρ j) * μ.w x)
    (hν : ∀ y, ν₀.w y + ∑ j, σ j * (νj j).w y =
      (1 + ∑ j, σ j) * ν.w y)
    (π₀ : Coupling μ₀ ν₀) (πm : ∀ j, Coupling (μj j) (νj j))
    (πl : ∀ j, Coupling (μj j) ν) (πr : ∀ j, Coupling μ (νj j))
    (d : S → T → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hzero : π₀.cost d = 0) (hm : ∀ j, (πm j).cost d ≤ 1 + t)
    (hl : ∀ j, (πl j).cost d ≤ 1 + 2 * t)
    (hr : ∀ j, (πr j).cost d ≤ 1 + 2 * t) :
    (exposureCoupling μ ν μ₀ ν₀ μj νj ρ σ hρ hσ hμ hν π₀ πm πl πr).cost d ≤
      exposureBudget ρ σ / (1 + exposureBudget ρ σ) * (1 + 2 * t) := by
  rw [exposureCoupling_cost, hzero, zero_add, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by have := exposureBudget_nonneg ρ σ hρ; linarith)
  exact exposure_table_weighted_bound ρ σ (fun j => (πm j).cost d)
    (fun j => (πl j).cost d) (fun j => (πr j).cost d) hρ hσ ht hm hl hr

lemma occurrence_budget {Δ : ℝ} (_hΔ : 0 ≤ Δ)
    (ρ σ : J → ℝ) (hρ : ∀ j, ρ j ≤ 1 / (Δ + 1))
    (hσ : ∀ j, σ j ≤ 1 / (Δ + 1)) (hcard : Fintype.card J ≤ Δ - 1) :
    exposureBudget ρ σ ≤ (Δ - 1) / (Δ + 1) := by
  calc
    exposureBudget ρ σ ≤ ∑ _ : J, 1 / (Δ + 1) :=
      Finset.sum_le_sum fun j _ => max_le (hρ j) (hσ j)
    _ = (Fintype.card J : ℝ) / (Δ + 1) := by simp [div_eq_mul_inv]
    _ ≤ (Δ - 1) / (Δ + 1) := div_le_div_of_nonneg_right hcard (by linarith)

lemma occurrence_fraction {Δ R : ℝ} (hΔ : 1 ≤ Δ) (hR : 0 ≤ R)
    (hbudget : R ≤ (Δ - 1) / (Δ + 1)) :
    R / (1 + R) ≤ (Δ - 1) / (2 * Δ) := by
  have hd : 0 < Δ := by linarith
  have hdr : 0 < Δ + 1 := by linarith
  have hr : 0 < 1 + R := by linarith
  rw [le_div_iff₀ hdr] at hbudget
  apply (div_le_div_iff₀ hr (by positivity : 0 < 2 * Δ)).mpr
  nlinarith

/-- The exact closed-form upper envelope of the recursive one-label cost. -/
def oneLabelBound (Δ : ℝ) (n : ℕ) : ℝ :=
  (Δ - 1) / 2 * (1 - ((Δ - 1) / Δ) ^ n)

@[simp] lemma oneLabelBound_zero (Δ : ℝ) : oneLabelBound Δ 0 = 0 := by
  simp [oneLabelBound]

lemma oneLabelBound_succ {Δ : ℝ} (hΔ : Δ ≠ 0) (n : ℕ) :
    oneLabelBound Δ (n + 1) = (Δ - 1) / (2 * Δ) * (1 + 2 * oneLabelBound Δ n) := by
  unfold oneLabelBound
  rw [pow_succ]
  field_simp
  ring

lemma oneLabelBound_le {Δ : ℝ} (hΔ : 1 ≤ Δ) (n : ℕ) :
    oneLabelBound Δ n ≤ (Δ - 1) / 2 := by
  have hratio : 0 ≤ (Δ - 1) / Δ := div_nonneg (by linarith) (by linarith)
  have hp := pow_nonneg hratio n
  unfold oneLabelBound
  nlinarith [mul_nonneg (show 0 ≤ (Δ - 1) / 2 by linarith) hp]

lemma one_label_recursion_bound {Δ : ℝ} (hΔ : 1 ≤ Δ) (T : ℕ → ℝ)
    (hzero : T 0 = 0)
    (hstep : ∀ n, T (n + 1) ≤ (Δ - 1) / (2 * Δ) * (1 + 2 * T n))
    (n : ℕ) : T n ≤ oneLabelBound Δ n := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [oneLabelBound_succ (by linarith)]
    exact (hstep n).trans (mul_le_mul_of_nonneg_left (by linarith)
      (div_nonneg (by linarith) (by linarith)))

end
end CI2ZF.Appendix.Edge
