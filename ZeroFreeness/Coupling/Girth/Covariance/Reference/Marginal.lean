import ZeroFreeness.Coupling.Girth.Analysis.Product

/-! The actual reference marginal occupancy estimate used by the
girth-five response recursion. The weighted product estimate is applied
to the unary palette, including zero unary coordinates. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
variable {C D : Type*} [Fintype C] [Fintype D]

def logChord (B : ℝ) : ℝ := -Real.log (1 - B) / B

theorem logChord_nonneg {B : ℝ} (hB0 : 0 < B) (hB1 : B < 1) : 0 ≤ logChord B := by
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))) hB0.le

theorem logChord_le {B : ℝ} (hB0 : 0 < B) (hB1 : B < 1) : logChord B ≤ 1 / (1 - B) := by
  have hh := Real.one_sub_inv_le_log_of_pos (sub_pos.mpr hB1)
  apply (div_le_iff₀ hB0).mpr
  change -Real.log (1 - B) ≤ 1 / (1 - B) * B
  have he : 1 / (1 - B) * B = (1 - B)⁻¹ - 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hB1)]
    ring
  rw [he]
  linarith

theorem reference_occupancy (a : C → ℝ) (m : D → C → ℝ) {A B t : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA0 : 0 < A) (hA : A ≤ ∑ c, a c)
    (hB0 : 0 < B) (hB1 : B < 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ B) (hmass : ∀ i, ∑ c, m i c ≤ 1)
    (ht : (Fintype.card D : ℝ) / A ≤ t) (c : C) :
    (Fintype.card D : ℝ) * messageMarginal a m c * (∑ i, m i c) ≤
      t * Real.exp (t * logChord B - 1) := by
  have hθ : 0 ≤ (Fintype.card D : ℝ) / A := by positivity
  have ht0 : 0 ≤ t := hθ.trans ht
  have hℓ := logChord_nonneg hB0 hB1
  have ho := message_occupancy_bound a m (fun _ => B) ha hA0 hA
    (fun _ => ⟨hB0, hB1⟩) hm hmass c
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ho
  have he : Real.exp (-1 + (Fintype.card D : ℝ) * logChord B / A) ≤
      Real.exp (t * logChord B - 1) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right ht hℓ
    calc
      _ = (Fintype.card D : ℝ) / A * logChord B - 1 := by ring
      _ ≤ _ := sub_le_sub_right h 1
  calc
    _ ≤ (Fintype.card D : ℝ) * (Real.exp (-1 + (Fintype.card D : ℝ) * logChord B / A) / A) := by
      simpa only [logChord, mul_assoc] using mul_le_mul_of_nonneg_left ho (Nat.cast_nonneg (Fintype.card D))
    _ = ((Fintype.card D : ℝ) / A) * Real.exp (-1 + (Fintype.card D : ℝ) * logChord B / A) := by ring
    _ ≤ t * Real.exp (t * logChord B - 1) := mul_le_mul ht he (Real.exp_pos _).le ht0

/-- The insertion loss enters once after taking a square root. -/
theorem tilted_reference_occupancy (a : C → ℝ) (r : D → FinDist C) (p : FinDist C)
    {s A B t E : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA0 : 0 < A) (hA : A ≤ ∑ c, a c)
    (hB0 : 0 < B) (hB1 : B < 1) (hr : ∀ i c, s * (r i).w c ≤ B)
    (ht : (Fintype.card D : ℝ) / A ≤ t)
    (hp : ∀ c, p.w c ≤ Real.exp (2 * E) * messageMarginal a (fun i c => s * (r i).w c) c)
    (c : C) :
    s ^ 2 * (Fintype.card D : ℝ) * p.w c * (∑ i, (r i).w c) ≤
      Real.exp (2 * E) * (t * Real.exp (t * logChord B - 1)) := by
  have hsquare : s ^ 2 ≤ s := by nlinarith
  have hsum : 0 ≤ ∑ i, (r i).w c := Finset.sum_nonneg fun i _ => (r i).nonneg c
  have hscale : ∑ i, s * (r i).w c = s * ∑ i, (r i).w c := (Finset.mul_sum ..).symm
  have hm : ∀ i, ∑ c, s * (r i).w c ≤ 1 := by
    intro i
    simpa only [← Finset.mul_sum, (r i).sum_one, mul_one] using hs1
  have ho := reference_occupancy a (fun i c => s * (r i).w c) ha hA0 hA hB0 hB1
    (fun i c => ⟨mul_nonneg hs0 ((r i).nonneg c), hr i c⟩) hm ht c
  have hmult := mul_le_mul_of_nonneg_right (hp c)
    (mul_nonneg (Nat.cast_nonneg (Fintype.card D)) (mul_nonneg hs0 hsum))
  calc
    _ ≤ s * (Fintype.card D : ℝ) * p.w c * (∑ i, (r i).w c) := by
      gcongr
      exact p.nonneg c
    _ ≤ Real.exp (2 * E) * ((Fintype.card D : ℝ) *
        messageMarginal a (fun i c => s * (r i).w c) c * (∑ i, s * (r i).w c)) := by
      rw [hscale]
      nlinarith only [hmult]
    _ ≤ _ := mul_le_mul_of_nonneg_left ho (Real.exp_pos _).le

def referenceResponseCoefficient (E B t : ℝ) : ℝ :=
  Real.exp E * Real.sqrt (t * Real.exp (t * logChord B - 1)) / (1 - B)

theorem referenceResponseCoefficient_sq {E B t : ℝ} (ht : 0 ≤ t) :
    referenceResponseCoefficient E B t ^ 2 =
      Real.exp (2 * E) * (t * Real.exp (t * logChord B - 1)) / (1 - B) ^ 2 := by
  unfold referenceResponseCoefficient
  rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg ht (Real.exp_pos _).le)]
  rw [← Real.exp_nat_mul]
  norm_num

end
end ZeroFreeness.Appendix.Girth
