import ZeroFreeness.Coupling.Foundations.FinDist

/-! Completion of finite partial couplings. Adapted from the earlier project's
CarlsonVigoda/ComponentCoupling.lean; independent of the flip profile. -/

namespace ZeroFreeness
open Finset PottsCI
noncomputable section
variable {S T : Type*} [Fintype S] [Fintype T]

/-- A nonnegative partial matching whose row and column masses do not exceed
the desired marginals. -/
structure PartialCoupling (mu : FinDist S) (nu : FinDist T) where
  w : S -> T -> ℝ
  nonneg : forall x y, 0 <= w x y
  row_le : forall x, (∑ y, w x y) <= mu.w x
  col_le : forall y, (∑ x, w x y) <= nu.w y

namespace PartialCoupling

variable {mu : FinDist S} {nu : FinDist T}

def mass (kappa : PartialCoupling mu nu) : ℝ :=
  ∑ x, ∑ y, kappa.w x y

def leftResidual (kappa : PartialCoupling mu nu) (x : S) : ℝ :=
  mu.w x - ∑ y, kappa.w x y

def rightResidual (kappa : PartialCoupling mu nu) (y : T) : ℝ :=
  nu.w y - ∑ x, kappa.w x y

lemma leftResidual_nonneg (kappa : PartialCoupling mu nu) (x : S) :
    0 <= kappa.leftResidual x := by
  exact sub_nonneg.mpr (kappa.row_le x)

lemma rightResidual_nonneg (kappa : PartialCoupling mu nu) (y : T) :
    0 <= kappa.rightResidual y := by
  exact sub_nonneg.mpr (kappa.col_le y)

lemma sum_leftResidual (kappa : PartialCoupling mu nu) :
    (∑ x, kappa.leftResidual x) = 1 - kappa.mass := by
  simp only [leftResidual, sum_sub_distrib, mu.sum_one, mass]

lemma sum_rightResidual (kappa : PartialCoupling mu nu) :
    (∑ y, kappa.rightResidual y) = 1 - kappa.mass := by
  simp only [rightResidual, sum_sub_distrib, nu.sum_one, mass]
  rw [sum_comm]

lemma residual_totals_eq (kappa : PartialCoupling mu nu) :
    (∑ x, kappa.leftResidual x) =
      ∑ y, kappa.rightResidual y := by
  rw [kappa.sum_leftResidual, kappa.sum_rightResidual]

lemma residualTotal_nonneg (kappa : PartialCoupling mu nu) :
    0 <= 1 - kappa.mass := by
  rw [← kappa.sum_leftResidual]
  exact sum_nonneg fun x _ => kappa.leftResidual_nonneg x

private lemma leftResidual_eq_zero_of_total (kappa : PartialCoupling mu nu)
    (hzero : 1 - kappa.mass = 0) (x : S) : kappa.leftResidual x = 0 := by
  apply le_antisymm
  · have hsum : (∑ z, kappa.leftResidual z) = 0 := by
      rw [kappa.sum_leftResidual, hzero]
    exact (sum_eq_zero_iff_of_nonneg
      (fun z _ => kappa.leftResidual_nonneg z)).mp hsum x (mem_univ x) |>.le
  · exact kappa.leftResidual_nonneg x

private lemma rightResidual_eq_zero_of_total (kappa : PartialCoupling mu nu)
    (hzero : 1 - kappa.mass = 0) (y : T) : kappa.rightResidual y = 0 := by
  apply le_antisymm
  · have hsum : (∑ z, kappa.rightResidual z) = 0 := by
      rw [kappa.sum_rightResidual, hzero]
    exact (sum_eq_zero_iff_of_nonneg
      (fun z _ => kappa.rightResidual_nonneg z)).mp hsum y (mem_univ y) |>.le
  · exact kappa.rightResidual_nonneg y

/-- Complete the unmatched residual mass by its normalized product.  The
formula also covers zero residual mass: then all residual coordinates vanish.
-/
def complete (kappa : PartialCoupling mu nu) : FinDist.Coupling mu nu where
  w := fun x y => kappa.w x y +
    kappa.leftResidual x * kappa.rightResidual y / (1 - kappa.mass)
  nonneg := fun x y => add_nonneg (kappa.nonneg x y)
    (div_nonneg (mul_nonneg (kappa.leftResidual_nonneg x)
      (kappa.rightResidual_nonneg y)) kappa.residualTotal_nonneg)
  sum_row := fun x => by
    rw [sum_add_distrib]
    by_cases hzero : 1 - kappa.mass = 0
    · have hx := kappa.leftResidual_eq_zero_of_total hzero x
      rw [hzero]
      simp only [div_zero]
      simp
      simp only [leftResidual] at hx
      linarith
    · calc
        (∑ y, kappa.w x y) +
              (∑ y, kappa.leftResidual x * kappa.rightResidual y /
                (1 - kappa.mass))
            = (∑ y, kappa.w x y) + kappa.leftResidual x := by
                rw [← sum_div, ← mul_sum, kappa.sum_rightResidual,
                  mul_div_assoc, div_self hzero, mul_one]
        _ = mu.w x := by simp only [leftResidual]; ring
  sum_col := fun y => by
    rw [sum_add_distrib]
    by_cases hzero : 1 - kappa.mass = 0
    · have hy := kappa.rightResidual_eq_zero_of_total hzero y
      rw [hzero]
      simp only [div_zero]
      simp
      simp only [rightResidual] at hy
      linarith
    · calc
        (∑ x, kappa.w x y) +
              (∑ x, kappa.leftResidual x * kappa.rightResidual y /
                (1 - kappa.mass))
            = (∑ x, kappa.w x y) + kappa.rightResidual y := by
                rw [← sum_div, ← sum_mul, kappa.sum_leftResidual]
                rw [mul_comm, mul_div_assoc, div_self hzero, mul_one]
        _ = nu.w y := by simp only [rightResidual]; ring

theorem exists_completion (kappa : PartialCoupling mu nu) :
    Nonempty (FinDist.Coupling mu nu) :=
  ⟨kappa.complete⟩

def cost (kappa : PartialCoupling mu nu) (d : S -> T -> ℝ) : ℝ :=
  ∑ x, ∑ y, kappa.w x y * d x y

private lemma completionResidualMass (kappa : PartialCoupling mu nu) :
    (∑ x, ∑ y, kappa.leftResidual x * kappa.rightResidual y /
      (1 - kappa.mass)) = 1 - kappa.mass := by
  by_cases hzero : 1 - kappa.mass = 0
  · rw [hzero]
    simp
  · calc
      (∑ x, ∑ y, kappa.leftResidual x * kappa.rightResidual y /
          (1 - kappa.mass)) = ∑ x, kappa.leftResidual x := by
            apply sum_congr rfl
            intro x _
            rw [← sum_div, ← mul_sum, kappa.sum_rightResidual,
              mul_div_assoc, div_self hzero, mul_one]
      _ = 1 - kappa.mass := kappa.sum_leftResidual

lemma complete_cost_le (kappa : PartialCoupling mu nu) (d : S -> T -> ℝ)
    {B : ℝ} (hB : forall x y, d x y <= B) :
    kappa.complete.cost d <= kappa.cost d + B * (1 - kappa.mass) := by
  have hcoeff : forall x y,
      0 <= kappa.leftResidual x * kappa.rightResidual y /
        (1 - kappa.mass) := fun x y =>
    div_nonneg (mul_nonneg (kappa.leftResidual_nonneg x)
      (kappa.rightResidual_nonneg y)) kappa.residualTotal_nonneg
  have hres :
      (∑ x, ∑ y,
        (kappa.leftResidual x * kappa.rightResidual y /
          (1 - kappa.mass)) * d x y) <=
      ∑ x, ∑ y,
        (kappa.leftResidual x * kappa.rightResidual y /
          (1 - kappa.mass)) * B := by
    exact sum_le_sum fun x _ => sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hB x y) (hcoeff x y)
  have hsplit : kappa.complete.cost d = kappa.cost d +
      ∑ x, ∑ y, (kappa.leftResidual x * kappa.rightResidual y /
        (1 - kappa.mass)) * d x y := by
    simp only [FinDist.Coupling.cost, complete, PartialCoupling.cost, add_mul,
      sum_add_distrib]
  rw [hsplit]
  calc
    kappa.cost d +
        (∑ x, ∑ y, (kappa.leftResidual x * kappa.rightResidual y /
          (1 - kappa.mass)) * d x y)
      <= kappa.cost d +
        ∑ x, ∑ y, (kappa.leftResidual x * kappa.rightResidual y /
          (1 - kappa.mass)) * B := add_le_add le_rfl hres
    _ = kappa.cost d + B * (1 - kappa.mass) := by
      congr 1
      calc
        (∑ x, ∑ y, (kappa.leftResidual x * kappa.rightResidual y /
            (1 - kappa.mass)) * B) =
            ∑ x, (∑ y, kappa.leftResidual x * kappa.rightResidual y /
              (1 - kappa.mass)) * B := by
                apply sum_congr rfl
                intro x _
                rw [sum_mul]
        _ = (∑ x, ∑ y, kappa.leftResidual x * kappa.rightResidual y /
              (1 - kappa.mass)) * B := by rw [sum_mul]
        _ = B * (1 - kappa.mass) := by
          rw [kappa.completionResidualMass]
          ring


/-- Completing residual masses preserves separate charges on each side.
This is the bound used when residual component moves are paired across
different colour groups. The cost itself may be a signed Hamming drift. -/
theorem complete_cost_le_separable (kappa : PartialCoupling mu nu)
    (d : S → T → ℝ) (a : S → ℝ) (b : T → ℝ)
    (hd : ∀ x y, d x y ≤ a x + b y) :
    kappa.complete.cost d ≤ kappa.cost d +
      (∑ x, kappa.leftResidual x * a x) +
      (∑ y, kappa.rightResidual y * b y) := by
  let R (x : S) (y : T) :=
    kappa.leftResidual x * kappa.rightResidual y / (1 - kappa.mass)
  have hR (x : S) (y : T) : 0 ≤ R x y :=
    div_nonneg (mul_nonneg (kappa.leftResidual_nonneg x)
      (kappa.rightResidual_nonneg y)) kappa.residualTotal_nonneg
  have hrow (x : S) : ∑ y, R x y = kappa.leftResidual x := by
    have h := kappa.complete.sum_row x
    change (∑ y, (kappa.w x y + R x y)) = mu.w x at h
    rw [sum_add_distrib] at h
    unfold leftResidual
    linarith
  have hcol (y : T) : ∑ x, R x y = kappa.rightResidual y := by
    have h := kappa.complete.sum_col y
    change (∑ x, (kappa.w x y + R x y)) = nu.w y at h
    rw [sum_add_distrib] at h
    unfold rightResidual
    linarith
  have ha : (∑ x, ∑ y, R x y * a x) = ∑ x, kappa.leftResidual x * a x := by
    simp_rw [← sum_mul, hrow]
  have hb : (∑ x, ∑ y, R x y * b y) = ∑ y, kappa.rightResidual y * b y := by
    rw [sum_comm]
    simp_rw [← sum_mul, hcol]
  have hbound : (∑ x, ∑ y, R x y * d x y) ≤
      (∑ x, kappa.leftResidual x * a x) + (∑ y, kappa.rightResidual y * b y) := by
    calc
      _ ≤ ∑ x, ∑ y, R x y * (a x + b y) :=
        sum_le_sum fun x _ => sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hd x y) (hR x y)
      _ = _ := by simp_rw [mul_add, sum_add_distrib]; rw [ha, hb]
  have hsplit : kappa.complete.cost d = kappa.cost d + ∑ x, ∑ y, R x y * d x y := by
    simp only [FinDist.Coupling.cost, complete, PartialCoupling.cost, R, add_mul,
      sum_add_distrib]
  rw [hsplit]
  linarith

end PartialCoupling
end
end ZeroFreeness
