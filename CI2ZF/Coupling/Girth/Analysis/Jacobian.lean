import CI2ZF.Coupling.Girth.Analysis.Covariance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The large-girth transformed matrix factorization

This file proves the Euclidean energy bound for the explicit transformed
matrix in `hg-jacobian-factor`. The bound is dimension-independent and
retains both factors `F₁` and `F₂`. `GirthDifferential` identifies this
matrix with the derivative of the actual potential-coordinate recursion.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C D : Type*} [Fintype C] [Fintype D]

/-- The exact weighted projection identity used in the factorization. -/
theorem weighted_centering_identity (p : FinDist C) (hp : ∀ c, 0 < p.w c)
    (u : C → ℝ) :
    (∑ c, (u c - p.w c * ∑ b, u b) ^ 2 / p.w c) =
      (∑ c, u c ^ 2 / p.w c) - (∑ c, u c) ^ 2 := by
  have hpoint (c : C) : (u c - p.w c * ∑ b, u b) ^ 2 / p.w c =
      u c ^ 2 / p.w c - u c * (2 * ∑ b, u b) + p.w c * (∑ b, u b) ^ 2 := by
    field_simp [(hp c).ne']
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, p.sum_one]
  ring

def potentialDiagonal (p : FinDist C) (c : C) : ℝ :=
  Real.sqrt (p.w c) / (1 - p.w c)

def transposeEnergy (p : FinDist C) (occupancy h : C → ℝ) : ℝ :=
  ∑ c, occupancy c * (potentialDiagonal p c * h c -
    p.w c * ∑ b, potentialDiagonal p b * h b) ^ 2

theorem potentialDiagonal_energy (p : FinDist C) (hp : ∀ c, 0 < p.w c)
    (h : C → ℝ) (c : C) :
    (potentialDiagonal p c * h c) ^ 2 / p.w c = h c ^ 2 / (1 - p.w c) ^ 2 := by
  unfold potentialDiagonal
  rw [mul_pow, div_pow, Real.sq_sqrt (p.nonneg c)]
  field_simp
  exact mul_div_mul_left _ _ (hp c).ne'

/-- The two-factor estimate before introducing spectral norms. -/
theorem transposeEnergy_le (p : FinDist C) (hp : ∀ c, 0 < p.w c)
    (occupancy h : C → ℝ) {F₁ F₂ : ℝ} (hF₂ : 0 ≤ F₂)
    (h₁ : ∀ c, 1 / (1 - p.w c) ^ 2 ≤ F₁)
    (h₂ : ∀ c, p.w c * occupancy c ≤ F₂) :
    transposeEnergy p occupancy h ≤ F₁ * F₂ * ∑ c, h c ^ 2 := by
  let u : C → ℝ := fun c => potentialDiagonal p c * h c
  have hpoint (c : C) : occupancy c * (u c - p.w c * ∑ b, u b) ^ 2 ≤
      F₂ * ((u c - p.w c * ∑ b, u b) ^ 2 / p.w c) := by
    have hr : occupancy c ≤ F₂ / p.w c := (le_div_iff₀ (hp c)).mpr (by simpa [mul_comm] using h₂ c)
    have hmul := mul_le_mul_of_nonneg_right hr (sq_nonneg (u c - p.w c * ∑ b, u b))
    calc
      _ ≤ (F₂ / p.w c) * (u c - p.w c * ∑ b, u b) ^ 2 := hmul
      _ = _ := by ring
  have henergy : (∑ c, u c ^ 2 / p.w c) ≤ F₁ * ∑ c, h c ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    rw [show u c = potentialDiagonal p c * h c from rfl, potentialDiagonal_energy p hp]
    have hb := mul_le_mul_of_nonneg_right (h₁ c) (sq_nonneg (h c))
    convert hb using 1
    ring
  calc
    transposeEnergy p occupancy h ≤ ∑ c, F₂ * ((u c - p.w c * ∑ b, u b) ^ 2 / p.w c) :=
      Finset.sum_le_sum fun c _ => hpoint c
    _ = F₂ * ((∑ c, u c ^ 2 / p.w c) - (∑ c, u c) ^ 2) := by
      rw [← Finset.mul_sum, weighted_centering_identity p hp]
    _ ≤ F₂ * ∑ c, u c ^ 2 / p.w c :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hF₂
    _ ≤ F₂ * (F₁ * ∑ c, h c ^ 2) := mul_le_mul_of_nonneg_left henergy hF₂
    _ = _ := by ring

variable [DecidableEq C]

/-- The explicit transformed derivative block from the appendix. -/
def transformedBlock (p : FinDist C) (m : D → C → ℝ) (i : D) (c b : C) : ℝ :=
  potentialDiagonal p c * (p.w b - if b = c then 1 else 0) * Real.sqrt (m i b)

def blockAction (p : FinDist C) (m h : D → C → ℝ) (c : C) : ℝ :=
  ∑ i, ∑ b, transformedBlock p m i c b * h i b

def blockTranspose (p : FinDist C) (m : D → C → ℝ) (h : C → ℝ) (i : D) (b : C) : ℝ :=
  ∑ c, transformedBlock p m i c b * h c

theorem blockTranspose_formula (p : FinDist C) (m : D → C → ℝ)
    (h : C → ℝ) (i : D) (b : C) :
    blockTranspose p m h i b = Real.sqrt (m i b) *
      (p.w b * ∑ c, potentialDiagonal p c * h c - potentialDiagonal p b * h b) := by
  unfold blockTranspose transformedBlock
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hl : (∑ c, potentialDiagonal p c * p.w b * Real.sqrt (m i b) * h c) =
      Real.sqrt (m i b) * p.w b * ∑ c, potentialDiagonal p c * h c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hl]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem blockTranspose_energy (p : FinDist C) (m : D → C → ℝ)
    (hm : ∀ i c, 0 ≤ m i c) (h : C → ℝ) :
    (∑ i, ∑ b, blockTranspose p m h i b ^ 2) =
      transposeEnergy p (fun c => ∑ i, m i c) h := by
  simp_rw [blockTranspose_formula, mul_pow, Real.sq_sqrt (hm _ _)]
  rw [Finset.sum_comm]
  unfold transposeEnergy
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul]
  ring

/-- The exact adjoint identity for the finite block matrix. -/
theorem block_adjoint_identity (p : FinDist C) (m h : D → C → ℝ) (g : C → ℝ) :
    (∑ c, g c * blockAction p m h c) = ∑ i, ∑ b, h i b * blockTranspose p m g i b := by
  simp only [blockAction, blockTranspose, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ c, ∑ b, g c * (transformedBlock p m i c b * h i b) := Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ c, g c * (transformedBlock p m i c b * h i b) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- The forward Euclidean operator estimate for the full concatenated matrix,
proved from the transpose factorization by finite Cauchy--Schwarz. -/
theorem blockAction_energy_le (p : FinDist C) (hp : ∀ c, 0 < p.w c)
    (m h : D → C → ℝ) (hm : ∀ i c, 0 ≤ m i c)
    {F₁ F₂ : ℝ} (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (h₁ : ∀ c, 1 / (1 - p.w c) ^ 2 ≤ F₁)
    (h₂ : ∀ c, p.w c * (∑ i, m i c) ≤ F₂) :
    (∑ c, blockAction p m h c ^ 2) ≤ F₁ * F₂ * ∑ i, ∑ b, h i b ^ 2 := by
  let y := blockAction p m h
  let Y : ℝ := ∑ c, y c ^ 2
  let H : ℝ := ∑ i, ∑ b, h i b ^ 2
  have hY : 0 ≤ Y := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hH : 0 ≤ H := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hadj : Y = ∑ i, ∑ b, h i b * blockTranspose p m y i b := by
    simpa only [Y, y, pow_two] using block_adjoint_identity p m h y
  have hcs : Y ^ 2 ≤ H * ∑ i, ∑ b, blockTranspose p m y i b ^ 2 := by
    rw [hadj]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (D × C))
      (fun ib => h ib.1 ib.2) (fun ib => blockTranspose p m y ib.1 ib.2)
    simpa only [Fintype.sum_prod_type, H] using hh
  rw [blockTranspose_energy p m hm] at hcs
  have ht := transposeEnergy_le p hp (fun c => ∑ i, m i c) y hF₂ h₁ h₂
  have hmul := mul_le_mul_of_nonneg_left ht hH
  change Y ≤ F₁ * F₂ * H
  by_cases hy0 : Y = 0
  · rw [hy0]
    exact mul_nonneg (mul_nonneg hF₁ hF₂) hH
  · have hypos : 0 < Y := lt_of_le_of_ne hY (Ne.symm hy0)
    have hbound : Y * Y ≤ (F₁ * F₂ * H) * Y := by
      change H * transposeEnergy p (fun c => ∑ i, m i c) y ≤ H * (F₁ * F₂ * Y) at hmul
      change Y ^ 2 ≤ H * transposeEnergy p (fun c => ∑ i, m i c) y at hcs
      nlinarith
    exact (mul_le_mul_iff_left₀ hypos).mp (by simpa [mul_comm] using hbound)

end

end CI2ZF.Appendix.Girth
