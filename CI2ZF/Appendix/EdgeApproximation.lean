import CI2ZF.PottsModel
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Finite polynomial approximations to the slot law

The deformed binomial polynomials have coefficients
`choose n k * x ^ (choose k 2)` and obey a dilation recurrence. These
identities are the algebraic starting point for a finite approximation
proof of the slot representation, avoiding entire-function factorization.
This module does not assert the negative-root theorem.
-/

namespace CI2ZF.Appendix.Edge

open Polynomial
open scoped BigOperators

noncomputable section

def slotApproxPolynomial (x : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => slotApproxPolynomial x n + X * (slotApproxPolynomial x n).comp (C x * X)

@[simp] lemma slotApproxPolynomial_zero (x : ℝ) : slotApproxPolynomial x 0 = 1 := rfl

lemma slotApproxPolynomial_succ (x : ℝ) (n : ℕ) :
    slotApproxPolynomial x (n + 1) =
      slotApproxPolynomial x n + X * (slotApproxPolynomial x n).comp (C x * X) := rfl

lemma choose_two_succ (k : ℕ) : (k + 1).choose 2 = k + k.choose 2 := by
  simpa using Nat.choose_succ_succ k 1

lemma slotApproxPolynomial_coeff (x : ℝ) (n k : ℕ) :
    (slotApproxPolynomial x n).coeff k = (n.choose k : ℝ) * x ^ k.choose 2 := by
  induction n generalizing k with
  | zero => cases k <;> simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [slotApproxPolynomial_succ, coeff_add]
    cases k with
    | zero => simp [ih]
    | succ k =>
      rw [coeff_X_mul, comp_C_mul_X_coeff, ih, ih]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, pow_add]
      ring

@[simp] lemma slotApproxPolynomial_constant (x : ℝ) (n : ℕ) :
    (slotApproxPolynomial x n).coeff 0 = 1 := by simp [slotApproxPolynomial_coeff]

@[simp] lemma slotApproxPolynomial_linear (x : ℝ) (n : ℕ) :
    (slotApproxPolynomial x n).coeff 1 = n := by simp [slotApproxPolynomial_coeff]

lemma slotApproxPolynomial_ne_zero (x : ℝ) (n : ℕ) : slotApproxPolynomial x n ≠ 0 := by
  intro h
  have := slotApproxPolynomial_constant x n
  rw [h, coeff_zero] at this
  norm_num at this

lemma slotApproxPolynomial_natDegree_le (x : ℝ) (n : ℕ) :
    (slotApproxPolynomial x n).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [slotApproxPolynomial_coeff, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_mul]

lemma slotApproxPolynomial_natDegree {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    (slotApproxPolynomial x n).natDegree = n := by
  apply le_antisymm (slotApproxPolynomial_natDegree_le x n)
  apply le_natDegree_of_ne_zero
  rw [slotApproxPolynomial_coeff, Nat.choose_self, Nat.cast_one, one_mul]
  exact pow_ne_zero _ hx

lemma slotApproxPolynomial_eval_succ (x t : ℝ) (n : ℕ) :
    (slotApproxPolynomial x (n + 1)).eval t =
      (slotApproxPolynomial x n).eval t + t * (slotApproxPolynomial x n).eval (x * t) := by
  simp [slotApproxPolynomial_succ]

/-- Scale by the number of available slots to give linear coefficient one. -/
def normalizedSlotApproxPolynomial (x : ℝ) (n : ℕ) : Polynomial ℝ :=
  (slotApproxPolynomial x n).comp (C (n : ℝ)⁻¹ * X)

lemma normalizedSlotApproxPolynomial_coeff (x : ℝ) (n k : ℕ) :
    (normalizedSlotApproxPolynomial x n).coeff k =
      (n.choose k : ℝ) * x ^ k.choose 2 / (n : ℝ) ^ k := by
  simp [normalizedSlotApproxPolynomial, comp_C_mul_X_coeff, slotApproxPolynomial_coeff,
    div_eq_mul_inv]

@[simp] lemma normalizedSlotApproxPolynomial_linear (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (normalizedSlotApproxPolynomial x n).coeff 1 = 1 := by
  simp [normalizedSlotApproxPolynomial_coeff, hn]

@[simp] lemma normalizedSlotApproxPolynomial_constant (x : ℝ) (n : ℕ) :
    (normalizedSlotApproxPolynomial x n).coeff 0 = 1 := by
  simp [normalizedSlotApproxPolynomial_coeff]

end
end CI2ZF.Appendix.Edge
