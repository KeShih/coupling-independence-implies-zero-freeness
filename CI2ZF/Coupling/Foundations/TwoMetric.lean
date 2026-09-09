import CI2ZF.Coupling.Foundations.FinDist

/-!
# Comparing transport costs in two metrics

This file records the two-metric form of stationary comparison used when a
Markov kernel contracts a geometric metric `d'`, while the desired conclusion
is stated in a smaller metric `d`.
-/

namespace PottsCI

open Finset

variable {S : Type*} [Fintype S]

namespace FinDist

/-- If `d'` dominates the nonnegative multiple `lambda * d` pointwise, then
the corresponding optimal transport costs satisfy the same domination. -/
theorem mul_W_le_W_of_mul_le {d d' : S → S → ℝ} {mu nu : FinDist S}
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (hd : ∀ x y, 0 ≤ d x y)
    (hdom : ∀ x y, lambda * d x y ≤ d' x y) :
    lambda * W d mu nu ≤ W d' mu nu := by
  apply le_W
  intro gamma
  calc
    lambda * W d mu nu ≤ lambda * gamma.cost d :=
      mul_le_mul_of_nonneg_left (W_le_cost hd gamma) hlambda
    _ ≤ gamma.cost d' := by
      unfold Coupling.cost
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      calc
        lambda * (gamma.w x y * d x y) = gamma.w x y * (lambda * d x y) := by ring
        _ ≤ gamma.w x y * d' x y :=
          mul_le_mul_of_nonneg_left (hdom x y) (gamma.nonneg x y)

/-- Two-metric stationary comparison.  The kernel `P` contracts in `d'`, its
rowwise discrepancy from `Q` is at most `D` in `d'`, and `d'` dominates the
positive multiple `lambda * d`.  The stationary laws are therefore close in
the target metric `d`.

The strict assumption `0 < lambda` is essential for the final division. -/
theorem stationary_comparison_two_metric [DecidableEq S]
    {d d' : S → S → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd' : ∀ x y, 0 ≤ d' x y)
    (htri' : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (P Q : S → FinDist S) (piP piQ : FinDist S)
    (hpiP : IsStationary P piP) (hpiQ : IsStationary Q piQ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcontr : ∀ alpha beta : FinDist S,
      W d' (alpha.bind P) (beta.bind P) ≤ c * W d' alpha beta)
    {D lambda : ℝ} (hlambda : 0 < lambda)
    (hdom : ∀ x y, lambda * d x y ≤ d' x y)
    (hD : ∀ x, W d' (P x) (Q x) ≤ D) :
    W d piP piQ ≤ D / (lambda * (1 - c)) := by
  have hmetric : lambda * W d piP piQ ≤ W d' piP piQ :=
    mul_W_le_W_of_mul_le hlambda.le hd hdom
  have hstationary : W d' piP piQ ≤ D / (1 - c) :=
    stationary_comparison hd' htri' P Q piP piQ hpiP hpiQ hc0 hc1 hcontr hD
  have hlambda_bound : lambda * W d piP piQ ≤ D / (1 - c) :=
    hmetric.trans hstationary
  have h1c : (0 : ℝ) < 1 - c := by linarith
  rw [le_div_iff₀ (mul_pos hlambda h1c)]
  apply (le_div_iff₀ h1c).mp at hlambda_bound
  nlinarith

end FinDist

end PottsCI
