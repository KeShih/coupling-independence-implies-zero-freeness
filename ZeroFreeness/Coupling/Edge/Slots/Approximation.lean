import ZeroFreeness.Coupling.Edge.RealRoots
import ZeroFreeness.Coupling.Edge.Slots.Moments
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite probability slot laws converging to the exact Potts moments

The negative-root factorization produces actual positive finite probability
weights. Their ordered distinct-slot moments converge to the moments in the
paper. Finite Potts colour spaces can use this approximation directly,
without requiring a countable slot law or an entire-function theorem.
-/

namespace ZeroFreeness.Appendix.Edge

open Polynomial Filter
open scoped BigOperators Topology

noncomputable section

lemma normalizedSlotApproxPolynomial_factorization {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ κ : Fin n → ℝ, (∀ r, 0 < κ r) ∧ (∑ r, κ r) = 1 ∧
      slotGeneratingPolynomial κ = normalizedSlotApproxPolynomial x n := by
  obtain ⟨r, hr, _, hfactor⟩ := slotApproxPolynomial_separated_factorization hx hx1 n
  let κ : Fin n → ℝ := fun i => ((n : ℝ) * r i)⁻¹
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hκ (i : Fin n) : 0 < κ i := inv_pos.mpr (mul_pos hnpos (hr i))
  have hpoly : slotGeneratingPolynomial κ = normalizedSlotApproxPolynomial x n := by
    apply Polynomial.funext
    intro t
    have hreflect := congrArg (fun p : Polynomial ℝ => p.eval (-((n : ℝ)⁻¹ * t))) hfactor
    simp only [reflectedSlotApproxPolynomial_eval, neg_neg, normalizedFactorPolynomial_eval] at hreflect
    simp only [normalizedSlotApproxPolynomial, eval_comp, eval_mul, eval_C, eval_X]
    rw [hreflect]
    simp only [slotGeneratingPolynomial, eval_prod, eval_add, eval_one, eval_mul, eval_C,
      eval_X, normalizedRootProduct]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [κ]
    field_simp
    ring
  refine ⟨κ, hκ, ?_, hpoly⟩
  have h := congrArg (fun p : Polynomial ℝ => p.coeff 1) hpoly
  simpa only [slotGeneratingPolynomial_linear, normalizedSlotApproxPolynomial_linear x hn] using h

lemma distinctSlotMass_of_approx_factorization {n : ℕ} (κ : Fin n → ℝ) (x : ℝ)
    (hfactor : slotGeneratingPolynomial κ = normalizedSlotApproxPolynomial x n) (k : ℕ) :
    distinctSlotMass κ k = (n.descFactorial k : ℝ) / (n : ℝ) ^ k * x ^ k.choose 2 := by
  rw [distinctSlotMass_eq_factorial_coeff, hfactor, normalizedSlotApproxPolynomial_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- An actual finite probability slot law, indexed so that every law has at
least one slot. -/
def finiteApproxSlotWeights (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (n : ℕ) : Fin (n + 1) → ℝ :=
  Classical.choose (normalizedSlotApproxPolynomial_factorization hx hx1 (Nat.succ_ne_zero n))

lemma finiteApproxSlotWeights_pos (x : ℝ) (hx : 0 < x) (hx1 : x < 1)
    (n : ℕ) (r : Fin (n + 1)) : 0 < finiteApproxSlotWeights x hx hx1 n r :=
  (Classical.choose_spec (normalizedSlotApproxPolynomial_factorization hx hx1
    (Nat.succ_ne_zero n))).1 r

lemma finiteApproxSlotWeights_sum (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (n : ℕ) :
    (∑ r, finiteApproxSlotWeights x hx hx1 n r) = 1 :=
  (Classical.choose_spec (normalizedSlotApproxPolynomial_factorization hx hx1
    (Nat.succ_ne_zero n))).2.1

lemma finiteApproxSlotWeights_factorization (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (n : ℕ) :
    slotGeneratingPolynomial (finiteApproxSlotWeights x hx hx1 n) =
      normalizedSlotApproxPolynomial x (n + 1) :=
  (Classical.choose_spec (normalizedSlotApproxPolynomial_factorization hx hx1
    (Nat.succ_ne_zero n))).2.2

lemma finiteApproxSlotWeights_moment (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (n k : ℕ) :
    distinctSlotMass (finiteApproxSlotWeights x hx hx1 n) k =
      ((n + 1).descFactorial k : ℝ) / ((n : ℝ) + 1) ^ k * x ^ k.choose 2 := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    distinctSlotMass_of_approx_factorization (finiteApproxSlotWeights x hx hx1 n) x
      (finiteApproxSlotWeights_factorization x hx hx1 n) k

/-- The finite-population correction tends to one for every fixed moment. -/
lemma tendsto_descFactorial_ratio (k : ℕ) :
    Tendsto (fun n : ℕ => ((n + 1).descFactorial k : ℝ) / ((n : ℝ) + 1) ^ k)
      atTop (𝓝 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hfactor : Tendsto (fun n : ℕ => 1 - (k : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      have hdiv : Tendsto (fun n : ℕ => (k : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa only [mul_one_div, mul_zero] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (k : ℝ)
      simpa using tendsto_const_nhds.sub hdiv
    have hmul := hfactor.mul ih
    simp only [one_mul] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkn : k ≤ n + 1 := by omega
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one, pow_succ]
    have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- Finite slot laws recover every exact Potts distinctness moment in the
limit. Both the laws and their convergence are constructed here. -/
lemma finiteApproxSlotWeights_moment_tendsto (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (k : ℕ) :
    Tendsto (fun n => distinctSlotMass (finiteApproxSlotWeights x hx hx1 n) k)
      atTop (𝓝 (x ^ k.choose 2)) := by
  simp only [finiteApproxSlotWeights_moment]
  simpa only [one_mul] using (tendsto_descFactorial_ratio k).mul_const (x ^ k.choose 2)

end
end ZeroFreeness.Appendix.Edge
