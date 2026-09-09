import CI2ZF.Appendix.Girth.Tree.TotalInfluence
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Eventual ratio-form spatial mixing

The logarithmic estimate is converted to the ratio form used in CLMM2023,
Definition 5.7. The burn-in is chosen uniformly from the colour and degree
parameters, and does not depend on the activity or the tree.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset Set PottsCI

noncomputable section

theorem exp_small_upper {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) :
    Real.exp ε ≤ 1 + 2 * ε := by
  have hc := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ from trivial)
    (show (1 : ℝ) ∈ Set.univ from trivial) (sub_nonneg.mpr hε.2) hε.1
    (by ring : (1 - ε) + ε = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hc
  have he := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hε.1
  nlinarith

theorem ratio_error_from_log {r ε : ℝ} (hr : 0 < r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hlog : |Real.log r| ≤ ε) : |r - 1| ≤ 2 * ε := by
  have hbounds := abs_le.mp hlog
  have hrupper : r ≤ Real.exp ε := by
    simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr hbounds.2
  have hrlower : Real.exp (-ε) ≤ r := by
    simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr hbounds.1
  have hlow := Real.add_one_le_exp (-ε)
  have hupp := exp_small_upper ⟨hε0, hε1⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem exists_uniform_burn_in {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, C * ρ ^ k ≤ 1 := by
  by_cases hc0 : C = 0
  · exact ⟨0, fun _ _ => by simp only [hc0, zero_mul]; norm_num⟩
  · have hC0 : 0 < C := lt_of_le_of_ne hC (Ne.symm hc0)
    obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / C by positivity) hρ1
    refine ⟨k₀, fun k hk => ?_⟩
    have hp := pow_le_pow_of_le_one hρ hρ1.le hk
    have hn : C * ρ ^ k₀ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hk₀.le hC
      simpa only [mul_one_div_cancel hc0] using h
    exact (mul_le_mul_of_nonneg_left hp hC).trans hn

def relativeMixingConstant (Δ q : ℝ) : ℝ :=
  (5 / 8 : ℝ) * Δ * q * Real.exp (1 / 12) * Real.log 3

theorem relativeMixingConstant_nonneg {Δ q : ℝ} (hΔ : 0 ≤ Δ) (hq : 0 ≤ q) :
    0 ≤ relativeMixingConstant Δ q := by
  unfold relativeMixingConstant
  exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))

namespace CavityTree

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- A single uniform burn-in gives the CLMM ratio error estimate for every
activity and every pair of boundary conditions at the same shell. -/
theorem eventual_ratio_spatial_mixing {Δ : ℕ} (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ d b (t u : Fin d → CavityTree C),
      (∀ i, Agreement k (t i) (u i)) →
      ∀ x : ℝ, 0 < x → x < 1 → d + (∑ c, b c) ≤ Δ →
      (∀ i, (t i).DegreeBudget Δ) → (∀ i, (u i).DegreeBudget Δ) → ∀ c,
      |(CavityTree.node d b t).probability x c / (CavityTree.node d b u).probability x c - 1| ≤
        2 * relativeMixingConstant Δ (Fintype.card C) * decayRate (Fintype.card C) ^ k := by
  have hq0 : 0 < (Fintype.card C : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hC := relativeMixingConstant_nonneg (Nat.cast_nonneg Δ) (Nat.cast_nonneg (Fintype.card C))
  obtain ⟨k₀, hk₀⟩ := exists_uniform_burn_in hC (decayRate_pos (Fintype.card C)).le (decayRate_lt_one hq0)
  refine ⟨k₀, ?_⟩
  intro k hk d b t u hag x hx hx1 hroot ht hu c
  have hlog := relative_spatial_decay k d b t u hag hx hx1 hq hroot ht hu c
  have htp : 0 < (CavityTree.node d b t).probability x c := by
    rw [(CavityTree.node d b t).probability_eq_gibbs hx c]
    exact div_pos ((CavityTree.node d b t).rootWeight_pos hx c) ((CavityTree.node d b t).partition_pos hx)
  have hup : 0 < (CavityTree.node d b u).probability x c := by
    rw [(CavityTree.node d b u).probability_eq_gibbs hx c]
    exact div_pos ((CavityTree.node d b u).rootWeight_pos hx c) ((CavityTree.node d b u).partition_pos hx)
  have h := ratio_error_from_log (div_pos htp hup)
    (mul_nonneg hC (pow_nonneg (decayRate_pos _).le _)) (hk₀ k hk) hlog
  simpa only [mul_assoc] using h

end CavityTree

end

end CI2ZF.Appendix.Girth
