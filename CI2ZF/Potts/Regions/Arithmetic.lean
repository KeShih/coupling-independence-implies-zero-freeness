import Mathlib.Tactic

/-! Exact integer and rational reductions in `additional-potts-results.tex`.
These arithmetic results do not assume any coupling or zero-free theorem.
-/
namespace CI2ZF.Appendix

/-- The near-Vigoda threshold used by regime (i). -/
def nearVigoda : ℚ := 11 / 6 - 1 / 84000

theorem nearVigoda_eq : nearVigoda = 153999 / 84000 := by
  norm_num [nearVigoda]

theorem nearVigoda_sub_cv : nearVigoda - 1809 / 1000 = 681 / 28000 := by
  norm_num [nearVigoda]

/-- Every integer point on the critical line is exactly `(6j,11j)`. -/
theorem critical_line_integer {Δ q : ℕ} (hline : 6 * q = 11 * Δ) :
    ∃ j : ℕ, Δ = 6 * j ∧ q = 11 * j := by
  have hdiv : 6 ∣ Δ := by omega
  obtain ⟨j, hj⟩ := hdiv
  exact ⟨j, hj, by omega⟩

/-- `lem:int-reduction`, with the paper's real-valued threshold. -/
theorem integer_reduction {Δ q : ℕ} (hΔ : 3 ≤ Δ) (hΔmax : Δ ≤ 124)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ q) :
    (11 / 6 : ℝ) * Δ < q ∨
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ 20 ∧ Δ = 6 * j ∧ q = 11 * j := by
  by_cases hs : (11 / 6 : ℝ) * Δ < q
  · exact Or.inl hs
  right
  have hu : (q : ℝ) ≤ (11 / 6 : ℝ) * Δ := le_of_not_gt hs
  have hmax : (Δ : ℝ) ≤ 124 := by exact_mod_cast hΔmax
  have hlow : (11 * Δ : ℝ) < 6 * q + 1 := by nlinarith
  have hn : 11 * Δ < 6 * q + 1 := by exact_mod_cast hlow
  have hn' : 6 * q ≤ 11 * Δ := by exact_mod_cast (show (6 * q : ℝ) ≤ 11 * Δ by linarith)
  have he : 6 * q = 11 * Δ := by omega
  obtain ⟨j, hjΔ, hjq⟩ := critical_line_integer he
  exact ⟨j, by omega, by omega, hjΔ, hjq⟩

/-- Degree two is strictly above the original Vigoda line. -/
theorem nearVigoda_degree_two {q : ℕ}
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * 2 ≤ q) :
    4 ≤ q ∧ (11 / 6 : ℝ) * 2 < q := by
  have hr : (3 : ℝ) < q := by linarith
  have hn : 3 < q := by exact_mod_cast hr
  constructor
  · omega
  · have hr' : (4 : ℝ) ≤ q := by exact_mod_cast (show 4 ≤ q by omega)
    linarith

/-- Large degrees in regime (i) automatically meet the CV colour threshold. -/
theorem nearVigoda_implies_cv {Δ q : ℕ}
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ q) :
    (1809 / 1000 : ℝ) * Δ ≤ q := by
  have hΔ : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  nlinarith

/-- The complete arithmetic case split used for the coupling inputs. -/
theorem nearVigoda_regime_cases {Δ q : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ q) :
    (125 ≤ Δ ∧ (1809 / 1000 : ℝ) * Δ ≤ q) ∨
    (11 / 6 : ℝ) * Δ < q ∨
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 20 ∧ Δ = 6 * j ∧ q = 11 * j := by
  by_cases hlarge : 125 ≤ Δ
  · exact Or.inl ⟨hlarge, nearVigoda_implies_cv hq⟩
  right
  by_cases htwo : Δ = 2
  · subst Δ
    exact Or.inl (nearVigoda_degree_two hq).2
  exact integer_reduction (by omega) (by omega) hq

/-- All three full-interval colour regimes satisfy hard feasibility. -/
theorem colours_succ_of_cv {Δ q : ℕ} (hΔ : 2 ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ q) : Δ + 1 ≤ q := by
  have hp : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hr : (Δ : ℝ) < q := by linarith
  have hn : Δ < q := by exact_mod_cast hr
  omega

theorem colours_succ_of_nearVigoda {Δ q : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ q) : Δ + 1 ≤ q :=
  colours_succ_of_cv hΔ (nearVigoda_implies_cv hq)

end CI2ZF.Appendix
