import ZeroFreeness.Coupling.Vigoda.CouplingIndependence

/-! The integer critical line lies in the degree range `Δ ≥ 6` on which the
Carlson–Vigoda contraction proves the hard-colouring bound cited in the main text. -/
namespace ZeroFreeness.Potts

theorem critical_line_degree_multiple_six {q Δ : ℕ}
    (hq : (q : ℝ) = (11 / 6 : ℝ) * Δ) : 6 ∣ Δ := by
  have h : 6 * q = 11 * Δ := by
    exact_mod_cast (show (6 : ℝ) * q = 11 * Δ by linarith)
  omega

theorem critical_line_degree_ge_six {q Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : (q : ℝ) = (11 / 6 : ℝ) * Δ) : 6 ≤ Δ :=
  Nat.le_of_dvd (by omega) (critical_line_degree_multiple_six hq)

theorem critical_line_degree_ge_three {q Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : (q : ℝ) = (11 / 6 : ℝ) * Δ) : 3 ≤ Δ :=
  le_trans (by norm_num) (critical_line_degree_ge_six hΔ hq)

end ZeroFreeness.Potts
