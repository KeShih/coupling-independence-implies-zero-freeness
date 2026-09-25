import ZeroFreeness.Coupling.CV.Arithmetic

/-! The continuous numerical closure in the CV appendix, with its exact gap.
The proof works throughout the unbounded half-plane, not on a sampled grid. -/
namespace ZeroFreeness.Appendix.CV
noncomputable section

def gammaGain (ρ Δ : ℝ) : ℝ := 17 / (200 * ρ) * (ρ - 1 - 2 / Δ)
def gammaLoss (ρ Δ θ φ : ℝ) : ℝ :=
  17 / (200 * ρ) * (ρ - (81 / 250) * θ * φ + 1 + 81 / 250 + 2 / Δ)

lemma coefficient_form {ρ Δ θ φ : ℝ} (hρ : 0 < ρ) :
    gammaGain ρ Δ = 17 / 200 - (17 / (200 * ρ)) * (1 + 2 / Δ) ∧
    gammaLoss ρ Δ θ φ =
      17 / 200 + (17 / (200 * ρ)) * (1 + 81 / 250 + 2 / Δ - (81 / 250) * (θ * φ)) := by
  unfold gammaGain gammaLoss
  constructor <;> field_simp <;> ring

lemma parameter_bounds {ρ Δ : ℝ} (hρ : 1809 / 1000 ≤ ρ) (hΔ : 125 ≤ Δ) :
    0 < ρ ∧ 0 < Δ ∧ 0 ≤ 2 / Δ ∧ 2 / Δ ≤ 2 / 125 ∧
    0 ≤ 17 / (200 * ρ) ∧ 17 / (200 * ρ) ≤ 85 / 1809 := by
  have hr : 0 < ρ := by linarith
  have hd : 0 < Δ := by linarith
  refine ⟨hr, hd, by positivity, ?_, by positivity, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 200 * ρ)).mpr
    linarith

lemma geometric_coefficients_box {ρ Δ θ φ : ℝ}
    (hρ : 1809 / 1000 ≤ ρ) (hΔ : 125 ≤ Δ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    13481 / 361800 ≤ gammaGain ρ Δ ∧ gammaGain ρ Δ < 17 / 200 ∧
    0 ≤ gammaLoss ρ Δ θ φ ∧ gammaLoss ρ Δ θ φ ≤ 799 / 5400 := by
  obtain ⟨hr, hd, ht0, ht1, he0, he1⟩ := parameter_bounds hρ hΔ
  obtain ⟨hgf, hlf⟩ := coefficient_form (Δ := Δ) (θ := θ) (φ := φ) hr
  have hy0 : 0 ≤ θ * φ := mul_nonneg hθ.1 hφ.1
  have hy1 : θ * φ ≤ 1 := (mul_le_mul_of_nonneg_right hθ.2 hφ.1).trans (by simpa using hφ.2)
  have hprod := mul_le_mul he1 (show 1 + 2 / Δ ≤ (127 / 125 : ℝ) by linarith)
    (by linarith : 0 ≤ 1 + 2 / Δ) (by norm_num : (0 : ℝ) ≤ 85 / 1809)
  have hep : 0 < 17 / (200 * ρ) := by positivity
  have hpos := mul_pos hep (show 0 < 1 + 2 / Δ by linarith)
  have hbr0 : 0 ≤ 1 + 81 / 250 + 2 / Δ - (81 / 250) * (θ * φ) := by linarith
  have hbr1 : 1 + 81 / 250 + 2 / Δ - (81 / 250) * (θ * φ) ≤ (67 / 50 : ℝ) := by linarith
  have hlprod := mul_le_mul he1 hbr1 hbr0 (by norm_num : (0 : ℝ) ≤ 85 / 1809)
  have hlpos := mul_nonneg he0 hbr0
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- A division-free form of the three-branch scalar certificate. -/
theorem scalar_box {ρ t e θ φ : ℝ}
    (hρ : 1809 / 1000 ≤ ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 2 / 125)
    (_he0 : 0 ≤ e) (he1 : e ≤ 85 / 1809)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    -ρ + bulk * (1 - φ) + θ * φ *
      low (17 / 200 - e * (1 + t))
        (17 / 200 + e * (1 + 81 / 250 + t - (81 / 250) * (θ * φ))) ≤ -gap := by
  let y := θ * φ
  have hy0 : 0 ≤ y := mul_nonneg hθ.1 hφ.1
  have hyp : y ≤ φ := by simpa [y] using mul_le_mul_of_nonneg_right hθ.2 hφ.1
  have hy1 : y ≤ 1 := hyp.trans hφ.2
  have hb0 : 0 ≤ 1 + 81 / 250 + t - (81 / 250) * y := by linarith
  have hb1 : 1 + 81 / 250 + t - (81 / 250) * y ≤ 67 / 50 - (81 / 250) * y := by linarith
  have hp := mul_le_mul he1 hb1 hb0 (by norm_num : (0 : ℝ) ≤ 85 / 1809)
  have hprod := mul_le_mul he1 (show 1 + t ≤ (127 / 125 : ℝ) by linarith)
    (by linarith : 0 ≤ 1 + t) (by norm_num : (0 : ℝ) ≤ 85 / 1809)
  have hp' := mul_le_mul_of_nonneg_left hp hy0
  have hprod' := mul_le_mul_of_nonneg_left hprod hy0
  have hs := sq_nonneg (y - 1)
  have h₁ : -ρ + bulk * (1 - φ) + y *
      (2 - 81 / 250 + (17 / 200 + e * (1 + 81 / 250 + t - (81 / 250) * y))) ≤ -gap := by
    unfold bulk gap
    nlinarith
  have h₂ : -ρ + bulk * (1 - φ) + y *
      (2 - 77 / 500 - (17 / 200 - e * (1 + t))) ≤ -gap := by
    unfold bulk gap
    nlinarith
  have h₃ : -ρ + bulk * (1 - φ) + y * (226 / 125) ≤ -gap := by
    unfold bulk gap
    nlinarith
  change -ρ + bulk * (1 - φ) + y * low _ _ ≤ -gap
  unfold low
  rw [mul_max_of_nonneg _ _ hy0, mul_max_of_nonneg _ _ hy0]
  exact add_le_of_le_sub_left (max_le (by linarith) (max_le (by linarith) (by linarith)))

/-- Lemma cv-scalar for every real admissible parameter, including both endpoints
of the activation interval. -/
theorem scalar_closure {ρ Δ θ φ : ℝ}
    (hρ : 1809 / 1000 ≤ ρ) (hΔ : 125 ≤ Δ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    -ρ + bulk * (1 - φ) + θ * φ * low (gammaGain ρ Δ) (gammaLoss ρ Δ θ φ) ≤ -gap := by
  obtain ⟨hr, _, ht0, ht1, he0, he1⟩ := parameter_bounds hρ hΔ
  obtain ⟨hg, hl⟩ := coefficient_form (Δ := Δ) (θ := θ) (φ := φ) hr
  rw [hg, hl]
  exact scalar_box hρ ht0 ht1 he0 he1 hθ hφ

/-! ### The critical line

On the line `q = 11Δ/6` of the main theorem the colour ratio exceeds 1.809,
and the same closure holds, with the same gap, for every degree `Δ ≥ 6`. -/

lemma critical_parameter_bounds {ρ Δ : ℝ} (hρ : 11 / 6 ≤ ρ) (hΔ : 6 ≤ Δ) :
    0 < ρ ∧ 0 < Δ ∧ 0 ≤ 2 / Δ ∧ 2 / Δ ≤ 1 / 3 ∧
    0 ≤ 17 / (200 * ρ) ∧ 17 / (200 * ρ) ≤ 51 / 1100 := by
  have hr : 0 < ρ := by linarith
  have hd : 0 < Δ := by linarith
  refine ⟨hr, hd, by positivity, ?_, by positivity, ?_⟩
  · apply (div_le_iff₀ hd).mpr; linarith
  · apply (div_le_iff₀ (by positivity : 0 < 200 * ρ)).mpr; linarith

lemma critical_coefficients_box {ρ Δ θ φ : ℝ}
    (hρ : 11 / 6 ≤ ρ) (hΔ : 6 ≤ Δ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    51 / 2200 ≤ gammaGain ρ Δ ∧ 0 ≤ gammaLoss ρ Δ θ φ ∧ gammaLoss ρ Δ θ φ ≤ 81 / 500 := by
  obtain ⟨hr, hd, ht0, ht1, he0, he1⟩ := critical_parameter_bounds hρ hΔ
  have hy0 : 0 ≤ θ * φ := mul_nonneg hθ.1 hφ.1
  have hy1 : θ * φ ≤ 1 := (mul_le_mul_of_nonneg_right hθ.2 hφ.1).trans (by simpa using hφ.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [(coefficient_form (Δ := Δ) (θ := θ) (φ := φ) hr).1]
    have := mul_le_mul he1 (show 1 + 2 / Δ ≤ (4 / 3 : ℝ) by linarith) (by linarith) (by norm_num)
    linarith
  · unfold gammaLoss
    have hb : 0 ≤ ρ - (81 / 250) * θ * φ + 1 + 81 / 250 + 2 / Δ := by nlinarith
    positivity
  · rw [(coefficient_form (Δ := Δ) (θ := θ) (φ := φ) hr).2]
    have hb0 : 0 ≤ 1 + 81 / 250 + 2 / Δ - (81 / 250) * (θ * φ) := by nlinarith
    have hb1 : 1 + 81 / 250 + 2 / Δ - (81 / 250) * (θ * φ) ≤ (1243 / 750 : ℝ) := by nlinarith
    have := mul_le_mul he1 hb1 hb0 (by norm_num)
    linarith

/-- The division-free three-branch closure on the critical line. -/
theorem critical_scalar_box {ρ t e θ φ : ℝ}
    (hρ : 11 / 6 ≤ ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 3)
    (_he0 : 0 ≤ e) (he1 : e ≤ 51 / 1100)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    -ρ + bulk * (1 - φ) + θ * φ *
      low (17 / 200 - e * (1 + t))
        (17 / 200 + e * (1 + 81 / 250 + t - (81 / 250) * (θ * φ))) ≤ -gap := by
  let y := θ * φ
  have hy0 : 0 ≤ y := mul_nonneg hθ.1 hφ.1
  have hyp : y ≤ φ := by simpa [y] using mul_le_mul_of_nonneg_right hθ.2 hφ.1
  have hy1 : y ≤ 1 := hyp.trans hφ.2
  have hb0 : 0 ≤ 1 + 81 / 250 + t - (81 / 250) * y := by linarith
  have hb1 : 1 + 81 / 250 + t - (81 / 250) * y ≤ 499 / 300 - (81 / 250) * y := by linarith
  have hp := mul_le_mul he1 hb1 hb0 (by norm_num : (0 : ℝ) ≤ 51 / 1100)
  have hprod := mul_le_mul he1 (show 1 + t ≤ (4 / 3 : ℝ) by linarith)
    (by linarith : 0 ≤ 1 + t) (by norm_num : (0 : ℝ) ≤ 51 / 1100)
  have hp' := mul_le_mul_of_nonneg_left hp hy0
  have hprod' := mul_le_mul_of_nonneg_left hprod hy0
  have hs := sq_nonneg (y - 1)
  have h₁ : -ρ + bulk * (1 - φ) + y *
      (2 - 81 / 250 + (17 / 200 + e * (1 + 81 / 250 + t - (81 / 250) * y))) ≤ -gap := by
    unfold bulk gap
    nlinarith
  have h₂ : -ρ + bulk * (1 - φ) + y *
      (2 - 77 / 500 - (17 / 200 - e * (1 + t))) ≤ -gap := by
    unfold bulk gap
    nlinarith
  have h₃ : -ρ + bulk * (1 - φ) + y * (226 / 125) ≤ -gap := by
    unfold bulk gap
    nlinarith
  change -ρ + bulk * (1 - φ) + y * low _ _ ≤ -gap
  unfold low
  rw [mul_max_of_nonneg _ _ hy0, mul_max_of_nonneg _ _ hy0]
  exact add_le_of_le_sub_left (max_le (by linarith) (max_le (by linarith) (by linarith)))

theorem critical_scalar_closure {ρ Δ θ φ : ℝ}
    (hρ : 11 / 6 ≤ ρ) (hΔ : 6 ≤ Δ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    -ρ + bulk * (1 - φ) + θ * φ * low (gammaGain ρ Δ) (gammaLoss ρ Δ θ φ) ≤ -gap := by
  obtain ⟨hr, _, ht0, ht1, he0, he1⟩ := critical_parameter_bounds hρ hΔ
  obtain ⟨hg, hl⟩ := coefficient_form (Δ := Δ) (θ := θ) (φ := φ) hr
  rw [hg, hl]
  exact critical_scalar_box hρ ht0 ht1 he0 he1 hθ hφ

/-! ### The two regimes of the CV contraction -/

/-- The published regime `Δ ≥ 125, q ≥ 1.809Δ`, or the critical line
`q ≥ 11Δ/6` with `Δ ≥ 6`. -/
def Regime (Δ : ℕ) (q : ℝ) : Prop :=
  (125 ≤ Δ ∧ (1809 / 1000 : ℝ) * Δ ≤ q) ∨ (6 ≤ Δ ∧ (11 / 6 : ℝ) * Δ ≤ q)

lemma Regime.degree_pos {Δ : ℕ} {q : ℝ} (h : Regime Δ q) : 0 < Δ := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

lemma Regime.colours {Δ : ℕ} {q : ℝ} (h : Regime Δ q) : (1809 / 1000 : ℝ) * Δ ≤ q := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    nlinarith

lemma Regime.slack {Δ : ℕ} {q : ℝ} (h : Regime Δ q) : (Δ : ℝ) + 2 ≤ q := by
  rcases h with ⟨hΔ, hq⟩ | ⟨hΔ, hq⟩
  · have : (125 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    linarith
  · have : (6 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    linarith

/-- The coefficient ranges used by the charge envelope, in both regimes. -/
lemma Regime.coefficients {Δ : ℕ} {q θ φ : ℝ} (h : Regime Δ q)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    51 / 2200 ≤ gammaGain (q / Δ) Δ ∧ 0 ≤ gammaLoss (q / Δ) Δ θ φ ∧
      gammaLoss (q / Δ) Δ θ φ ≤ 81 / 500 := by
  have hd : (0 : ℝ) < Δ := by exact_mod_cast h.degree_pos
  rcases h with ⟨hΔ, hq⟩ | ⟨hΔ, hq⟩
  · have hr : 1809 / 1000 ≤ q / Δ := (le_div_iff₀ hd).mpr hq
    have hΔ' : (125 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    obtain ⟨hg, _, hl0, hl⟩ := geometric_coefficients_box hr hΔ' hθ hφ
    exact ⟨by linarith, hl0, by linarith⟩
  · have hr : 11 / 6 ≤ q / Δ := (le_div_iff₀ hd).mpr hq
    have hΔ' : (6 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    exact critical_coefficients_box hr hΔ' hθ hφ

/-- Lemma cv-scalar in both regimes, with the same gap. -/
theorem Regime.scalar_closure {Δ : ℕ} {q θ φ : ℝ} (h : Regime Δ q)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    -(q / Δ) + bulk * (1 - φ) + θ * φ *
      low (gammaGain (q / Δ) Δ) (gammaLoss (q / Δ) Δ θ φ) ≤ -gap := by
  have hd : (0 : ℝ) < Δ := by exact_mod_cast h.degree_pos
  rcases h with ⟨hΔ, hq⟩ | ⟨hΔ, hq⟩
  · have hΔ' : (125 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    exact ZeroFreeness.Appendix.CV.scalar_closure ((le_div_iff₀ hd).mpr hq) hΔ' hθ hφ
  · have hΔ' : (6 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    exact critical_scalar_closure ((le_div_iff₀ hd).mpr hq) hΔ' hθ hφ

end
end ZeroFreeness.Appendix.CV
