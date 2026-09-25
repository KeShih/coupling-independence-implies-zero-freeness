import ZeroFreeness.Coupling.BBR.CertificateArithmetic

/-!
# The rounded BBR interval (companion, `additional-potts-results.tex`, lines 223-232)

After `thm:intro-bbr-interval`, the companion claims:

1. writing `t = Δ - q`, the ratio hypothesis gives `t/q ≥ 1/[2(e-1)]`, and
   hence `k = e(1 + q/(2t)) ≤ e²`;
2. `s ↦ (1 - s/Δ)^3 / (1 - s/(2Δ))` is decreasing on `(0, Δ)`;
3. hence the interval `[x₀, 1]` contains BBR's rounded interval (the formula
   `eq:intro-bbr-x0` with `k` replaced by `e²`) whenever the latter is
   nonempty;
4. at `(q, Δ) = (3, 4)` the rounded interval is empty.

All four are proved below.  `x₀` is the library's `start q Δ` (equal to
`3/4` at the exceptional pair and to `intervalStart q Δ` otherwise).
-/

namespace ZeroFreeness.Appendix.BBR
open Set ZeroFreeness.Appendix.BBR
noncomputable section

/-- The right side of `eq:intro-bbr-x0` as a function of the parameter `k`. -/
def startFormula (q Δ k : ℝ) : ℝ :=
  1 - q / Δ * (1 - k / Δ) ^ 2 * (Δ - k) / (Δ - k / 2)

/-- BBR's rounded endpoint: `k` replaced by `e²`. -/
def roundedStart (q Δ : ℝ) : ℝ := startFormula q Δ (Real.exp 1 ^ 2)

/-- The decreasing profile of the companion. -/
def profile (Δ s : ℝ) : ℝ := (1 - s / Δ) ^ 3 / (1 - s / (2 * Δ))

theorem intervalStart_eq_startFormula (q Δ : ℝ) :
    intervalStart q Δ = startFormula q Δ (parameter q Δ) := rfl

/-- The endpoint formula is `1 - (q/Δ) · profile(k)`. -/
theorem startFormula_eq_profile {q Δ : ℝ} (hΔ : Δ ≠ 0) (k : ℝ) :
    startFormula q Δ k = 1 - q / Δ * profile Δ k := by
  unfold startFormula profile
  by_cases hk : Δ - k / 2 = 0
  · have hk' : 1 - k / (2 * Δ) = 0 := by
      rw [show 1 - k / (2 * Δ) = (Δ - k / 2) / Δ by field_simp, hk, zero_div]
    rw [hk, hk', div_zero, div_zero, mul_zero]
  · have hk' : 1 - k / (2 * Δ) ≠ 0 := by
      rw [show 1 - k / (2 * Δ) = (Δ - k / 2) / Δ by field_simp]
      exact div_ne_zero hk hΔ
    field_simp

/-! ## 1. The parameter in terms of `t = Δ - q` -/

/-- The ratio hypothesis in the form `t/q ≥ 1/[2(e-1)]`, with `t = Δ - q`. -/
theorem ratio_iff_gap {q Δ : ℝ} (hq : 0 < q) :
    (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ Δ / q ↔
      1 / (2 * (Real.exp 1 - 1)) ≤ (Δ - q) / q := by
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.exp_one_gt_two]
  rw [ratio_iff hq, div_le_div_iff₀ (by positivity) hq]
  constructor <;> intro h <;> nlinarith

/-- `k = e (1 + q/(2t))` with `t = Δ - q`. -/
theorem parameter_eq_gap_form {q Δ : ℝ} (hqΔ : q < Δ) :
    parameter q Δ = Real.exp 1 * (1 + q / (2 * (Δ - q))) := by
  have ht : Δ - q ≠ 0 := sub_ne_zero.mpr hqΔ.ne'
  unfold parameter
  field_simp
  ring

/-- **Claim 1.** Under the ratio hypothesis, with `t = Δ - q`:
`t/q ≥ 1/[2(e-1)]` and `k = e(1 + q/(2t)) ≤ e²`. -/
theorem gap_form_and_parameter_le {q Δ : ℝ} (hq : 0 < q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ Δ / q) :
    1 / (2 * (Real.exp 1 - 1)) ≤ (Δ - q) / q ∧
      parameter q Δ = Real.exp 1 * (1 + q / (2 * (Δ - q))) ∧
      Real.exp 1 * (1 + q / (2 * (Δ - q))) ≤ Real.exp 1 ^ 2 := by
  have hqΔ := degree_gt_colours hq hr
  refine ⟨(ratio_iff_gap hq).mp hr, parameter_eq_gap_form hqΔ, ?_⟩
  rw [← parameter_eq_gap_form hqΔ]
  exact parameter_le_exp_sq hq hr

/-! ## 2. Monotonicity of the profile -/

/-- **Claim 2.** `s ↦ (1 - s/Δ)^3/(1 - s/(2Δ))` is strictly decreasing on
`[0, Δ]`, in particular on `(0, Δ)`. -/
theorem profile_strictAntiOn {Δ : ℝ} (hΔ : 0 < Δ) : StrictAntiOn (profile Δ) (Icc 0 Δ) := by
  intro a ha b hb hab
  unfold profile
  set u := 1 - a / Δ with hu
  set w := 1 - b / Δ with hw
  have hu1 : 1 - a / (2 * Δ) = (1 + u) / 2 := by rw [hu]; field_simp; ring
  have hw1 : 1 - b / (2 * Δ) = (1 + w) / 2 := by rw [hw]; field_simp; ring
  have hw0 : 0 ≤ w := by
    rw [hw, sub_nonneg]; exact (div_le_one hΔ).mpr hb.2
  have hwu : w < u := by
    rw [hw, hu]; have := div_lt_div_of_pos_right hab hΔ; linarith
  rw [hu1, hw1, div_lt_div_iff₀ (by linarith) (by linarith)]
  have hu0 : 0 < u := hw0.trans_lt hwu
  have h3 : w ^ 3 < u ^ 3 := by
    have := pow_lt_pow_left₀ hwu hw0 (by norm_num : (3 : ℕ) ≠ 0)
    exact this
  have h4 : w ^ 3 * u ≤ u ^ 3 * w := by
    have : w * u * (w ^ 2 - u ^ 2) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      nlinarith
    nlinarith
  nlinarith

theorem profile_strictAntiOn_Ioo {Δ : ℝ} (hΔ : 0 < Δ) : StrictAntiOn (profile Δ) (Ioo 0 Δ) :=
  (profile_strictAntiOn hΔ).mono Ioo_subset_Icc_self

/-! ## 3. Containment of the rounded interval -/

theorem exp_one_sq_bounds : 4 < Real.exp 1 ^ 2 ∧ Real.exp 1 ^ 2 < 8 := by
  have h2 := Real.exp_one_gt_two
  have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  constructor <;> nlinarith

/-- For every non-exceptional admissible integer pair, if the rounded
interval is nonempty, then its left end is at least `x₀`. -/
theorem intervalStart_le_roundedStart {q Δ : ℕ} (hq : 3 ≤ q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / q)
    (hne : ¬ (q = 3 ∧ Δ = 4)) (hround : (Icc (roundedStart q Δ) 1).Nonempty) :
    intervalStart q Δ ≤ roundedStart q Δ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqΔ := degree_gt_colours hq0 hr
  have hgap := (integer_degree_gap hq hr).resolve_left hne
  have hΔ5 : (5 : ℝ) ≤ Δ := by exact_mod_cast (show 5 ≤ Δ by omega)
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  obtain ⟨hE4, hE8⟩ := exp_one_sq_bounds
  set E := Real.exp 1 ^ 2 with hE
  have hk0 := parameter_pos hq0 hqΔ
  have hkΔ := parameter_lt_degree hq hgap
  have hkE : parameter q Δ ≤ E := parameter_le_exp_sq hq0 hr
  -- nonemptiness of the rounded interval forces `E ≤ Δ`
  obtain ⟨y, hy1, hy2⟩ := hround
  have hle1 : roundedStart q Δ ≤ 1 := hy1.trans hy2
  unfold roundedStart at hle1
  rw [startFormula_eq_profile hΔ0.ne', ← hE] at hle1
  have hprof : 0 ≤ profile Δ E := by
    have hqd : 0 < (q : ℝ) / Δ := div_pos hq0 hΔ0
    by_contra hneg
    have := mul_neg_of_pos_of_neg hqd (lt_of_not_ge hneg)
    linarith
  have hden : 0 < 1 - E / (2 * Δ) := by
    rw [sub_pos, div_lt_one (by positivity)]; linarith
  have hEΔ : E ≤ Δ := by
    unfold profile at hprof
    have hnum : 0 ≤ (1 - E / Δ) ^ 3 := by
      have := mul_nonneg hprof hden.le
      rwa [div_mul_cancel₀ _ hden.ne'] at this
    have h1 : 0 ≤ 1 - E / Δ := by
      by_contra hneg
      have : (1 - E / Δ) ^ 3 < 0 := Odd.pow_neg (by decide) (lt_of_not_ge hneg)
      linarith
    rw [sub_nonneg, div_le_one hΔ0] at h1
    exact h1
  have hmono : profile Δ E ≤ profile Δ (parameter q Δ) :=
    (profile_strictAntiOn hΔ0).antitoneOn ⟨hk0.le, hkΔ.le⟩ ⟨by linarith, hEΔ⟩ hkE
  rw [intervalStart_eq_startFormula, roundedStart, startFormula_eq_profile hΔ0.ne',
    startFormula_eq_profile hΔ0.ne']
  have hqd : 0 ≤ (q : ℝ) / Δ := (div_pos hq0 hΔ0).le
  nlinarith [mul_le_mul_of_nonneg_left hmono hqd]

/-- **Claim 4.** At `(q, Δ) = (3, 4)` the rounded interval is empty. -/
theorem roundedStart_three_four : 1 < roundedStart 3 4 := by
  obtain ⟨hE4, hE8⟩ := exp_one_sq_bounds
  unfold roundedStart startFormula
  set E := Real.exp 1 ^ 2
  have h1 : 0 < (1 - E / 4) ^ 2 := by
    have : 1 - E / 4 ≠ 0 := by intro h; linarith
    positivity
  have h2 : (4 : ℝ) - E < 0 := by linarith
  have h3 : (0 : ℝ) < 4 - E / 2 := by linarith
  have hneg : (3 : ℝ) / 4 * (1 - E / 4) ^ 2 * (4 - E) / (4 - E / 2) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) h2) h3
  linarith

theorem rounded_interval_three_four_empty : Icc (roundedStart 3 4) 1 = ∅ :=
  Icc_eq_empty (not_le.mpr roundedStart_three_four)

/-- **Claim 3.** For every admissible integer pair (`q ≥ 3` and the ratio
hypothesis), the interval `[x₀, 1]` of `thm:intro-bbr-interval` contains
BBR's rounded interval.  The rounded interval is empty at the exceptional
pair, and whenever it is nonempty its left end is at least `x₀`. -/
theorem rounded_interval_subset {q Δ : ℕ} (hq : 3 ≤ q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / q) :
    Icc (roundedStart q Δ) 1 ⊆ Icc (start q Δ) 1 := by
  by_cases hex : q = 3 ∧ Δ = 4
  · obtain ⟨rfl, rfl⟩ := hex
    have h : Icc (roundedStart ((3 : ℕ) : ℝ) ((4 : ℕ) : ℝ)) 1 = ∅ := by
      simpa using rounded_interval_three_four_empty
    rw [h]
    exact empty_subset _
  · by_cases hround : (Icc (roundedStart q Δ) 1).Nonempty
    · have hstart : start q Δ = intervalStart q Δ := by simp only [start, if_neg hex]
      rw [hstart]
      exact Icc_subset_Icc_left (intervalStart_le_roundedStart hq hr hex hround)
    · rw [not_nonempty_iff_eq_empty.mp hround]
      exact empty_subset _

end
end ZeroFreeness.Appendix.BBR
