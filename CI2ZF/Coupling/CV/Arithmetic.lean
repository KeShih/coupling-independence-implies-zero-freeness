import Mathlib.Tactic

/-! Exact arithmetic for the Carlson--Vigoda profile in Appendix cv-1809.
All infinite-size estimates below are proved after an explicit zero-tail reduction.
These lemmas concern the stated profile and do not assume a coupling inequality. -/
namespace CI2ZF.Appendix.CV
noncomputable section

/-- Aggregate accepted-flip mass from the CV appendix. -/
def mass : ℕ → ℝ
  | 1 => 1
  | 2 => 81 / 250
  | 3 => 77 / 500
  | 4 => 11 / 125
  | 5 => 11 / 250
  | 6 => 11 / 1000
  | _ => 0

lemma mass_zero_of_seven_le (r : ℕ) (hr : 7 ≤ r) : mass r = 0 := by
  match r with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
  | _ + 7 => simp [mass]

lemma mass_nonneg (r : ℕ) : 0 ≤ mass r := by
  by_cases h : r ≤ 6
  · interval_cases r <;> norm_num [mass]
  · rw [mass_zero_of_seven_le r (by omega)]

lemma mass_le_one (r : ℕ) : mass r ≤ 1 := by
  by_cases h : r ≤ 6
  · interval_cases r <;> norm_num [mass]
  · rw [mass_zero_of_seven_le r (by omega)]; norm_num

lemma mass_antitone {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) : mass s ≤ mass r := by
  by_cases hs : s ≤ 6
  · interval_cases s <;> interval_cases r <;> norm_num [mass] at *
  · rw [mass_zero_of_seven_le s (by omega)]
    exact mass_nonneg r

lemma size_mass_le_one (r : ℕ) : (r : ℝ) * mass r ≤ 1 := by
  by_cases h : r ≤ 6
  · interval_cases r <;> norm_num [mass]
  · rw [mass_zero_of_seven_le r (by omega)]; norm_num

lemma sub_one_size_mass_le (r : ℕ) : ((r : ℝ) - 1) * mass r ≤ 81 / 250 := by
  by_cases h : r ≤ 6
  · interval_cases r <;> norm_num [mass]
  · rw [mass_zero_of_seven_le r (by omega)]; norm_num

lemma sub_two_size_mass_le (r : ℕ) : ((r : ℝ) - 2) * mass r ≤ 22 / 125 := by
  by_cases h : r ≤ 6
  · interval_cases r <;> norm_num [mass]
  · rw [mass_zero_of_seven_le r (by omega)]; norm_num

lemma root_colour_one_neighbour (r : ℕ) :
    (r : ℝ) * mass r - ((r + 1 : ℕ) : ℝ) * mass (r + 1) ≤ 44 / 125 := by
  by_cases h : r ≤ 6
  · interval_cases r <;> norm_num [mass]
  · rw [mass_zero_of_seven_le r (by omega),
      mass_zero_of_seven_le (r + 1) (by omega)]; norm_num

/-- The residual-mass rectangle includes infeasible and partially matched moves. -/
lemma pair_charge_le (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    {u w : ℝ} (hu : u ≤ mass r) (hw : w ≤ mass s) :
    r * u + s * w - min u w ≤ 1 + 81 / 250 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hru := (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg r)).trans (size_mass_le_one r)
  have hsw := (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg s)).trans (size_mass_le_one s)
  have hru' := (mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ (r : ℝ) - 1)).trans
    (sub_one_size_mass_le r)
  have hsw' := (mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ (s : ℝ) - 1)).trans
    (sub_one_size_mass_le s)
  rcases le_total u w with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

def metricLower : ℝ := 1724 / 1809
def gap : ℝ := 59 / 226125
def bulk : ℝ := 1331 / 750
def low (gain loss : ℝ) : ℝ := max (2 - 81 / 250 + loss) (max (2 - 77 / 500 - gain) (226 / 125))

lemma constants :
    0 < metricLower ∧ 1 < 2 * metricLower ∧ metricLower ≤ 1 ∧
    0 < gap ∧ 2 / (metricLower * gap) = 409060125 / 50858 ∧
    2 / (metricLower * gap) < 804319 / 100 := by
  norm_num [metricLower, gap]

lemma high_multiplicity_arithmetic {k : ℝ} (hk : 3 ≤ k) :
    4 * (11 / 125) + k * (1 + 81 / 250) ≤ -1 + bulk * k := by
  unfold bulk
  linarith

lemma missing_colour_arithmetic {k loss : ℝ} (hk : 0 ≤ k) (hloss : loss ≤ 81 / 500) :
    k * (1 + 81 / 250 + loss) ≤ (743 / 500) * k ∧
    (743 / 500) * k ≤ bulk * k := by
  constructor
  · nlinarith
  · unfold bulk; nlinarith

lemma root_colour_many_arithmetic {k : ℝ} (hk : 2 ≤ k) :
    k + 22 / 125 ≤ -1 + bulk * k := by
  unfold bulk; linarith

lemma low_balancing : low (19 / 500) (33 / 250) = 226 / 125 := by
  norm_num [low]

/-- The excess is maximized at the balancing coefficients on the entire plane,
not just on the rectangle used by the paper. -/
theorem balancing_domination (H gain loss : ℝ) (k n₁₁ n₁₂ : ℕ)
    (hcount : n₁₁ + n₁₂ ≤ k) :
    H + loss * n₁₁ - gain * n₁₂ + 1 - k * low gain loss ≤
    H + (33 / 250) * n₁₁ - (19 / 500) * n₁₂ + 1 - k * (226 / 125) := by
  have ha : 2 - 81 / 250 + loss ≤ low gain loss := le_max_left _ _
  have hb : 2 - 77 / 500 - gain ≤ low gain loss :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hc : (226 / 125 : ℝ) ≤ low gain loss :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hn : (n₁₁ : ℝ) + n₁₂ ≤ k := by exact_mod_cast hcount
  have h₁ := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n₁₁)
  have h₂ := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg n₁₂)
  have h₃ := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hn)
  nlinarith

/-- The pointwise ordered-incidence inequality, for every blocker count. -/
theorem ordered_incidence_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (t : ℕ) :
    (1 - x) * ((1 + 81 / 250) + (1 - 81 / 250) * (x ^ t - x ^ (2 * t))) ≤
      1 + 81 / 250 := by
  by_cases ht : t = 0
  · subst t; norm_num; linarith
  have hp : 0 ≤ x ^ (2 * t) := pow_nonneg hx _
  have hpow : x ^ t ≤ x := by
    calc
      x ^ t ≤ x ^ 1 := pow_le_pow_of_le_one hx hx1 (by omega)
      _ = x := pow_one x
  have hterm : x ^ t - x ^ (2 * t) ≤ x := by linarith
  have hm := mul_le_mul_of_nonneg_left hterm
    (by positivity : 0 ≤ (1 - x) * (1 - (81 / 250 : ℝ)))
  have hxx : 0 ≤ x * x := mul_nonneg hx hx
  nlinarith

end
end CI2ZF.Appendix.CV
