import ZeroFreeness.Coupling.CV.Arithmetic

/-! Infinite-multiplicity and degree-budget arithmetic in the CV averaging
step. Unlike a finite regression scan, these proofs quantify every multiplicity. -/
namespace ZeroFreeness.Appendix.CV
noncomputable section

lemma singleton_binomial_weight_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * (1 - x) * x ^ k ≤ 1 := by
  have hs := Finset.single_le_sum (s := Finset.range (k + 1 + 1))
    (f := fun j => x ^ j * (1 - x) ^ (k + 1 - j) * ((k + 1).choose j : ℝ))
    (fun j _ => mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg (sub_nonneg.mpr hx.2) _))
      (Nat.cast_nonneg _)) (show k ∈ Finset.range (k + 1 + 1) by simp)
  rw [← add_pow] at hs
  simpa [Nat.choose_succ_self_right, mul_comm, mul_left_comm, mul_assoc] using hs

/-- The probability factor used for every physical multiplicity at least three. -/
theorem high_multiplicity_probability_bound {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 3 ≤ m) :
    (1 - x) * x ^ (m - 3) * (1 + ((m - 2 : ℕ) : ℝ) * (1 - x)) ≤ 2 := by
  have ht0 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have ht1 : 1 - x ≤ 1 := by linarith [hx.1]
  have hp0 : 0 ≤ x ^ (m - 3) := pow_nonneg hx.1 _
  have hp1 : x ^ (m - 3) ≤ 1 := pow_le_one₀ hx.1 hx.2
  have ha := mul_le_mul ht1 hp1 hp0 (by norm_num : (0 : ℝ) ≤ 1)
  have hb := singleton_binomial_weight_le_one hx (m - 3)
  have he : m - 3 + 1 = m - 2 := by omega
  rw [he] at hb
  have hb0 : 0 ≤ ((m - 2 : ℕ) : ℝ) * (1 - x) * x ^ (m - 3) := by positivity
  have hb' := mul_le_mul ht1 hb hb0 (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

/-- The high physical-multiplicity averaged rate never exceeds the bulk rate. -/
theorem averaged_high_rate {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 3 ≤ m) :
    bulk * (1 - x) + ((919 / 500) - bulk) * (1 - x) * x ^ (m - 2) *
      (1 + ((m - 2 : ℕ) : ℝ) * (1 - x)) ≤ bulk := by
  have h := high_multiplicity_probability_bound hx hm
  have he : m - 2 = (m - 3) + 1 := by omega
  have hpow : x ^ (m - 2) = x ^ (m - 3) * x := by rw [he, pow_succ]
  rw [hpow]
  have h' := mul_le_mul_of_nonneg_left h hx.1
  unfold bulk at *
  nlinarith [hx.1]

/-- The witness budget has exactly the form needed by the drift envelope. -/
theorem degree_resource {L H B Lx Δ : ℝ} (hdegree : L + H + B ≤ Δ) :
    (L - Lx) + H + B ≤ Δ - Lx := by linarith

/-- The finite-binomial averaging coefficient is strictly below the bulk
budget, including the contribution of missing colour baselines. -/
lemma averaging_constants :
    (743 / 500 : ℝ) < bulk ∧ 1 < bulk ∧
    0 < (919 / 500 : ℝ) - bulk ∧
    0 < 3 * bulk - 2 * (919 / 500 : ℝ) := by norm_num [bulk]

end
end ZeroFreeness.Appendix.CV
