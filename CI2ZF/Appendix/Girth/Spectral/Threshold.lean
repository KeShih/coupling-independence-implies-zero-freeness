import CI2ZF.Appendix.Girth.Analysis.Parameters

/-! The explicit degree threshold and all small constants in the
fixed-girth star Schur estimate, proved on the full parameter interval. -/
namespace CI2ZF.Appendix.Girth
noncomputable section

def girthFiveThreshold (δ : ℝ) : ℕ :=
  ⌈4096 * (1 + δ) * Real.exp (2 / δ) / δ ^ 4⌉₊

def starCap (δ Δ : ℝ) : ℝ := 1 / (δ * Δ)
def starKappa (B : ℝ) : ℝ := B ^ 2 / (1 - B) ^ 2
def starOmega (s B : ℝ) : ℝ := s * B / (1 - B) ^ 2
def starDensityConstant (δ : ℝ) : ℝ := δ / (1 + δ)
def starProjectionBound (δ B s : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * starKappa B * (1 + starOmega s B) ^ (d - 1) / starDensityConstant δ
def starSingletonError (δ B s : ℝ) (d : ℕ) : ℝ :=
  if 2 ≤ d then 2 * (d - 1 : ℕ) * starKappa B * (1 + starOmega s B) ^ (d - 2) /
    (starDensityConstant δ * (1 - B)) else 0
def starUniformBound (δ Δ : ℝ) : ℝ :=
  2 * (1 + δ) * Real.exp (2 / δ) / (δ ^ 3 * Δ)

lemma girthFiveThreshold_le_iff {δ : ℝ} {Δ : ℕ} :
    girthFiveThreshold δ ≤ Δ ↔ 4096 * (1 + δ) * Real.exp (2 / δ) / δ ^ 4 ≤ (Δ : ℝ) := by
  exact Nat.ceil_le

/-- All elementary cap bounds are consequences of the paper's literal
ceiling threshold; no additional asymptotic threshold is introduced. -/
theorem girthFiveThreshold_bounds {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ) :
    0 < (Δ : ℝ) ∧ 2 ≤ δ * Δ ∧ 0 < starCap δ Δ ∧
    starCap δ Δ ≤ δ / (8 * (1 + δ)) ∧ starCap δ Δ ≤ 1 / 8 ∧
    starUniformBound δ Δ ≤ δ / 2048 := by
  have hbase := (girthFiveThreshold_le_iff).mp hΔ
  have hD : 0 < (Δ : ℝ) := (by positivity : 0 < 4096 * (1 + δ) * Real.exp (2 / δ) / δ ^ 4).trans_le hbase
  have he : 1 ≤ Real.exp (2 / δ) := Real.one_le_exp (by positivity)
  have hbase' := (div_le_iff₀ (by positivity : 0 < δ ^ 4)).mp hbase
  have hpow2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hpow4 : δ ^ 4 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
  have hpow4' : δ ^ 4 ≤ δ := by
    have hp := pow_le_one₀ hδ.le hδ1 (n := 3)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4096 * (1 + δ))
  have hd2 := mul_le_mul_of_nonneg_left hpow4 hD.le
  have hd1 := mul_le_mul_of_nonneg_left hpow4' hD.le
  have hcap : starCap δ Δ ≤ δ / (8 * (1 + δ)) := by
    unfold starCap
    apply (div_le_div_iff₀ (mul_pos hδ hD) (by positivity : 0 < 8 * (1 + δ))).mpr
    nlinarith
  have hcsmall : starCap δ Δ ≤ 1 / 8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * (1 + δ))).mp hcap
    have hc0 : 0 ≤ starCap δ Δ := by unfold starCap; positivity
    nlinarith
  refine ⟨hD, by nlinarith, by unfold starCap; positivity, hcap, hcsmall, ?_⟩
  unfold starUniformBound
  apply (div_le_iff₀ (by positivity : 0 < δ ^ 3 * (Δ : ℝ))).mpr
  nlinarith

lemma one_add_nat_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (1 + t) ^ n ≤ Real.exp ((n : ℝ) * t) := by
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t)
    (show 1 + t ≤ Real.exp t by linarith [Real.add_one_le_exp t]) n
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_comm] using hp

lemma starCap_denominator_bounds {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ 1 / 8) :
    0 < 1 - B ∧ 1 / 2 ≤ (1 - B) ^ 2 ∧ 1 / (1 - B) ≤ 2 := by
  refine ⟨by linarith, by nlinarith, ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1 - B)).mpr
  linarith

lemma starKappa_bound {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ 1 / 8) :
    0 ≤ starKappa B ∧ starKappa B ≤ 2 * B ^ 2 := by
  have hd := starCap_denominator_bounds hB0 hB
  constructor
  · unfold starKappa
    positivity
  · unfold starKappa
    apply (div_le_iff₀ (sq_pos_of_pos hd.1)).mpr
    nlinarith [sq_nonneg B]

lemma starOmega_bound {s B : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB : B ≤ 1 / 8) :
    0 ≤ starOmega s B ∧ starOmega s B ≤ 2 * B := by
  have hd := starCap_denominator_bounds hB0 hB
  constructor
  · unfold starOmega
    positivity
  · unfold starOmega
    apply (div_le_iff₀ (sq_pos_of_pos hd.1)).mpr
    have hh := mul_le_mul_of_nonneg_right hs1 hB0
    nlinarith

/-- Both powers in the star bounds are dominated by the same exponential,
uniformly in the actual degree d and activity s. -/
lemma star_power_bound {δ Δ s : ℝ} {d k : ℕ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hd : (d : ℝ) ≤ Δ) (hk : k ≤ d)
    (hB : starCap δ Δ ≤ 1 / 8) :
    (1 + starOmega s (starCap δ Δ)) ^ k ≤ Real.exp (2 / δ) := by
  have hc : 0 ≤ starCap δ Δ := by unfold starCap; positivity
  have ho := starOmega_bound hs hs1 hc hB
  have hkR : (k : ℝ) ≤ Δ := (show (k : ℝ) ≤ d by exact_mod_cast hk).trans hd
  have he : (k : ℝ) * starOmega s (starCap δ Δ) ≤ 2 / δ := by
    calc
      _ ≤ Δ * (2 * starCap δ Δ) :=
        mul_le_mul hkR ho.2 ho.1 hΔ.le
      _ = 2 / δ := by unfold starCap; field_simp
  exact (one_add_nat_pow_le_exp ho.1 k).trans (Real.exp_le_exp.mpr he)

lemma starProjectionBound_nonneg {δ B s : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hs : 0 ≤ s) (d : ℕ) :
    0 ≤ starProjectionBound δ B s d := by
  unfold starProjectionBound starKappa starOmega starDensityConstant
  positivity

lemma starProjectionBound_le_uniform {δ Δ s : ℝ} {d : ℕ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hd : (d : ℝ) ≤ Δ) (hB : starCap δ Δ ≤ 1 / 8) :
    starProjectionBound δ (starCap δ Δ) s d ≤ starUniformBound δ Δ := by
  have hc : 0 ≤ starCap δ Δ := by unfold starCap; positivity
  have hk := starKappa_bound hc hB
  have ho := starOmega_bound hs hs1 hc hB
  have hp := star_power_bound hδ hΔ hs hs1 hd (Nat.sub_le d 1) hB
  have hfirst := mul_le_mul hd hk.2 hk.1 hΔ.le
  have hsecond := mul_le_mul hfirst hp (pow_nonneg (by linarith : 0 ≤ 1 + starOmega s (starCap δ Δ)) _)
    (mul_nonneg hΔ.le (by positivity : 0 ≤ 2 * starCap δ Δ ^ 2))
  have hdiv := div_le_div_of_nonneg_right hsecond
    (show 0 ≤ starDensityConstant δ by unfold starDensityConstant; positivity)
  calc
    _ ≤ Δ * (2 * starCap δ Δ ^ 2) * Real.exp (2 / δ) / starDensityConstant δ := hdiv
    _ = _ := by
      unfold starCap starDensityConstant starUniformBound
      field_simp

lemma starSingletonError_nonneg {δ B s : ℝ}
    (hδ : 0 < δ) (hB0 : 0 ≤ B) (hB : B < 1) (hs : 0 ≤ s) (d : ℕ) :
    0 ≤ starSingletonError δ B s d := by
  unfold starSingletonError
  split_ifs
  · unfold starKappa starOmega starDensityConstant
    positivity
  · exact le_refl 0

lemma starSingletonError_le_four {δ B s : ℝ}
    (hδ : 0 < δ) (hB0 : 0 ≤ B) (hB : B ≤ 1 / 8) (hs : 0 ≤ s) (d : ℕ) :
    starSingletonError δ B s d ≤ 4 * starProjectionBound δ B s d := by
  have hr0 := starProjectionBound_nonneg hδ hB0 hs d
  by_cases hd : 2 ≤ d
  · rw [starSingletonError, if_pos hd]
    have hc : 0 < starDensityConstant δ := by unfold starDensityConstant; positivity
    have hk0 : 0 ≤ starKappa B := by unfold starKappa; positivity
    have ho0 : 0 ≤ starOmega s B := by unfold starOmega; positivity
    have hden := starCap_denominator_bounds hB0 hB
    have hp : (1 + starOmega s B) ^ (d - 2) ≤ (1 + starOmega s B) ^ (d - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hd' : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.sub_le d 1)
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hd' hk0) hp
      (pow_nonneg (by linarith : 0 ≤ 1 + starOmega s B) _) (by positivity : 0 ≤ (d : ℝ) * starKappa B)
    have hh' := div_le_div_of_nonneg_right hh hc.le
    change ((d - 1 : ℕ) : ℝ) * starKappa B * (1 + starOmega s B) ^ (d - 2) /
      starDensityConstant δ ≤ starProjectionBound δ B s d at hh'
    calc
      _ = (2 / (1 - B)) * (((d - 1 : ℕ) : ℝ) * starKappa B *
        (1 + starOmega s B) ^ (d - 2) / starDensityConstant δ) := by
          rw [div_mul_eq_div_div]
          ring
      _ ≤ (2 / (1 - B)) * starProjectionBound δ B s d :=
        mul_le_mul_of_nonneg_left hh' (div_nonneg (by norm_num) hden.1.le)
      _ ≤ 4 * starProjectionBound δ B s d := by
        apply mul_le_mul_of_nonneg_right _ hr0
        have he : 2 / (1 - B) = 2 * (1 / (1 - B)) := by ring
        rw [he]
        linarith [hden.2.2]
  · rw [starSingletonError, if_neg hd]
    positivity

/-- The exact threshold simultaneously supplies every smallness margin
used in the zero block, singleton block, and C correction estimates. -/
theorem girthFive_star_bounds {δ s : ℝ} {Δ d : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hd : d ≤ Δ) :
    0 ≤ starProjectionBound δ (starCap δ Δ) s d ∧
    starProjectionBound δ (starCap δ Δ) s d ≤ δ / 2048 ∧
    0 ≤ starSingletonError δ (starCap δ Δ) s d ∧
    starProjectionBound δ (starCap δ Δ) s d + starSingletonError δ (starCap δ Δ) s d ≤ 5 / 2048 := by
  obtain ⟨hD, _, hc, _, hcsmall, hR⟩ := girthFiveThreshold_bounds hδ hδ1 hΔ
  have hr := (starProjectionBound_le_uniform hδ hD hs hs1 (by exact_mod_cast hd) hcsmall).trans hR
  have he := starSingletonError_le_four hδ hc.le hcsmall hs d
  refine ⟨starProjectionBound_nonneg hδ hc.le hs d, hr,
    starSingletonError_nonneg hδ hc.le (by linarith) hs d, ?_⟩
  linarith

end
end CI2ZF.Appendix.Girth
