import CI2ZF.Appendix.BBR.Parameters

/-! The scalar part of the BBR certificate, including the exceptional and
gap-two degree cases. The published weight bound is used only at its
printed hypothesis `d ≥ q+2`; no weakened proposition is assumed. -/
namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open Set
noncomputable section

def start (q Δ : ℕ) : ℝ := if q = 3 ∧ Δ = 4 then 3 / 4 else intervalStart q Δ
def contractionSquare (Δ : ℕ) : ℝ := ((Δ : ℝ) - 1) / Δ
def contractionRate (Δ : ℕ) : ℝ := Real.sqrt (contractionSquare Δ)

theorem start_mem {q Δ : ℕ} (hq : 3 ≤ q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / q) :
    start q Δ ∈ Ioo (0 : ℝ) 1 := by
  unfold start
  split_ifs with he
  · exact exceptional_interval
  · exact intervalStart_mem_Ioo hq hr he

theorem contractionSquare_mem {Δ : ℕ} (hΔ : 2 ≤ Δ) : contractionSquare Δ ∈ Ioo (0 : ℝ) 1 := by
  have hd : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  unfold contractionSquare
  exact ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

theorem contractionRate_mem {Δ : ℕ} (hΔ : 2 ≤ Δ) : contractionRate Δ ∈ Ioo (0 : ℝ) 1 := by
  have h := contractionSquare_mem hΔ
  refine ⟨Real.sqrt_pos.2 h.1, ?_⟩
  have hs := Real.sq_sqrt h.1.le
  have hn := Real.sqrt_nonneg (contractionSquare Δ)
  unfold contractionRate
  nlinarith [h.2]

theorem contractionRate_sq {Δ : ℕ} (hΔ : 2 ≤ Δ) : contractionRate Δ ^ 2 = contractionSquare Δ :=
  Real.sq_sqrt (contractionSquare_mem hΔ).1.le

def weightBase (Δ k : ℝ) : ℝ := Real.exp 1 * (Δ - k / 2) / (Δ - k)
def publishedWeightBound (q Δ f : ℝ) : ℝ :=
  (1 / q / (1 - parameter q Δ / Δ) ^ 2) *
    Real.exp ((1 - f / (Δ - 1)) * Real.log (parameter q Δ) +
      (f / (Δ - 1)) * Real.log (weightBase Δ (parameter q Δ)))

theorem intervalStart_ge_basic {q Δ : ℝ} (hq : 0 < q) (hqd : q < Δ)
    (hk : 0 < parameter q Δ) (hkd : parameter q Δ < Δ) :
    1 - q / Δ ≤ intervalStart q Δ := by
  have hd : 0 < Δ := hq.trans hqd
  have ha0 : 0 ≤ 1 - parameter q Δ / Δ := by linarith [(div_lt_one hd).2 hkd]
  have ha1 : 1 - parameter q Δ / Δ ≤ 1 := by linarith [div_pos hk hd]
  have ha2 : (1 - parameter q Δ / Δ) ^ 2 ≤ 1 := by nlinarith
  have hden : 0 < Δ - parameter q Δ / 2 := by linarith
  have hr0 : 0 ≤ (Δ - parameter q Δ) / (Δ - parameter q Δ / 2) :=
    div_nonneg (sub_nonneg.mpr hkd.le) hden.le
  have hr1 : (Δ - parameter q Δ) / (Δ - parameter q Δ / 2) ≤ 1 := (div_le_one hden).2 (by linarith)
  have ha := mul_le_mul_of_nonneg_left ha2 (div_pos hq hd).le
  have hh := mul_le_mul_of_nonneg_left hr1
    (mul_nonneg (div_pos hq hd).le (sq_nonneg (1 - parameter q Δ / Δ)))
  unfold intervalStart
  rw [← mul_div_assoc] at hh
  nlinarith

theorem weighted_geometric_max {k B t : ℝ} (_hk : 0 < k) (hB : 0 < B)
    (ht : t ∈ Icc (0 : ℝ) 1) (hlog : Real.log k - Real.log B ≤ 1) :
    t * Real.exp ((1 - t) * Real.log k + t * Real.log B) ≤ B := by
  have hm := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr ht.2)
  have hexp := Real.exp_le_exp.mpr (show
      (1 - t) * Real.log k + t * Real.log B ≤ Real.log B + (1 - t) by nlinarith)
  have htan := Real.add_one_le_exp (t - 1)
  have ht' : t * Real.exp (1 - t) ≤ 1 := by
    calc
      _ ≤ Real.exp (t - 1) * Real.exp (1 - t) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc
    _ ≤ t * Real.exp (Real.log B + (1 - t)) := mul_le_mul_of_nonneg_left hexp ht.1
    _ = B * (t * Real.exp (1 - t)) := by rw [Real.exp_add, Real.exp_log hB]; ring
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left ht' hB.le
    _ = B := mul_one _

theorem weightBase_log_gap {q Δ : ℝ} (hq : 0 < q)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ Δ / q)
    (hkΔ : parameter q Δ < Δ) :
    0 < weightBase Δ (parameter q Δ) ∧
      Real.log (parameter q Δ) - Real.log (weightBase Δ (parameter q Δ)) ≤ 1 := by
  have hk := parameter_pos hq (degree_gt_colours hq hr)
  have he := Real.exp_pos 1
  have hB : Real.exp 1 ≤ weightBase Δ (parameter q Δ) := by
    unfold weightBase
    apply (le_div_iff₀ (sub_pos.mpr hkΔ)).2
    nlinarith
  have hB0 := he.trans_le hB
  have hklog : Real.log (parameter q Δ) ≤ 2 := by
    have hh := Real.log_le_log hk (parameter_le_exp_sq hq hr)
    simpa only [Real.log_pow, Real.log_exp, Nat.cast_ofNat, mul_one] using hh
  have hBlog : 1 ≤ Real.log (weightBase Δ (parameter q Δ)) := by
    simpa only [Real.log_exp] using Real.log_le_log he hB
  exact ⟨hB0, by linarith⟩

/-- Maximization in the free-child count is proved, rather than included
in the imported local-weight estimate. -/
theorem certificate_of_published_bound {q Δ f x L : ℝ} (hq : 0 < q) (hd : 1 < Δ)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ Δ / q)
    (hkΔ : parameter q Δ < Δ) (hf : f ∈ Icc (0 : ℝ) (Δ - 1))
    (hx : intervalStart q Δ ≤ x) (hx1 : x ≤ 1)
    (hL : L ≤ publishedWeightBound q Δ f) :
    f * ((1 - x) / Real.exp 1) * L ≤ (Δ - 1) / Δ := by
  let k := parameter q Δ
  let B := weightBase Δ k
  let a := 1 - k / Δ
  have hΔ : 0 < Δ := by linarith
  have hk : 0 < k := parameter_pos hq (degree_gt_colours hq hr)
  have hdk : 0 < Δ - k := sub_pos.mpr hkΔ
  have hdk2 : 0 < Δ - k / 2 := by linarith
  have ha : 0 < a := sub_pos.mpr ((div_lt_one hΔ).2 hkΔ)
  have hd0 : 0 < Δ - 1 := by linarith
  have hB := weightBase_log_gap hq hr hkΔ
  have hB0 : 0 < B := hB.1
  have hmax := weighted_geometric_max hk hB.1
    (show f / (Δ - 1) ∈ Icc (0 : ℝ) 1 from
      ⟨div_nonneg hf.1 hd0.le, (div_le_one hd0).2 hf.2⟩) hB.2
  have hmax' : f * Real.exp ((1 - f / (Δ - 1)) * Real.log k +
      (f / (Δ - 1)) * Real.log B) ≤ (Δ - 1) * B := by
    let E := Real.exp ((1 - f / (Δ - 1)) * Real.log k + (f / (Δ - 1)) * Real.log B)
    have h : (Δ - 1) * (f / (Δ - 1) * E) ≤ (Δ - 1) * B :=
      mul_le_mul_of_nonneg_left hmax hd0.le
    have heq : (Δ - 1) * (f / (Δ - 1) * E) = f * E := by field_simp [hd0.ne']
    rw [heq] at h
    exact h
  have hL' : f * L ≤ (1 / q / a ^ 2) * ((Δ - 1) * B) := by
    calc
      _ ≤ f * publishedWeightBound q Δ f := mul_le_mul_of_nonneg_left hL hf.1
      _ = (1 / q / a ^ 2) * (f * Real.exp ((1 - f / (Δ - 1)) * Real.log k +
          (f / (Δ - 1)) * Real.log B)) := by unfold publishedWeightBound; dsimp [a, k, B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmax' (by positivity)
  have hx' : 1 - x ≤ q / Δ * a ^ 2 * (Δ - k) / (Δ - k / 2) := by
    unfold intervalStart at hx
    dsimp [a, k]
    linarith
  calc
    _ = ((1 - x) / Real.exp 1) * (f * L) := by ring
    _ ≤ ((1 - x) / Real.exp 1) * ((1 / q / a ^ 2) * ((Δ - 1) * B)) :=
      mul_le_mul_of_nonneg_left hL' (by positivity)
    _ ≤ (q / Δ * a ^ 2 * (Δ - k) / (Δ - k / 2) / Real.exp 1) *
        ((1 / q / a ^ 2) * ((Δ - 1) * B)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hx' (Real.exp_pos _).le) (by positivity)
    _ = _ := by
      dsimp [B, weightBase]
      have h2 : Δ * 2 - k ≠ 0 := by linarith
      field_simp [hq.ne', hΔ.ne', ha.ne', hdk.ne', hdk2.ne', h2, (Real.exp_pos 1).ne']

theorem gap_two_colours_le_six {q Δ : ℕ} (hq : 3 ≤ q) (hgap : Δ = q + 2)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / q) : q ≤ 6 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h := (ratio_iff hq0).1 hr
  have hd : (Δ : ℝ) = q + 2 := by exact_mod_cast hgap
  have he : Real.exp 1 < 11 / 4 := Real.exp_one_lt_d9.trans (by norm_num)
  rw [hd] at h
  have hq7 : (q : ℝ) < 7 := by nlinarith
  have : q < 7 := by exact_mod_cast hq7
  omega

/-- The omitted gap-two cases have an elementary stronger annulus. -/
theorem gap_two_start_lower {q Δ : ℕ} (hq : 3 ≤ q) (hgap : Δ = q + 2)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / q) :
    (15 / 16 : ℝ) ≤ intervalStart q Δ := by
  have hq6 := gap_two_colours_le_six hq hgap hr
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq6r : (q : ℝ) ≤ 6 := by exact_mod_cast hq6
  have hd : (Δ : ℝ) = q + 2 := by exact_mod_cast hgap
  have hΔ : (0 : ℝ) < Δ := by linarith
  have hkΔ := parameter_lt_degree hq (show q + 2 ≤ Δ by omega)
  have hk0 := parameter_pos (show (0 : ℝ) < q by linarith) (show (q : ℝ) < Δ by linarith)
  have hk : 3 / 4 ≤ parameter q Δ / Δ := by
    apply (le_div_iff₀ hΔ).2
    unfold parameter
    rw [hd]
    have he : (5 / 2 : ℝ) < Real.exp 1 := (by norm_num : (5 / 2 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
    have hm := mul_le_mul_of_nonneg_right he.le (show 0 ≤ (q : ℝ) / 2 + 2 by linarith)
    have hden : (q : ℝ) + 2 - q = 2 := by ring
    rw [hden]
    nlinarith
  have ha0 : 0 ≤ 1 - parameter q Δ / Δ := by linarith [(div_lt_one hΔ).2 hkΔ]
  have ha : (1 - parameter q Δ / Δ) ^ 2 ≤ 1 / 16 := by nlinarith
  have hqΔ : (q : ℝ) / Δ ≤ 1 := (div_le_one hΔ).2 (by linarith)
  have hr1 : ((Δ : ℝ) - parameter q Δ) / (Δ - parameter q Δ / 2) ≤ 1 :=
    (div_le_one (by linarith : (0 : ℝ) < Δ - parameter q Δ / 2)).2 (by linarith)
  have hp1 := mul_le_mul_of_nonneg_right hqΔ (sq_nonneg (1 - parameter q Δ / Δ))
  have hp0 : 0 ≤ (q : ℝ) / Δ * (1 - parameter q Δ / Δ) ^ 2 := by positivity
  have hp2 := mul_le_mul_of_nonneg_left hr1 hp0
  unfold intervalStart
  rw [← mul_div_assoc] at hp2
  nlinarith

/-- The crude annular estimate suffices whenever `x≥15/16`, `q≥3`,
and `Δ≤8`, covering every gap-two pair. -/
theorem small_degree_certificate {q Δ f : ℕ} {x L : ℝ}
    (hq : 3 ≤ q) (hΔ : 2 ≤ Δ) (hΔ8 : Δ ≤ 8) (hf : f ≤ Δ - 1)
    (hx : (15 / 16 : ℝ) ≤ x) (hx1 : x ≤ 1) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / ((q : ℝ) * x ^ (Δ + 1))) :
    (f : ℝ) * ((1 - x) / Real.exp 1) * L ≤ contractionSquare Δ := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hd0 : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hd1 : (1 : ℝ) ≤ Δ := by exact_mod_cast (show 1 ≤ Δ by omega)
  have h1mx : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hfp : (f : ℝ) ≤ (Δ : ℝ) - 1 := by
    have hh : (f : ℝ) + 1 ≤ Δ := by exact_mod_cast (show f + 1 ≤ Δ by omega)
    linarith
  have hp : (1 / 2 : ℝ) ≤ x ^ (Δ + 1) := by
    have h9 : (1 / 2 : ℝ) ≤ (15 / 16 : ℝ) ^ (9 : ℕ) := by norm_num
    exact h9.trans ((pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 15 / 16)
      (by norm_num) (show Δ + 1 ≤ 9 by omega)).trans (pow_le_pow_left₀ (by norm_num) hx _))
  have hfactor : ((1 - x) / Real.exp 1) * (1 / ((q : ℝ) * x ^ (Δ + 1))) ≤ 1 / Δ := by
    have he := Real.exp_one_gt_two
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    have hd8 : (Δ : ℝ) ≤ 8 := by exact_mod_cast hΔ8
    have hden : (0 : ℝ) < q * x ^ (Δ + 1) := by positivity
    have hsmall : (1 - x) * (Δ : ℝ) ≤ Real.exp 1 * ((q : ℝ) * x ^ (Δ + 1)) := by
      have hm1 := mul_le_mul_of_nonneg_left hp hq0.le
      have hm2 := mul_le_mul_of_nonneg_right hd8 (sub_nonneg.mpr hx1)
      have hm3 := mul_le_mul_of_nonneg_left hm1 (Real.exp_pos 1).le
      nlinarith
    calc
      _ = (1 - x) / (Real.exp 1 * ((q : ℝ) * x ^ (Δ + 1))) := by ring
      _ ≤ _ := (div_le_div_iff₀ (mul_pos (Real.exp_pos 1) hden) hd0).2 (by simpa using hsmall)
  calc
    _ ≤ ((Δ : ℝ) - 1) * (((1 - x) / Real.exp 1) * (1 / ((q : ℝ) * x ^ (Δ + 1)))) := by
      rw [← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hfp (by positivity)) hL hL0 (by positivity)
    _ ≤ ((Δ : ℝ) - 1) * (1 / Δ) := mul_le_mul_of_nonneg_left hfactor (by linarith)
    _ = contractionSquare Δ := by unfold contractionSquare; ring

theorem exceptional_certificate {f : ℕ} {x L : ℝ} (hf : f ≤ 3)
    (hx : (3 / 4 : ℝ) ≤ x) (hx1 : x ≤ 1) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / (3 * x ^ 5)) :
    (f : ℝ) * ((1 - x) / Real.exp 1) * L ≤ 3 / 4 := by
  have hx0 : 0 < x := by linarith
  have hmx : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hx 5
  have hp : 0 < x ^ 5 := pow_pos hx0 _
  have he := Real.exp_one_gt_two
  have hh := mul_le_mul_of_nonneg_left hpow (Real.exp_pos 1).le
  have hfactor : (1 - x) / Real.exp 1 * (1 / (3 * x ^ 5)) ≤ 1 / 4 := by
    calc
      _ = (1 - x) / (Real.exp 1 * (3 * x ^ 5)) := by ring
      _ ≤ _ := (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)).2 (by norm_num at hpow hh; nlinarith)
  have hf3 : (f : ℝ) ≤ 3 := by exact_mod_cast hf
  calc
    _ ≤ 3 * (((1 - x) / Real.exp 1) * (1 / (3 * x ^ 5))) := by
      rw [← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hf3 (by positivity)) hL hL0 (by positivity)
    _ ≤ 3 * (1 / 4) := mul_le_mul_of_nonneg_left hfactor (by norm_num)
    _ = _ := by ring

end
end CI2ZF.Appendix.BBR
