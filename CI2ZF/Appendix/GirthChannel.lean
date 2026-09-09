import CI2ZF.Appendix.GirthHoeffding

/-! Exact leaf-channel means and the conditional-variance lower bound
used in the additive sector of the fixed-girth spectral-gap proof. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem edgeChannel_expect (p : FinDist C) {s : ℝ} (hs : s ≤ 1) (c : C)
    (hd : 0 < 1 - s * p.w c) (h : C → ℝ) :
    expectReal (edgeChannel p s hs c hd) h =
      (expectReal p h - s * p.w c * h c) / (1 - s * p.w c) := by
  unfold expectReal edgeChannel edgeLikelihood
  calc
    _ = (∑ t, p.w t * h t * (1 - s * colourIndicator c t)) / (1 - s * p.w c) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      congr 1
      simp [colourIndicator]
      ring

theorem edgeChannel_centered_variance (p : FinDist C) {s : ℝ} (hs : s ≤ 1) (c : C)
    (hd : 0 < 1 - s * p.w c) (h : C → ℝ) (hmean : expectReal p h = 0) :
    variance (edgeChannel p s hs c hd) h =
      expectReal p (fun t => h t ^ 2) / (1 - s * p.w c) -
        s * p.w c * h c ^ 2 / (1 - s * p.w c) ^ 2 := by
  rw [← covariance_self, covariance_eq_moment]
  rw [edgeChannel_expect p hs c hd h, edgeChannel_expect p hs c hd (fun t => h t * h t), hmean]
  have he : expectReal p (fun t => h t * h t) = expectReal p (fun t => h t ^ 2) := by
    simp only [pow_two]
  rw [he]
  field_simp
  ring

def channelVariance (ν p : FinDist C) (s : ℝ) (hs : s ≤ 1)
    (hd : ∀ c, 0 < 1 - s * p.w c) (h : C → ℝ) : ℝ :=
  expectReal ν (fun c => variance (edgeChannel p s hs c (hd c)) h)

theorem channelVariance_formula (ν p : FinDist C) {s : ℝ} (hs : s ≤ 1)
    (hd : ∀ c, 0 < 1 - s * p.w c) (h : C → ℝ) (hmean : expectReal p h = 0) :
    channelVariance ν p s hs hd h =
      expectReal p (fun t => h t ^ 2) * expectReal ν (fun c => 1 / (1 - s * p.w c)) -
        ∑ c, (s * ν.w c / (1 - s * p.w c) ^ 2) * (p.w c * h c ^ 2) := by
  unfold channelVariance
  simp_rw [edgeChannel_centered_variance p hs _ (hd _) h hmean]
  simp only [expectReal, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro c _ <;> ring

/-- The additive leaf residual retains almost all of its cavity energy.
Only the two raw scaled atom bounds are used. -/
theorem channelVariance_lower (ν p : FinDist C) {s B : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ c, s * p.w c ≤ B) (hν : ∀ c, s * ν.w c ≤ B)
    (h : C → ℝ) (hmean : expectReal p h = 0) :
    (1 - B / (1 - B) ^ 2) * expectReal p (fun t => h t ^ 2) ≤
      channelVariance ν p s hs1 (fun c => by linarith [hp c]) h := by
  let E := expectReal p (fun t => h t ^ 2)
  have hE : 0 ≤ E := Finset.sum_nonneg fun c _ => mul_nonneg (p.nonneg c) (sq_nonneg _)
  have hd (c : C) : 0 < 1 - s * p.w c := by linarith [hp c]
  have hA : 1 ≤ expectReal ν (fun c => 1 / (1 - s * p.w c)) := by
    conv_lhs => rw [← expectReal_const ν 1]
    apply expectReal_mono
    intro c
    apply (le_div_iff₀ (hd c)).mpr
    have hn := mul_nonneg hs (p.nonneg c)
    linarith
  have hcorr : (∑ c, (s * ν.w c / (1 - s * p.w c) ^ 2) * (p.w c * h c ^ 2)) ≤
      (B / (1 - B) ^ 2) * E := by
    change _ ≤ (B / (1 - B) ^ 2) * ∑ c, p.w c * h c ^ 2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    have hden : (1 - B) ^ 2 ≤ (1 - s * p.w c) ^ 2 := by nlinarith [hp c]
    have hb := div_le_div₀ hB (hν c) (by positivity : 0 < (1 - B) ^ 2) hden
    exact mul_le_mul_of_nonneg_right hb (mul_nonneg (p.nonneg c) (sq_nonneg _))
  rw [channelVariance_formula ν p hs1 _ h hmean]
  have hm := mul_le_mul_of_nonneg_left hA hE
  change (1 - B / (1 - B) ^ 2) * E ≤ E * _ - _
  nlinarith

theorem edgeLikelihood_le (p : FinDist C) {s B : ℝ}
    (hs : 0 ≤ s) (hB1 : B < 1) (hp : ∀ c, s * p.w c ≤ B) (c t : C) :
    edgeLikelihood s p c t ≤ 1 / (1 - B) := by
  have hden : 1 - B ≤ 1 - s * p.w c := by linarith [hp c]
  unfold edgeLikelihood
  have hn : 1 - s * colourIndicator c t ≤ 1 := by
    unfold colourIndicator
    split_ifs <;> simp only [mul_one, mul_zero, sub_zero] <;> linarith
  exact div_le_div₀ zero_le_one hn (by linarith) hden

theorem edgeLikelihood_square_le (p : FinDist C) {s B : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB1 : B < 1)
    (hp : ∀ c, s * p.w c ≤ B) (c t : C) :
    edgeLikelihood s p c t ^ 2 ≤ edgeLikelihood s p c t / (1 - B) := by
  have hd : 0 < 1 - s * p.w c := by linarith [hp c]
  have h := mul_le_mul_of_nonneg_left (edgeLikelihood_le p hs hB1 hp c t)
    (edgeLikelihood_nonneg p hs1 c t hd)
  simpa only [pow_two, mul_one_div] using h

/-- A marked leaf in a Hoeffding component changes the Gram bound by
the exact factor `(1-B)⁻¹`; the remaining leaf energy is under its actual
conditional channel. -/
theorem marked_leaf_energy_bound (p : FinDist C) {s B : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hB1 : B < 1)
    (hp : ∀ c, s * p.w c ≤ B) (c : C) (h : C → ℝ) :
    expectReal p (fun t => (h t * edgeLikelihood s p c t) ^ 2) ≤
      (1 / (1 - B)) * expectReal (edgeChannel p s hs1 c (by linarith [hp c])) (fun t => h t ^ 2) := by
  calc
    _ ≤ expectReal p (fun t => h t ^ 2 * (edgeLikelihood s p c t / (1 - B))) := by
      apply expectReal_mono
      intro t
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (edgeLikelihood_square_le p hs hs1 hB1 hp c t) (sq_nonneg _)
    _ = _ := by
      simp only [expectReal, edgeChannel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

end

end CI2ZF.Appendix.Girth
