import ZeroFreeness.Coupling.Girth.Covariance.Response.Insertion

/-! Both response-block norms for actual finite root and cavity laws.
All colour coordinates, including zero root masses, are retained. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
set_option linter.unusedSectionVars false
variable {C U : Type*} [Fintype C] [Fintype U] [DecidableEq C]

def responseChildSum (r : U → FinDist C) (h : U → C → ℝ) (c : C) : ℝ :=
  ∑ u, Real.sqrt ((r u).w c) * h u c

theorem responseChildSum_point_energy (p : FinDist C) (r : U → FinDist C)
    (h : U → C → ℝ) {Λ : ℝ} (hΛ : ∀ c, p.w c * (∑ u, (r u).w c) ≤ Λ) (c : C) :
    p.w c * responseChildSum r h c ^ 2 ≤ Λ * ∑ u, h u c ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset U)
    (fun u => Real.sqrt ((r u).w c)) (fun u => h u c)
  simp_rw [Real.sq_sqrt ((r _).nonneg c)] at hc
  calc
    _ ≤ p.w c * ((∑ u, (r u).w c) * ∑ u, h u c ^ 2) :=
      mul_le_mul_of_nonneg_left hc (p.nonneg c)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hΛ c) (Finset.sum_nonneg fun u _ => sq_nonneg _)

theorem responseChildSum_variance (p : FinDist C) (r : U → FinDist C)
    (h : U → C → ℝ) {Λ : ℝ} (hΛ : ∀ c, p.w c * (∑ u, (r u).w c) ≤ Λ) :
    variance p (responseChildSum r h) ≤ Λ * ∑ u, colourNorm (h u) ^ 2 := by
  calc
    _ ≤ expectReal p (fun c => responseChildSum r h c ^ 2) := by
      simpa only [sub_zero] using variance_le_error p (responseChildSum r h) 0
    _ ≤ ∑ c, Λ * ∑ u, h u c ^ 2 :=
      Finset.sum_le_sum fun c _ => responseChildSum_point_energy p r h hΛ c
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [colourNorm_sq]

theorem responseBlock_energy (s : ℝ) (p : FinDist C) (r : U → FinDist C)
    (h : U → C → ℝ) {B Λ H : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB : B < 1) (hp : ∀ c, p.w c ≤ B) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ c, p.w c * (∑ u, (r u).w c) ≤ Λ) (_hH : 0 ≤ H)
    (hh : ∀ u, colourNorm (h u) ≤ H) :
    colourNorm (responseBlockAction s p r h) ^ 2 ≤
      (s * Real.sqrt ((Fintype.card U : ℝ) * Λ) / (1 - B) * H) ^ 2 := by
  have hs : (∑ c, responseBlockAction s p r h c ^ 2) =
      s ^ 2 * ∑ c, scoreSource s p (responseChildSum r h) c ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    change (-s * scoreDiagonal s p c * (responseChildSum r h c - expectReal p (responseChildSum r h))) ^ 2 =
      s ^ 2 * (scoreDiagonal s p c * (responseChildSum r h c - expectReal p (responseChildSum r h))) ^ 2
    ring
  have hn : ∑ u, colourNorm (h u) ^ 2 ≤ (Fintype.card U : ℝ) * H ^ 2 := by
    calc
      _ ≤ ∑ _u : U, H ^ 2 := Finset.sum_le_sum fun u _ =>
        pow_le_pow_left₀ (colourNorm_nonneg _) (hh u) 2
      _ = _ := by simp
  rw [colourNorm_sq, hs]
  calc
    _ ≤ s ^ 2 * ((1 / (1 - B)) ^ 2 * variance p (responseChildSum r h)) :=
      mul_le_mul_of_nonneg_left (scoreSource_energy s p _ hs0 hs1 hB hp) (sq_nonneg _)
    _ ≤ s ^ 2 * ((1 / (1 - B)) ^ 2 * (Λ * ∑ u, colourNorm (h u) ^ 2)) := by
      gcongr
      exact responseChildSum_variance p r h hΛ
    _ ≤ s ^ 2 * ((1 / (1 - B)) ^ 2 * (Λ * ((Fintype.card U : ℝ) * H ^ 2))) := by
      gcongr
    _ = _ := by
      simp only [mul_pow, div_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) hΛ0)]
      ring

theorem responseBlock_norm (s : ℝ) (p : FinDist C) (r : U → FinDist C)
    (h : U → C → ℝ) {B Λ H : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB : B < 1) (hp : ∀ c, p.w c ≤ B) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ c, p.w c * (∑ u, (r u).w c) ≤ Λ) (hH : 0 ≤ H)
    (hh : ∀ u, colourNorm (h u) ≤ H) :
    colourNorm (responseBlockAction s p r h) ≤
      s * Real.sqrt ((Fintype.card U : ℝ) * Λ) / (1 - B) * H := by
  apply (sq_le_sq₀ (colourNorm_nonneg _) (by positivity)).mp
  exact responseBlock_energy s p r h hs0 hs1 hB hp hΛ0 hΛ hH hh

theorem responseChildSum_mean_energy (p : FinDist C) (r : U → FinDist C)
    (h : U → C → ℝ) {Λ : ℝ} (hΛ : ∀ c, p.w c * (∑ u, (r u).w c) ≤ Λ) :
    expectReal p (responseChildSum r h) ^ 2 ≤ Λ * ∑ u, colourNorm (h u) ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (U × C))
    (fun uc => p.w uc.2 * Real.sqrt ((r uc.1).w uc.2)) (fun uc => h uc.1 uc.2)
  have hid : (∑ uc : U × C, p.w uc.2 * Real.sqrt ((r uc.1).w uc.2) * h uc.1 uc.2) =
      expectReal p (responseChildSum r h) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [expectReal, responseChildSum, Finset.mul_sum, mul_assoc]
  have hm : (∑ uc : U × C, (p.w uc.2 * Real.sqrt ((r uc.1).w uc.2)) ^ 2) ≤ Λ := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [mul_pow, Real.sq_sqrt ((r _).nonneg _)]
    calc
      _ = ∑ c, p.w c * (p.w c * ∑ u, (r u).w c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← Finset.mul_sum]
        ring
      _ ≤ ∑ c, p.w c * Λ :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hΛ c) (p.nonneg c)
      _ = Λ := by rw [← Finset.sum_mul, p.sum_one, one_mul]
  rw [hid] at hc
  calc
    _ ≤ _ := hc
    _ ≤ Λ * ∑ uc : U × C, h uc.1 uc.2 ^ 2 :=
      mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [Fintype.sum_prod_type]; simp_rw [colourNorm_sq]

theorem responseBlock_infty (s : ℝ) (p : FinDist C) (r : U → FinDist C)
    (h : U → C → ℝ) {B Λ H₂ Hinf : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB : B < 1) (hp : ∀ c, p.w c ≤ B) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ c, p.w c * (∑ u, (r u).w c) ≤ Λ) (hH₂ : 0 ≤ H₂) (hHinf : 0 ≤ Hinf)
    (hh₂ : ∀ u, colourNorm (h u) ≤ H₂) (hhinf : ∀ u c, |h u c| ≤ Hinf) (c : C) :
    |responseBlockAction s p r h c| ≤
      s * Real.sqrt ((Fintype.card U : ℝ) * Λ) / (1 - B) * (Hinf + Real.sqrt B * H₂) := by
  let d : ℝ := Fintype.card U
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hroot : Real.sqrt (d * Λ) ^ 2 = d * Λ := Real.sq_sqrt (mul_nonneg hd0 hΛ0)
  have hn₂ : (∑ u, colourNorm (h u) ^ 2) ≤ d * H₂ ^ 2 := by
    calc
      _ ≤ ∑ _u : U, H₂ ^ 2 := Finset.sum_le_sum fun u _ =>
        pow_le_pow_left₀ (colourNorm_nonneg _) (hh₂ u) 2
      _ = _ := by simp [d]
  have hninf : (∑ u, h u c ^ 2) ≤ d * Hinf ^ 2 := by
    calc
      _ ≤ ∑ _u : U, Hinf ^ 2 := Finset.sum_le_sum fun u _ =>
        by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hHinf).2 (hhinf u c)
      _ = _ := by simp [d]
  have hdiag : |Real.sqrt (p.w c) * responseChildSum r h c| ≤ Real.sqrt (d * Λ) * Hinf := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hHinf)).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt (p.nonneg c), mul_pow, hroot]
    calc
      _ ≤ Λ * ∑ u, h u c ^ 2 := responseChildSum_point_energy p r h hΛ c
      _ ≤ Λ * (d * Hinf ^ 2) := mul_le_mul_of_nonneg_left hninf hΛ0
      _ = _ := by ring
  have hmean : |expectReal p (responseChildSum r h)| ≤ Real.sqrt (d * Λ) * H₂ := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hH₂)).mp
    rw [sq_abs, mul_pow, hroot]
    calc
      _ ≤ Λ * ∑ u, colourNorm (h u) ^ 2 := responseChildSum_mean_energy p r h hΛ
      _ ≤ Λ * (d * H₂ ^ 2) := mul_le_mul_of_nonneg_left hn₂ hΛ0
      _ = _ := by ring
  have hc : 1 - B ≤ 1 - s * p.w c := by nlinarith [p.nonneg c, hp c]
  have hc0 : 0 < 1 - s * p.w c := (sub_pos.mpr hB).trans_le hc
  have hfactor : s / (1 - s * p.w c) ≤ s / (1 - B) :=
    div_le_div_of_nonneg_left hs0 (sub_pos.mpr hB) hc
  have hdev : |Real.sqrt (p.w c) * (responseChildSum r h c - expectReal p (responseChildSum r h))| ≤
      Real.sqrt (d * Λ) * Hinf + Real.sqrt B * (Real.sqrt (d * Λ) * H₂) := by
    rw [mul_sub]
    calc
      _ ≤ |Real.sqrt (p.w c) * responseChildSum r h c| +
          |Real.sqrt (p.w c) * expectReal p (responseChildSum r h)| := abs_sub _ _
      _ ≤ Real.sqrt (d * Λ) * Hinf + Real.sqrt B * (Real.sqrt (d * Λ) * H₂) := by
        apply add_le_add hdiag
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul (Real.sqrt_le_sqrt (hp c)) hmean (abs_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = s / (1 - s * p.w c) *
        |Real.sqrt (p.w c) * (responseChildSum r h c - expectReal p (responseChildSum r h))| := by
      have he : responseBlockAction s p r h c =
          -(s / (1 - s * p.w c)) * (Real.sqrt (p.w c) *
            (responseChildSum r h c - expectReal p (responseChildSum r h))) := by
        unfold responseBlockAction scoreDiagonal responseChildSum
        ring
      rw [he, abs_mul, abs_neg, abs_of_nonneg (div_nonneg hs0 hc0.le)]
    _ ≤ s / (1 - B) * (Real.sqrt (d * Λ) * Hinf + Real.sqrt B * (Real.sqrt (d * Λ) * H₂)) :=
      mul_le_mul hfactor hdev (abs_nonneg _) (div_nonneg hs0 (sub_pos.mpr hB).le)
    _ = _ := by dsimp [d]; ring

end
end ZeroFreeness.Appendix.Girth
