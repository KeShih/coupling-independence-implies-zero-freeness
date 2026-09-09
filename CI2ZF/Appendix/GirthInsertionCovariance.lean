import CI2ZF.Appendix.GirthInsertionLaw

/-! From the actual one-coordinate variance estimates and Poincaré to
colour covariance, and from colour covariance to both source norms. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C U W : Type*} [Fintype Ω] [Fintype C] [Fintype U] [Fintype W]

theorem covariance_const_mul_right (μ : FinDist Ω) (f g : Ω → ℝ) (a : ℝ) :
    covariance μ f (fun ω => a * g ω) = a * covariance μ f g := by
  rw [covariance_eq_moment, covariance_eq_moment, expectReal_const_mul]
  have he : expectReal μ (fun t => f t * (a * g t)) = a * expectReal μ (fun t => f t * g t) := by
    rw [← expectReal_const_mul]
    congr 1
    funext t
    ring
  rw [he]
  ring

theorem covariance_sum_right (μ : FinDist Ω) (f : Ω → ℝ) (G : C → Ω → ℝ) :
    covariance μ f (fun ω => ∑ c, G c ω) = ∑ c, covariance μ f (G c) := by
  simp only [covariance_eq_moment, Finset.mul_sum, expectReal_sum, Finset.sum_sub_distrib]

/-- The quadratic form is exactly the covariance matrix of the colour
coordinates; no matrix-norm conclusion is assumed. -/
def ColourCovarianceBound (μ : FinDist Ω) (G : C → Ω → ℝ) (K : ℝ) : Prop :=
  ∀ z : C → ℝ, variance μ (fun ω => ∑ c, z c * G c ω) ≤ K * ∑ c, z c ^ 2

/-- Disjoint second-layer blocks enter only through their total size.
All coordinate energies are evaluated under the true, possibly dependent,
base law. -/
theorem colourCovariance_of_coordinate_bounds (μ : FinDist Ω)
    (G : C → Ω → ℝ) (β : U → C → Ω → ℝ) (owner : W → U)
    (D : W → (Ω → ℝ) → Ω → ℝ) {γ B L b Δ : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hΔ : (Fintype.card W : ℝ) ≤ Δ ^ 2)
    (hP : ∀ f, γ * variance μ f ≤ ∑ w, expectReal μ (D w f))
    (hD : ∀ (z : C → ℝ) w ω, D w (fun t => ∑ c, z c * G c t) ω ≤
      B * L ^ 2 * ∑ c, z c ^ 2 * β (owner w) c ω ^ 2)
    (hβ : ∀ u c, expectReal μ (fun ω => β u c ω ^ 2) ≤ b ^ 2) :
    ColourCovarianceBound μ G (Δ ^ 2 * B * L ^ 2 / γ * b ^ 2) := by
  intro z
  have hpoint (w : W) : expectReal μ (D w (fun t => ∑ c, z c * G c t)) ≤
      B * L ^ 2 * b ^ 2 * ∑ c, z c ^ 2 := by
    calc
      _ ≤ expectReal μ (fun ω => B * L ^ 2 * ∑ c, z c ^ 2 * β (owner w) c ω ^ 2) :=
        expectReal_mono μ (hD z w)
      _ = B * L ^ 2 * ∑ c, z c ^ 2 * expectReal μ (fun ω => β (owner w) c ω ^ 2) := by
        rw [expectReal_const_mul, expectReal_sum]
        simp_rw [expectReal_const_mul]
      _ ≤ B * L ^ 2 * ∑ c, z c ^ 2 * b ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hβ (owner w) c) (sq_nonneg _))
          (mul_nonneg hB (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hs := (hP (fun t => ∑ c, z c * G c t)).trans (Finset.sum_le_sum fun w _ => hpoint w)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hh : γ * variance μ (fun t => ∑ c, z c * G c t) ≤
      Δ ^ 2 * (B * L ^ 2 * b ^ 2 * ∑ c, z c ^ 2) :=
    hs.trans (mul_le_mul_of_nonneg_right hΔ
      (mul_nonneg (mul_nonneg (mul_nonneg hB (sq_nonneg _)) (sq_nonneg _))
        (Finset.sum_nonneg fun c _ => sq_nonneg _)))
  calc
    _ ≤ (Δ ^ 2 * (B * L ^ 2 * b ^ 2 * ∑ c, z c ^ 2)) / γ :=
      (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by ring

theorem covariance_vector_energy (μ : FinDist Ω) (G : C → Ω → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hG : ColourCovarianceBound μ G K) (f : Ω → ℝ) :
    (∑ c, covariance μ f (G c) ^ 2) ≤ variance μ f * K := by
  let z : C → ℝ := fun c => covariance μ f (G c)
  let e : ℝ := ∑ c, z c ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hid : covariance μ f (fun ω => ∑ c, z c * G c ω) = e := by
    rw [covariance_sum_right]
    simp_rw [covariance_const_mul_right]
    simp only [e, z, pow_two]
  have hc := covariance_sq_le μ f (fun ω => ∑ c, z c * G c ω)
  rw [hid] at hc
  have hh : e ^ 2 ≤ (variance μ f * K) * e := hc.trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hG z) (variance_nonneg μ f))
  change e ≤ variance μ f * K
  by_cases hz : e = 0
  · rw [hz]
    exact mul_nonneg (variance_nonneg μ f) hK
  · have hep : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    by_contra hn
    have ht : 0 < e * (e - variance μ f * K) := mul_pos hep (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hh, ht]

theorem weighted_covariance_vector_energy (μ : FinDist Ω) (G : C → Ω → ℝ) {K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hG : ColourCovarianceBound μ G K)
    (p : FinDist C) (hp : ∀ c, p.w c ≤ B) (f : Ω → ℝ) :
    (∑ c, (Real.sqrt (p.w c) * covariance μ f (G c)) ^ 2) ≤ B * variance μ f * K := by
  calc
    _ = ∑ c, p.w c * covariance μ f (G c) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [mul_pow, Real.sq_sqrt (p.nonneg c)]
    _ ≤ ∑ c, B * covariance μ f (G c) ^ 2 :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hp c) (sq_nonneg _)
    _ = B * ∑ c, covariance μ f (G c) ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ B * (variance μ f * K) :=
      mul_le_mul_of_nonneg_left (covariance_vector_energy μ G hK hG f) hB
    _ = _ := by ring

end
end CI2ZF.Appendix.Girth
