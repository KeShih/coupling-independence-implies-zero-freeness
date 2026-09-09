import CI2ZF.Appendix.Girth.Spectral.SchurData

/-! The mixed singleton/higher block estimate, including its precise
49/8 constant and the retained D/8 Schur margin. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace StarData
variable (S : StarData E)

theorem crossK_defect (b h : E) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    S.crossK b h = -(⟪b - S.H b, h⟫_ℝ + ⟪b - S.H b, S.W h⟫_ℝ +
      ⟪S.W b - S.H (S.W b), h⟫_ℝ) / 2 := by
  simp only [crossK, inner_sub_left, S.orth_BU b hb h hh,
    S.orth_BU b hb (S.W h) (S.W_U h hh),
    S.orth_BU (S.W b) (S.W_B b hb) h hh]
  rw [S.H_projection.symmetric b h, S.H_projection.symmetric (S.W b) h]
  ring

theorem crossK_bound {η : ℝ} (hη : 0 ≤ η)
    (hH : ∀ b ∈ S.B, (1 - η) * ‖b‖ ^ 2 ≤ energy S.H b)
    (b h : E) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    |S.crossK b h| ≤ Real.sqrt η * ‖b‖ * (3 * ‖h‖ + ‖S.W h‖) / 2 := by
  have hbdef := S.H_projection.defect_norm hη b (hH b hb)
  have hwdef := S.H_projection.defect_norm hη (S.W b) (hH _ (S.W_B b hb))
  have hwdef' : ‖S.W b - S.H (S.W b)‖ ≤ 2 * Real.sqrt η * ‖b‖ := by
    have hm := mul_le_mul_of_nonneg_left (S.W_B_norm b hb) (Real.sqrt_nonneg η)
    nlinarith
  have h1 := (abs_real_inner_le_norm (b - S.H b) h).trans
    (mul_le_mul_of_nonneg_right hbdef (norm_nonneg _))
  have h2 := (abs_real_inner_le_norm (b - S.H b) (S.W h)).trans
    (mul_le_mul_of_nonneg_right hbdef (norm_nonneg _))
  have h3 := (abs_real_inner_le_norm (S.W b - S.H (S.W b)) h).trans
    (mul_le_mul_of_nonneg_right hwdef' (norm_nonneg _))
  rw [S.crossK_defect b h hb hh, abs_div, abs_neg]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht := (abs_add_le (⟪b - S.H b, h⟫_ℝ + ⟪b - S.H b, S.W h⟫_ℝ)
    ⟪S.W b - S.H (S.W b), h⟫_ℝ).trans
      (add_le_add (abs_add_le _ _) (le_refl _))
  linarith

theorem crossK_square {η : ℝ} (hη : 0 ≤ η)
    (hH : ∀ b ∈ S.B, (1 - η) * ‖b‖ ^ 2 ≤ energy S.H b)
    (b h : E) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    S.crossK b h ^ 2 ≤ (49 / 8 : ℝ) * η * ‖b‖ ^ 2 * energy S.D h := by
  have hu := S.U_norm h hh
  have hv := S.W_U_norm h hh
  have hscalar : (3 * ‖h‖ + ‖S.W h‖) ^ 2 ≤ (49 / 2 : ℝ) * energy S.D h := by
    nlinarith [sq_nonneg (2 * ‖h‖ - ‖S.W h‖ / 2)]
  have hhbound := S.crossK_bound hη hH b h hb hh
  have hnon : 0 ≤ Real.sqrt η * ‖b‖ * (3 * ‖h‖ + ‖S.W h‖) / 2 := by positivity
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hhbound 2
  rw [sq_abs] at hsq
  have hmult := mul_le_mul_of_nonneg_left hscalar (show 0 ≤ η * ‖b‖ ^ 2 / 4 by positivity)
  have heq : (Real.sqrt η * ‖b‖ * (3 * ‖h‖ + ‖S.W h‖) / 2) ^ 2 =
      η * ‖b‖ ^ 2 / 4 * (3 * ‖h‖ + ‖S.W h‖) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hη]
    ring
  rw [heq] at hsq
  nlinarith

/-- Retaining D/8 leaves loss at most 49 η on the singleton block. -/
theorem crossK_young {η : ℝ} (hη : 0 ≤ η)
    (hH : ∀ b ∈ S.B, (1 - η) * ‖b‖ ^ 2 ≤ energy S.H b)
    (b h : E) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    -(49 * η * ‖b‖ ^ 2 + energy S.D h / 8) ≤ 2 * S.crossK b h := by
  have hsq := S.crossK_square hη hH b h hb hh
  have hd : 0 ≤ energy S.D h := by have := S.U_norm h hh; nlinarith [sq_nonneg ‖h‖]
  have ha : 0 ≤ 49 * η * ‖b‖ ^ 2 := by positivity
  have hab : 0 ≤ 49 * η * ‖b‖ ^ 2 + energy S.D h / 8 := by positivity
  nlinarith [sq_nonneg (49 * η * ‖b‖ ^ 2 - energy S.D h / 8)]

/-- The quantitative coercivity estimate, obtained from the projection
identity rather than assuming an off-diagonal operator norm bound. -/
theorem coercivity {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 5 / 2048)
    (hH : ∀ b ∈ S.B, (1 - η) * ‖b‖ ^ 2 ≤ energy S.H b)
    (a b h : E) (ha : a ∈ S.A) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    ‖b‖ ^ 2 / 4 + energy S.D h / 8 ≤ S.K (a + (b + h)) := by
  rw [S.K_add_A a (b + h) ha, S.K_add b h hb]
  have hsingle := S.singleton_lower hη hH b hb
  have hhigh := S.higher_lower h hh
  have hcross := S.crossK_young hη hH b h hb hh
  have hmargin : 0 ≤ 1 / 4 - (103 / 2 : ℝ) * η := by linarith
  nlinarith [mul_nonneg hmargin (sq_nonneg ‖b‖)]

end StarData
end
end CI2ZF.Appendix.Girth.Schur
