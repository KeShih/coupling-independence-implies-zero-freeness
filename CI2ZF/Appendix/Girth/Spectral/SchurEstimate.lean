import CI2ZF.Appendix.Girth.Spectral.SchurCross

/-! Absorbing the C correction and eliminating the degree-zero block. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace StarData
variable (S : StarData E)

theorem W_complement_energy (b h : E) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    ‖S.W (b + h)‖ ^ 2 ≤ 4 * ‖b‖ ^ 2 + 8 * energy S.D h := by
  have horth := S.orth_BU (S.W b) (S.W_B b hb) (S.W h) (S.W_U h hh)
  have hrev : ⟪S.W h, S.W b⟫_ℝ = 0 := by rw [real_inner_comm]; exact horth
  rw [map_add, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, horth, hrev, real_inner_self_eq_norm_sq]
  have hbnd := pow_le_pow_left₀ (norm_nonneg _) (S.W_B_norm b hb) 2
  have hhnd := S.W_U_norm h hh
  nlinarith

theorem L_additive_lower (a b h : E) (ha : a ∈ S.A) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    ‖S.W a‖ ^ 2 ≤ energy S.L (a + (b + h)) := by
  rw [energy_add S.L S.L_symmetric, S.L_A_energy a ha]
  have hcross : ⟪a, S.L (b + h)⟫_ℝ = 0 := by
    rw [← S.L_symmetric, inner_add_right, S.orth_AB (S.L a) (S.L_A a ha) b hb,
      S.orth_AU (S.L a) (S.L_A a ha) h hh]
    ring
  rw [hcross]
  linarith [S.L_positive (b + h)]

/-- The only numeric loss from C is at most 1/32, uniformly in δ. -/
theorem correction_factor {δ r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : r ≤ δ / 2048) :
    (1 + 4 / δ) * r ≤ 1 / 32 := by
  have hf : 0 ≤ 1 + 4 / δ := by positivity
  calc
    _ ≤ (1 + 4 / δ) * (δ / 2048) := mul_le_mul_of_nonneg_left hr hf
    _ = (δ + 4) / 2048 := by field_simp
    _ ≤ _ := by linarith

def theta (δ : ℝ) : ℝ := (1 + δ / 4) / (1 + δ / 2)

theorem theta_mem {δ : ℝ} (hδ : 0 < δ) : theta δ ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold theta
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).2
    linarith

/-- The C Young estimate, after using the exact additive incidence square
and retaining the degree-one/higher energy in the complementary block. -/
theorem correction_bound {δ r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : r ≤ δ / 2048)
    (hC : ∀ f, energy S.C f ≤ r * ‖f‖ ^ 2) {d : ℕ} (hd : 0 < d)
    (hCA : ∀ a ∈ S.A, (d : ℝ) * energy S.C a ≤ ‖a‖ ^ 2 / (1 + δ / 2))
    (a b h : E) (ha : a ∈ S.A) (hb : b ∈ S.B) (hh : h ∈ S.U) :
    energy S.C (S.W (a + (b + h))) ≤
      theta δ / d * energy S.L (a + (b + h)) + ‖b‖ ^ 2 / 8 + energy S.D h / 4 := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hδden : 0 < 1 + δ / 2 := by positivity
  have hε : 0 < δ / 4 := by positivity
  have hy := positive_young S.C S.C_symmetric S.C_positive hε (S.W a) (S.W (b + h))
  have hca := hCA (S.W a) (S.W_A a ha)
  have hca' : energy S.C (S.W a) ≤ ‖S.W a‖ ^ 2 / (1 + δ / 2) / d :=
    (le_div_iff₀ hd0).2 (by nlinarith)
  have hcf := hC (S.W (b + h))
  have hfirst : (1 + δ / 4) * energy S.C (S.W a) ≤
      theta δ / d * energy S.L (a + (b + h)) := by
    calc
      _ ≤ (1 + δ / 4) * (‖S.W a‖ ^ 2 / (1 + δ / 2) / d) :=
        mul_le_mul_of_nonneg_left hca' (by positivity)
      _ = theta δ / d * ‖S.W a‖ ^ 2 := by unfold theta; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (S.L_additive_lower a b h ha hb hh)
        (div_nonneg (theta_mem hδ).1.le hd0.le)
  have hsecond : (1 + 1 / (δ / 4)) * energy S.C (S.W (b + h)) ≤
      ‖b‖ ^ 2 / 8 + energy S.D h / 4 := by
    calc
      _ ≤ (1 + 1 / (δ / 4)) * (r * ‖S.W (b + h)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcf (by positivity)
      _ = ((1 + 4 / δ) * r) * ‖S.W (b + h)‖ ^ 2 := by ring
      _ ≤ (1 / 32) * ‖S.W (b + h)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (correction_factor hδ hδ1 hr) (sq_nonneg _)
      _ ≤ (1 / 32) * (4 * ‖b‖ ^ 2 + 8 * energy S.D h) :=
        mul_le_mul_of_nonneg_left (S.W_complement_energy b h hb hh) (by norm_num)
      _ = _ := by ring
  rw [map_add]
  linarith

/-- The precise Schur complement of the unequal-incidence star operator
is positive. Its proof contains every numerical margin from the appendix. -/
theorem schur_positive {δ η r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 ≤ η) (hη1 : η ≤ 5 / 2048) (hr : r ≤ δ / 2048)
    (hH : ∀ b ∈ S.B, (1 - η) * ‖b‖ ^ 2 ≤ energy S.H b)
    (hC : ∀ f, energy S.C f ≤ r * ‖f‖ ^ 2) {d : ℕ} (hd : 0 < d)
    (hCA : ∀ a ∈ S.A, (d : ℝ) * energy S.C a ≤ ‖a‖ ^ 2 / (1 + δ / 2)) (f : E) :
    0 ≤ S.K f - energy S.C (S.W f) / 2 + theta δ / (2 * d) * energy S.L f := by
  obtain ⟨a, ha, b, hb, h, hh, rfl⟩ := S.decomposition f
  have hk := S.coercivity hη hη1 hH a b h ha hb hh
  have hc := S.correction_bound hδ hδ1 hr hC hd hCA a b h ha hb hh
  have hid : theta δ / (2 * d) * energy S.L (a + (b + h)) =
      (theta δ / d * energy S.L (a + (b + h))) / 2 := by ring
  rw [hid]
  nlinarith [sq_nonneg ‖b‖]

end StarData

/-- The final degree-zero Schur elimination, expressed directly as a
quadratic form identity. Only an actual positive zero block and its
algebraic inverse are used. -/
theorem zero_block_completion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A R : F →ₗ[ℝ] F) (hA : Symmetric A) (hp : Positive A)
    (hAR : ∀ x, A (R x) = x) (x v : F) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ energy A x / 2 - ⟪x, v⟫_ℝ + energy A (R v) / 2 + s := by
  have h := hp (x - R v)
  simp only [energy, map_sub, inner_sub_left, inner_sub_right, hAR] at h
  have hc : ⟪R v, A x⟫_ℝ = ⟪x, v⟫_ℝ := by
    rw [← hA, hAR, real_inner_comm]
  rw [hc] at h
  have he : energy A (R v) = ⟪R v, v⟫_ℝ := by rw [energy, hAR]
  rw [he]
  unfold energy
  linarith

end
end CI2ZF.Appendix.Girth.Schur
