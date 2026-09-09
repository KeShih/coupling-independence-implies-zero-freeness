import CI2ZF.Appendix.GirthSchurLinear

/-! Orthogonal degree blocks and the actual incidence operators. The
hypotheses below describe projection geometry and independently proved
compression bounds; they contain no desired Schur inequality. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped InnerProductSpace
noncomputable section
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure StarData where
  A : Submodule ℝ E
  B : Submodule ℝ E
  U : Submodule ℝ E
  H : E →ₗ[ℝ] E
  W : E →ₗ[ℝ] E
  C : E →ₗ[ℝ] E
  D : E →ₗ[ℝ] E
  L : E →ₗ[ℝ] E
  H_projection : Projection H
  W_symmetric : Symmetric W
  C_symmetric : Symmetric C
  D_symmetric : Symmetric D
  L_symmetric : Symmetric L
  C_positive : Positive C
  L_positive : Positive L
  W_A : ∀ a ∈ A, W a ∈ A
  W_B : ∀ b ∈ B, W b ∈ B
  W_U : ∀ h ∈ U, W h ∈ U
  L_A : ∀ a ∈ A, L a ∈ A
  H_A : ∀ a ∈ A, H a = 0
  D_A : ∀ a ∈ A, D a = 0
  D_B : ∀ b ∈ B, D b = 0
  orth_AB : ∀ a ∈ A, ∀ b ∈ B, ⟪a, b⟫_ℝ = 0
  orth_AU : ∀ a ∈ A, ∀ h ∈ U, ⟪a, h⟫_ℝ = 0
  orth_BU : ∀ b ∈ B, ∀ h ∈ U, ⟪b, h⟫_ℝ = 0
  decomposition : ∀ f, ∃ a ∈ A, ∃ b ∈ B, ∃ h ∈ U, f = a + (b + h)
  W_B_positive : ∀ b ∈ B, 0 ≤ energy W b
  W_B_norm : ∀ b ∈ B, ‖W b‖ ≤ 2 * ‖b‖
  U_norm : ∀ h ∈ U, ‖h‖ ^ 2 ≤ energy D h / 2
  W_U_norm : ∀ h ∈ U, ‖W h‖ ^ 2 ≤ 8 * energy D h
  W_U_shift : ∀ h ∈ U, ‖W h - h‖ ^ 2 ≤ 9 / 2 * energy D h
  L_A_energy : ∀ a ∈ A, energy L a = ‖W a‖ ^ 2

namespace StarData
variable {E} (S : StarData E)

def K (f : E) : ℝ := energy S.H f / 2 + ⟪S.H f, S.W f⟫_ℝ + energy S.D f

def crossK (b h : E) : ℝ :=
  ⟪S.H b, h⟫_ℝ / 2 + ⟪S.H b, S.W h⟫_ℝ / 2 + ⟪S.W b, S.H h⟫_ℝ / 2

theorem K_add (b h : E) (hb : b ∈ S.B) :
    S.K (b + h) = S.K b + 2 * S.crossK b h + S.K h := by
  unfold K crossK
  rw [energy_add S.H S.H_projection.symmetric, energy_add S.D S.D_symmetric]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [← S.D_symmetric, S.D_B b hb, inner_zero_left,
    real_inner_comm (S.H h) (S.W b)]
  rw [S.H_projection.symmetric b h]
  ring

theorem K_add_A (a f : E) (ha : a ∈ S.A) : S.K (a + f) = S.K f := by
  unfold K
  rw [energy_add S.H S.H_projection.symmetric, energy_add S.D S.D_symmetric]
  have hh : energy S.H a = 0 := by simp [energy, S.H_A a ha]
  have hd : energy S.D a = 0 := by simp [energy, S.D_A a ha]
  have hcrossH : ⟪a, S.H f⟫_ℝ = 0 := by rw [← S.H_projection.symmetric, S.H_A a ha, inner_zero_left]
  have hcrossD : ⟪a, S.D f⟫_ℝ = 0 := by rw [← S.D_symmetric, S.D_A a ha, inner_zero_left]
  simp only [hh, hd, hcrossH, hcrossD, map_add, S.H_A a ha, zero_add, inner_add_right]
  have hw : ⟪S.H f, S.W a⟫_ℝ = 0 := by
    rw [S.H_projection.symmetric, S.H_A (S.W a) (S.W_A a ha), inner_zero_right]
  rw [hw]
  ring

theorem higher_lower (h : E) (hh : h ∈ S.U) : energy S.D h / 4 ≤ S.K h := by
  have hc := S.H_projection.completed_square S.W h
  have hs := S.W_U_shift h hh
  unfold K
  linarith

theorem singleton_lower {η : ℝ} (hη : 0 ≤ η)
    (hH : ∀ b ∈ S.B, (1 - η) * ‖b‖ ^ 2 ≤ energy S.H b) (b : E) (hb : b ∈ S.B) :
    (1 / 2 - 5 * η / 2) * ‖b‖ ^ 2 ≤ S.K b := by
  have hi := S.H_projection.defect_inner_bound hη b (S.W b) (hH b hb) (hH _ (S.W_B b hb))
  have hn := mul_le_mul_of_nonneg_left (S.W_B_norm b hb) (mul_nonneg hη (norm_nonneg b))
  have hic : |⟪b - S.H b, S.W b⟫_ℝ| ≤ 2 * η * ‖b‖ ^ 2 := by nlinarith
  have hw := S.W_B_positive b hb
  have hh := hH b hb
  simp only [inner_sub_left] at hic
  have hd : energy S.D b = 0 := by simp [energy, S.D_B b hb]
  unfold K
  rw [hd]
  unfold energy at hw
  nlinarith [le_abs_self (⟪b, S.W b⟫_ℝ - ⟪S.H b, S.W b⟫_ℝ)]

end StarData
end
end CI2ZF.Appendix.Girth.Schur
