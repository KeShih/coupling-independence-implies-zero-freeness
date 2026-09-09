import CI2ZF.Appendix.GirthSchurEstimate

/-! Reassembling the degree-zero block gives the unequal-incidence star
inequality. The coefficient L is the literal incidence-square operator;
H+C is the positive-sector block of I-P. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped InnerProductSpace
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

namespace StarData
variable (S : StarData E)

/-- Exact quadratic form of Tβ-Q/2+(θ/(2d)) L in degree blocks. Here A
is I-P00 and B is P0+. The identity H+C=I-P++ is used in this expression. -/
def fullCorrection (A : F →ₗ[ℝ] F) (B : E →ₗ[ℝ] F) (δ : ℝ) (d : ℕ) (x : F) (f : E) : ℝ :=
  energy A x / 2 - ⟪x, B (f + S.W f)⟫_ℝ +
    energy (S.H + S.C) f / 2 + ⟪(S.H + S.C) f, S.W f⟫_ℝ +
    energy S.D f + theta δ / (2 * d) * energy S.L f

/-- Algebraic cancellation of the full Schur correction, including all
terms linear and quadratic in the unequal incidence operator W. -/
theorem fullCorrection_eq (A R : F →ₗ[ℝ] F) (B : E →ₗ[ℝ] F)
    (hAR : ∀ x, A (R x) = x)
    (hC : ∀ f, energy S.C f = ⟪B f, R (B f)⟫_ℝ)
    (δ : ℝ) (d : ℕ) (x : F) (f : E) :
    S.fullCorrection A B δ d x f =
      energy A x / 2 - ⟪x, B (f + S.W f)⟫_ℝ +
      energy A (R (B (f + S.W f))) / 2 +
      (S.K f - energy S.C (S.W f) / 2 + theta δ / (2 * d) * energy S.L f) := by
  have he : energy A (R (B (f + S.W f))) = energy S.C (f + S.W f) := by
    rw [hC, energy, hAR, real_inner_comm]
  rw [he, energy_add S.C S.C_symmetric]
  unfold fullCorrection K energy
  simp only [LinearMap.add_apply, inner_add_right, inner_add_left]
  rw [S.C_symmetric]
  ring

/-- The full star form is positive after eliminating its invertible
zero-degree block. This is the final unequal-incidence inequality. -/
theorem fullCorrection_nonneg (A R : F →ₗ[ℝ] F) (B : E →ₗ[ℝ] F)
    (hA : Symmetric A) (hp : Positive A) (hAR : ∀ x, A (R x) = x)
    (hfactor : ∀ f, energy S.C f = ⟪B f, R (B f)⟫_ℝ)
    {δ η r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 ≤ η) (hη1 : η ≤ 5 / 2048) (hr : r ≤ δ / 2048)
    (hH : ∀ b ∈ S.B, (1 - η) * ‖b‖ ^ 2 ≤ energy S.H b)
    (hC : ∀ f, energy S.C f ≤ r * ‖f‖ ^ 2) {d : ℕ} (hd : 0 < d)
    (hCA : ∀ a ∈ S.A, (d : ℝ) * energy S.C a ≤ ‖a‖ ^ 2 / (1 + δ / 2)) (x : F) (f : E) :
    0 ≤ S.fullCorrection A B δ d x f := by
  rw [S.fullCorrection_eq A R B hAR hfactor]
  exact zero_block_completion A R hA hp hAR x (B (f + S.W f)) _
    (S.schur_positive hδ hδ1 hη hη1 hr hH hC hd hCA f)

end StarData
end
end CI2ZF.Appendix.Girth.Schur
