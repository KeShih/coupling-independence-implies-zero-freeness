import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-! Elementary Hilbert-space identities used in the unequal-incidence
star Schur estimate. No spectral or star inequality is assumed. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Symmetric (T : E →ₗ[ℝ] E) : Prop := ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ
def energy (T : E →ₗ[ℝ] E) (x : E) : ℝ := ⟪x, T x⟫_ℝ
def Positive (T : E →ₗ[ℝ] E) : Prop := ∀ x, 0 ≤ energy T x

theorem energy_add (T : E →ₗ[ℝ] E) (hT : Symmetric T) (x y : E) :
    energy T (x + y) = energy T x + 2 * ⟪x, T y⟫_ℝ + energy T y := by
  simp only [energy, map_add, inner_add_left, inner_add_right]
  rw [← hT y x, real_inner_comm (T y) x]
  ring

theorem positive_young (T : E →ₗ[ℝ] E) (hT : Symmetric T) (hp : Positive T)
    {ε : ℝ} (hε : 0 < ε) (x y : E) :
    energy T (x + y) ≤ (1 + ε) * energy T x + (1 + 1 / ε) * energy T y := by
  have hh := hp (ε • x - y)
  simp only [energy, map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right] at hh
  rw [← hT y x, real_inner_comm (T y) x] at hh
  rw [energy_add T hT]
  have hc : ⟪T y, x⟫_ℝ = ⟪x, T y⟫_ℝ := real_inner_comm _ _
  rw [hc] at hh
  apply (mul_le_mul_iff_right₀ hε).mp
  have he : ε * ((1 + ε) * energy T x + (1 + 1 / ε) * energy T y) =
      (ε + ε ^ 2) * energy T x + (ε + 1) * energy T y := by
    field_simp [hε.ne']
  rw [he]
  unfold energy
  nlinarith

structure Projection (H : E →ₗ[ℝ] E) : Prop where
  symmetric : Symmetric H
  idem : ∀ x, H (H x) = H x

namespace Projection
variable {H : E →ₗ[ℝ] E} (hH : Projection H)
include hH

theorem inner_self (x : E) : ⟪x, H x⟫_ℝ = ‖H x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, hH.symmetric, hH.idem]

theorem defect_energy (x : E) : ‖x - H x‖ ^ 2 = ‖x‖ ^ 2 - energy H x := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (H x) x, ← hH.inner_self]
  unfold energy
  simp only [show ⟪H x, x⟫_ℝ = ⟪x, H x⟫_ℝ from real_inner_comm _ _]
  ring

theorem defect_inner (x y : E) : ⟪x - H x, y⟫_ℝ = ⟪x - H x, y - H y⟫_ℝ := by
  simp only [inner_sub_left, inner_sub_right]
  rw [hH.symmetric, hH.symmetric, hH.idem]
  ring

theorem defect_norm {η : ℝ} (hη : 0 ≤ η) (x : E)
    (hx : (1 - η) * ‖x‖ ^ 2 ≤ energy H x) :
    ‖x - H x‖ ≤ Real.sqrt η * ‖x‖ := by
  have hh := hH.defect_energy x
  have hs := Real.sq_sqrt hη
  have hn : 0 ≤ Real.sqrt η * ‖x‖ := by positivity
  nlinarith [norm_nonneg (x - H x)]

theorem defect_inner_bound {η : ℝ} (hη : 0 ≤ η) (x y : E)
    (hx : (1 - η) * ‖x‖ ^ 2 ≤ energy H x)
    (hy : (1 - η) * ‖y‖ ^ 2 ≤ energy H y) :
    |⟪x - H x, y⟫_ℝ| ≤ η * ‖x‖ * ‖y‖ := by
  rw [hH.defect_inner]
  calc
    _ ≤ ‖x - H x‖ * ‖y - H y‖ := abs_real_inner_le_norm _ _
    _ ≤ (Real.sqrt η * ‖x‖) * (Real.sqrt η * ‖y‖) :=
      mul_le_mul (hH.defect_norm hη x hx) (hH.defect_norm hη y hy)
        (norm_nonneg _) (by positivity)
    _ = (Real.sqrt η) ^ 2 * (‖x‖ * ‖y‖) := by ring
    _ = _ := by rw [Real.sq_sqrt hη]; ring

/-- Completing the square preserves all off-diagonal parts of H. -/
theorem completed_square (W : E →ₗ[ℝ] E) (x : E) :
    energy H x / 2 + ⟪H x, W x⟫_ℝ ≥ -(‖W x - x‖ ^ 2) / 6 := by
  have hh := sq_nonneg ‖H x + (1 / 3 : ℝ) • (W x - x)‖
  rw [← real_inner_self_eq_norm_sq] at hh
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_sub_left, inner_sub_right] at hh
  rw [real_inner_comm (W x) (H x), real_inner_comm x (H x),
    real_inner_self_eq_norm_sq, ← hH.inner_self] at hh
  have hb : ‖W x - x‖ ^ 2 = ⟪W x, W x⟫_ℝ - ⟪W x, x⟫_ℝ - ⟪x, W x⟫_ℝ + ⟪x, x⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  simp only [show ⟪W x, H x⟫_ℝ = ⟪H x, W x⟫_ℝ from real_inner_comm _ _] at hh
  unfold energy
  nlinarith

end Projection
end
end CI2ZF.Appendix.Girth.Schur
