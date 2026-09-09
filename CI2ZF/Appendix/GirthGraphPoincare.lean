import CI2ZF.Appendix.GirthGraphGap
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! In finite supported L², the proved quadratic spectral gap gives
Poincaré on the orthogonal complement of the exact kernel. No mixing
inequality is assumed in this conversion. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped BigOperators InnerProductSpace
open Module.End
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every nonzero eigenvalue obeys the quadratic gap. -/
theorem nonzero_eigenvalue_ge_gap (T : E →ₗ[ℝ] E) (hp : Positive T) {γ : ℝ}
    (hgap : ∀ f, γ * energy T f ≤ energy (T.comp T) f)
    {mu : ℝ} (hmu : HasEigenvalue T mu) (hne : mu ≠ 0) : γ ≤ mu := by
  obtain ⟨v, hv, hv0⟩ := hmu.exists_hasEigenvector
  have he : T v = mu • v := mem_eigenspace_iff.mp hv
  have hs : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv0)
  have h1 : energy T v = mu * ‖v‖ ^ 2 := inner_product_apply_eigenvector he
  have h2 : energy (T.comp T) v = mu ^ 2 * ‖v‖ ^ 2 := by
    unfold energy
    rw [LinearMap.comp_apply, he, map_smul, he, smul_smul, real_inner_smul_right,
      real_inner_self_eq_norm_sq, pow_two]
    ring
  have hm0 : 0 ≤ mu := (mul_nonneg_iff_of_pos_right hs).mp (h1 ▸ hp v)
  have hm : 0 < mu := lt_of_le_of_ne hm0 (Ne.symm hne)
  have hh := hgap v
  rw [h1, h2] at hh
  have hscalar : γ * mu ≤ mu ^ 2 := by nlinarith
  nlinarith

/-- The Poincaré inequality on the complement of the kernel, including
zero-dimensional spaces and disconnected configuration supports. -/
theorem poincare_of_square_gap (T : E →ₗ[ℝ] E) (hT : Symmetric T) (hp : Positive T)
    {γ : ℝ} (hgap : ∀ f, γ * energy T f ≤ energy (T.comp T) f)
    (f : E) (hf : ∀ g, T g = 0 → ⟪f, g⟫_ℝ = 0) :
    γ * ‖f‖ ^ 2 ≤ energy T f := by
  have hTs : T.IsSymmetric := hT
  let p (mu : Eigenvalues T) : E := (eigenspace T (mu : ℝ)).starProjection f
  have hpmem (mu : Eigenvalues T) : p mu ∈ eigenspace T (mu : ℝ) :=
    (eigenspace T (mu : ℝ)).starProjection_apply_mem f
  have heigen (mu : Eigenvalues T) : T (p mu) = (mu : ℝ) • p mu := mem_eigenspace_iff.mp (hpmem mu)
  have hspan : (⨆ mu : Eigenvalues T, eigenspace T (mu : ℝ)) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hTs.orthogonalComplement_iSup_eigenspaces_eq_bot'
  have hsum : (∑ mu : Eigenvalues T, p mu) = f :=
    hTs.orthogonalFamily_eigenspaces'.sum_projection_of_mem_iSup f (by rw [hspan]; trivial)
  have hnorm : ‖f‖ ^ 2 = ∑ mu : Eigenvalues T, ‖p mu‖ ^ 2 := by
    have h := hTs.orthogonalFamily_eigenspaces'.norm_sum
      (fun mu => (⟨p mu, hpmem mu⟩ : eigenspace T (mu : ℝ))) Finset.univ
    change ‖∑ mu : Eigenvalues T, p mu‖ ^ 2 = ∑ mu : Eigenvalues T, ‖p mu‖ ^ 2 at h
    rwa [hsum] at h
  have hinner (mu : Eigenvalues T) : ⟪f, p mu⟫_ℝ = ‖p mu‖ ^ 2 := by
    have hproj : Projection ((eigenspace T (mu : ℝ)).starProjection.toLinearMap) :=
      ⟨fun x y => (eigenspace T (mu : ℝ)).inner_starProjection_left_eq_right x y,
        fun x => (eigenspace T (mu : ℝ)).starProjection_eq_self_iff.mpr
          ((eigenspace T (mu : ℝ)).starProjection_apply_mem x)⟩
    exact hproj.inner_self f
  have henergy : energy T f = ∑ mu : Eigenvalues T, (mu : ℝ) * ‖p mu‖ ^ 2 := by
    have hh : T f = ∑ mu : Eigenvalues T, (mu : ℝ) • p mu := by
      conv_lhs => rw [← hsum]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun mu _ => heigen mu)
    rw [energy, hh, inner_sum]
    exact Finset.sum_congr rfl (fun mu _ => by rw [real_inner_smul_right, hinner])
  rw [hnorm, henergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro mu _
  by_cases hz : (mu : ℝ) = 0
  · have hpzero : T (p mu) = 0 := by rw [heigen, hz, zero_smul]
    have hh := hf (p mu) hpzero
    rw [hinner] at hh
    rw [hh, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (nonzero_eigenvalue_ge_gap T hp hgap mu.2 hz) (sq_nonneg _)

end
end CI2ZF.Appendix.Girth.Schur

namespace CI2ZF.Appendix.Girth.GraphProjections
open scoped InnerProductSpace
open Schur
noncomputable section
variable {V E : Type*} [Fintype V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {G : SimpleGraph V} (P : GraphProjections G E)

theorem girth_five_poincare {δ : ℝ} (hδ : 0 < δ) (hg : 5 ≤ G.egirth)
    (hlocal : P.LocalStarBound (StarData.theta δ)) (f : E)
    (hf : ∀ g, P.laplacian g = 0 → ⟪f, g⟫_ℝ = 0) :
    spectralGap δ * ‖f‖ ^ 2 ≤ energy P.laplacian f :=
  poincare_of_square_gap P.laplacian P.laplacian_symmetric P.laplacian_positive
    (P.girth_five_square_gap hδ hg hlocal) f hf

end
end CI2ZF.Appendix.Girth.GraphProjections
