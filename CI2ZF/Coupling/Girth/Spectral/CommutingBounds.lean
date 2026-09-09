import CI2ZF.Coupling.Girth.Spectral.CommutingEnergy

/-! Identifying explicit conditional sectors and deriving the precise
higher-sector bounds required by the star Schur data. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped BigOperators InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]

namespace CommutingProjections
variable (P : CommutingProjections I E)

theorem mem_sector_iff (χ : I → Bool) (f : E) :
    f ∈ P.sector χ ↔ ∀ i, P.Q i f = if χ i then f else 0 := by
  simp only [sector, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  apply forall_congr'
  intro i
  cases χ i <;> simp [bitValue]

/-- An explicit symmetric conditional-product operator is the sector
projection as soon as its range and fixed vectors are identified. -/
theorem eq_part_of_range (χ : I → Bool) (T : E →ₗ[ℝ] E) (hT : Symmetric T)
    (hrange : ∀ f, T f ∈ P.sector χ) (hfix : ∀ f ∈ P.sector χ, T f = f) (f : E) :
    T f = P.part χ f := by
  apply Eq.symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hrange f)
  intro g hg
  rw [inner_sub_left, hT, hfix g hg, sub_self]

theorem part_on_sector (χ ψ : I → Bool) {f : E} (hf : f ∈ P.sector ψ) :
    P.part χ f = if χ = ψ then f else 0 := by
  by_cases h : χ = ψ
  · subst χ
    rw [if_pos (Eq.refl ψ)]
    exact (P.sector ψ).starProjection_eq_self_iff.mpr hf
  · rw [if_neg h]
    apply (P.sector χ).starProjection_apply_eq_zero_iff.mpr
    exact P.sector_orthogonal.isOrtho (Ne.symm h) hf

theorem weighted_part (β : I → ℝ) (χ : I → Bool) (f : E) :
    P.part χ (P.weighted β f) = sectorWeight β χ • P.part χ f := by
  conv_lhs => rw [← P.sum_parts f]
  rw [map_sum, map_sum]
  simp_rw [P.weighted_action β _ (P.part_mem _ f), map_smul,
    P.part_on_sector _ _ (P.part_mem _ f)]
  simp

/-- Joint-degree support is preserved by every weighted incidence map. -/
theorem weighted_preserves_degrees (β : I → ℝ) (S : Set ℕ) (f : E)
    (hf : ∀ χ, degree χ ∉ S → P.part χ f = 0) :
    ∀ χ, degree χ ∉ S → P.part χ (P.weighted β f) = 0 := by
  intro χ hχ
  rw [P.weighted_part, hf χ hχ, smul_zero]

theorem weighted_positive (β : I → ℝ) (hβ : ∀ i, 0 ≤ β i) : Positive (P.weighted β) := by
  intro f
  rw [P.weighted_energy]
  apply Finset.sum_nonneg
  intro χ _
  exact mul_nonneg (Finset.sum_nonneg fun i _ => hβ i) (sq_nonneg _)

/-- All higher-sector inequalities are consequences of the literal
0<β_i<2 interval and the complete orthogonal decomposition. -/
theorem higher_bounds (β : I → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2) (f : E)
    (hf : ∀ χ, degree χ < 2 → P.part χ f = 0) :
    ‖f‖ ^ 2 ≤ energy P.higher f / 2 ∧
    ‖P.weighted β f‖ ^ 2 ≤ 8 * energy P.higher f ∧
    ‖P.weighted β f - f‖ ^ 2 ≤ (9 / 2 : ℝ) * energy P.higher f := by
  have hpoint (χ : I → Bool) :
      2 * ‖P.part χ f‖ ^ 2 ≤ ((degree χ : ℝ) * (degree χ - 1)) * ‖P.part χ f‖ ^ 2 ∧
      sectorWeight β χ ^ 2 * ‖P.part χ f‖ ^ 2 ≤
        8 * (((degree χ : ℝ) * (degree χ - 1)) * ‖P.part χ f‖ ^ 2) ∧
      (sectorWeight β χ - 1) ^ 2 * ‖P.part χ f‖ ^ 2 ≤
        (9 / 2 : ℝ) * (((degree χ : ℝ) * (degree χ - 1)) * ‖P.part χ f‖ ^ 2) := by
    by_cases hlow : degree χ < 2
    · simp only [hf χ hlow, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl, and_self]
    · have hh := incidence_sector_bounds (active χ) β (fun i _ => hβ i) (Nat.le_of_not_gt hlow)
      have h1 := mul_le_mul_of_nonneg_right hh.1 (sq_nonneg ‖P.part χ f‖)
      have h2 := mul_le_mul_of_nonneg_right hh.2.1 (sq_nonneg ‖P.part χ f‖)
      have h3 := mul_le_mul_of_nonneg_right hh.2.2 (sq_nonneg ‖P.part χ f‖)
      exact ⟨h1, by simpa only [sectorWeight, degree, mul_assoc] using h2,
        by simpa only [sectorWeight, degree, mul_assoc] using h3⟩
  have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (I → Bool))) (fun χ _ => (hpoint χ).1)
  have h2 := Finset.sum_le_sum (s := (Finset.univ : Finset (I → Bool))) (fun χ _ => (hpoint χ).2.1)
  have h3 := Finset.sum_le_sum (s := (Finset.univ : Finset (I → Bool))) (fun χ _ => (hpoint χ).2.2)
  simp only [← Finset.mul_sum, ← P.norm_sq_sum_parts, ← P.weighted_norm_sq,
    ← P.weighted_shift_norm_sq, ← P.higher_energy] at h1 h2 h3
  exact ⟨by linarith, h2, h3⟩

theorem singleton_weighted_norm (β : I → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2) (f : E)
    (hf : ∀ χ, degree χ ≠ 1 → P.part χ f = 0) :
    ‖P.weighted β f‖ ≤ 2 * ‖f‖ := by
  have hpoint (χ : I → Bool) : sectorWeight β χ ^ 2 * ‖P.part χ f‖ ^ 2 ≤ 4 * ‖P.part χ f‖ ^ 2 := by
    by_cases hdeg : degree χ = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdeg
      have he : sectorWeight β χ = β i := by simp [sectorWeight, hi]
      rw [he]
      exact mul_le_mul_of_nonneg_right (by nlinarith [(hβ i).1, (hβ i).2]) (sq_nonneg _)
    · simp only [hf χ hdeg, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (I → Bool))) (fun χ _ => hpoint χ)
  rw [← P.weighted_norm_sq, ← Finset.mul_sum, ← P.norm_sq_sum_parts] at h
  nlinarith [norm_nonneg (P.weighted β f), norm_nonneg f]

theorem singleton_square_energy (β : I → ℝ) (f : E)
    (hf : ∀ χ, degree χ ≠ 1 → P.part χ f = 0) :
    energy (P.weighted (fun i => β i ^ 2)) f = ‖P.weighted β f‖ ^ 2 := by
  rw [P.weighted_energy, P.weighted_norm_sq]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hdeg : degree χ = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdeg
    simp [sectorWeight, hi]
  · simp only [hf χ hdeg, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

end CommutingProjections
end
end CI2ZF.Appendix.Girth.Schur
