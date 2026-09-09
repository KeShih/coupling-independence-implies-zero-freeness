import CI2ZF.Appendix.Girth.Spectral.CommutingProjections

/-! Exact sector energy formulas for N, W and D=N²-N, with arbitrary
unequal incidence coefficients. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped BigOperators InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]

namespace CommutingProjections
variable (P : CommutingProjections I E)

def active (χ : I → Bool) : Finset I := Finset.univ.filter (fun i => χ i = true)
def degree (χ : I → Bool) : ℕ := (active χ).card
def sectorWeight (β : I → ℝ) (χ : I → Bool) : ℝ := ∑ i ∈ active χ, β i

def weighted (β : I → ℝ) : E →ₗ[ℝ] E := ∑ i, β i • P.Q i
def number : E →ₗ[ℝ] E := P.weighted (fun _ => 1)
def higher : E →ₗ[ℝ] E := P.number.comp P.number - P.number

theorem weighted_action (β : I → ℝ) (χ : I → Bool) {f : E} (hf : f ∈ P.sector χ) :
    P.weighted β f = sectorWeight β χ • f := by
  simp only [weighted, LinearMap.sum_apply, LinearMap.smul_apply, P.sector_action χ hf, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  unfold sectorWeight active
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases χ i <;> simp [bitValue]

theorem sectorWeight_one (χ : I → Bool) : sectorWeight (fun _ => (1 : ℝ)) χ = degree χ := by
  simp [sectorWeight, degree]

theorem number_action (χ : I → Bool) {f : E} (hf : f ∈ P.sector χ) :
    P.number f = (degree χ : ℝ) • f := by
  rw [number, P.weighted_action _ χ hf, sectorWeight_one]

theorem higher_action (χ : I → Bool) {f : E} (hf : f ∈ P.sector χ) :
    P.higher f = ((degree χ : ℝ) * (degree χ - 1)) • f := by
  simp only [higher, LinearMap.sub_apply, LinearMap.comp_apply, P.number_action χ hf, map_smul,
    smul_smul]
  rw [← sub_smul]
  congr 1
  ring

theorem diagonal_energy (T : E →ₗ[ℝ] E) (lam : (I → Bool) → ℝ)
    (hT : ∀ χ (f : E), f ∈ P.sector χ → T f = lam χ • f) (f : E) :
    energy T f = ∑ χ : I → Bool, lam χ * ‖P.part χ f‖ ^ 2 := by
  have he : T f = ∑ χ : I → Bool, lam χ • P.part χ f := by
    conv_lhs => rw [← P.sum_parts f]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun χ _ => hT χ _ (P.part_mem χ f))
  rw [energy, he, inner_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [real_inner_smul_right, (P.part_projection χ).inner_self]

theorem diagonal_norm_sq (T : E →ₗ[ℝ] E) (lam : (I → Bool) → ℝ)
    (hT : ∀ χ (f : E), f ∈ P.sector χ → T f = lam χ • f) (f : E) :
    ‖T f‖ ^ 2 = ∑ χ : I → Bool, lam χ ^ 2 * ‖P.part χ f‖ ^ 2 := by
  have he : T f = ∑ χ : I → Bool, lam χ • P.part χ f := by
    conv_lhs => rw [← P.sum_parts f]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun χ _ => hT χ _ (P.part_mem χ f))
  have h := P.sector_orthogonal.norm_sum
    (fun χ => (lam χ) • (⟨P.part χ f, P.part_mem χ f⟩ : P.sector χ)) Finset.univ
  change ‖∑ χ : I → Bool, lam χ • P.part χ f‖ ^ 2 =
    ∑ χ : I → Bool, ‖lam χ • P.part χ f‖ ^ 2 at h
  rw [he]
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using h

theorem weighted_energy (β : I → ℝ) (f : E) :
    energy (P.weighted β) f = ∑ χ : I → Bool, sectorWeight β χ * ‖P.part χ f‖ ^ 2 :=
  P.diagonal_energy _ _ (fun χ _ hf => P.weighted_action β χ hf) f

theorem weighted_norm_sq (β : I → ℝ) (f : E) :
    ‖P.weighted β f‖ ^ 2 = ∑ χ : I → Bool, sectorWeight β χ ^ 2 * ‖P.part χ f‖ ^ 2 :=
  P.diagonal_norm_sq _ _ (fun χ _ hf => P.weighted_action β χ hf) f

theorem number_energy (f : E) :
    energy P.number f = ∑ χ : I → Bool, (degree χ : ℝ) * ‖P.part χ f‖ ^ 2 :=
  P.diagonal_energy _ _ (fun χ _ hf => P.number_action χ hf) f

theorem higher_energy (f : E) :
    energy P.higher f = ∑ χ : I → Bool, ((degree χ : ℝ) * (degree χ - 1)) * ‖P.part χ f‖ ^ 2 :=
  P.diagonal_energy _ _ (fun χ _ hf => P.higher_action χ hf) f

theorem weighted_shift_norm_sq (β : I → ℝ) (f : E) :
    ‖P.weighted β f - f‖ ^ 2 =
      ∑ χ : I → Bool, (sectorWeight β χ - 1) ^ 2 * ‖P.part χ f‖ ^ 2 := by
  have he (χ : I → Bool) (f : E) (hf : f ∈ P.sector χ) :
      (P.weighted β - (LinearMap.id : E →ₗ[ℝ] E)) f = (sectorWeight β χ - 1) • f := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, P.weighted_action β χ hf,
      sub_smul, one_smul]
  exact P.diagonal_norm_sq _ _ he f

end CommutingProjections
end
end CI2ZF.Appendix.Girth.Schur
