import CI2ZF.Appendix.Girth.Spectral.SupportedOperator

/-! The genuine mean-zero subspace of supported finite L², together
with restrictions of self-adjoint constant-preserving operators. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

def supportedOne (μ : FinDist Ω) : SupportedSpace μ := supportedEmbed μ (fun _ => 1)

def supportedMean (μ : FinDist Ω) : SupportedSpace μ →ₗ[ℝ] ℝ where
  toFun z := ⟪supportedOne μ, z⟫_ℝ
  map_add' z w := inner_add_right _ _ _
  map_smul' a z := by simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul]

def meanZeroSpace (μ : FinDist Ω) : Submodule ℝ (SupportedSpace μ) := (supportedMean μ).ker

theorem supportedMean_embed (μ : FinDist Ω) (f : Ω → ℝ) :
    supportedMean μ (supportedEmbed μ f) = expectReal μ f := by
  change ⟪supportedEmbed μ (fun _ => 1), supportedEmbed μ f⟫_ℝ = _
  rw [supportedEmbed_inner]
  simp only [one_mul]

theorem supportedOne_mean (μ : FinDist Ω) : supportedMean μ (supportedOne μ) = 1 := by
  rw [supportedOne, supportedMean_embed]
  exact expectReal_const _ 1

theorem mem_meanZeroSpace (μ : FinDist Ω) (z : SupportedSpace μ) :
    z ∈ meanZeroSpace μ ↔ ⟪supportedOne μ, z⟫_ℝ = 0 := Iff.rfl

theorem embed_mem_meanZeroSpace (μ : FinDist Ω) (f : Ω → ℝ) :
    supportedEmbed μ f ∈ meanZeroSpace μ ↔ expectReal μ f = 0 := by
  change supportedMean μ (supportedEmbed μ f) = 0 ↔ _
  rw [supportedMean_embed]

def centeredEmbed (μ : FinDist Ω) (f : Ω → ℝ) : meanZeroSpace μ :=
  ⟨supportedEmbed μ (fun ω => f ω - expectReal μ f),
    (embed_mem_meanZeroSpace μ _).mpr (expectation_centered μ f)⟩

theorem centeredEmbed_norm_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    ‖centeredEmbed μ f‖ ^ 2 = variance μ f := by
  change ‖supportedEmbed μ (fun ω => f ω - expectReal μ f)‖ ^ 2 = _
  exact supportedEmbed_norm_sq μ _

def restrictMeanZero (μ : FinDist Ω) (T : SupportedSpace μ →ₗ[ℝ] SupportedSpace μ)
    (hT : ∀ z w, ⟪T z, w⟫_ℝ = ⟪z, T w⟫_ℝ)
    (h1 : T (supportedOne μ) = supportedOne μ) : meanZeroSpace μ →ₗ[ℝ] meanZeroSpace μ where
  toFun z := ⟨T z, by
    change ⟪supportedOne μ, T z⟫_ℝ = 0
    rw [← hT, h1]
    exact z.property⟩
  map_add' z w := by apply Subtype.ext; exact map_add T z.val w.val
  map_smul' a z := by apply Subtype.ext; exact map_smul T a z.val

theorem restrictMeanZero_apply (μ : FinDist Ω) (T : SupportedSpace μ →ₗ[ℝ] SupportedSpace μ)
    (hT : ∀ z w, ⟪T z, w⟫_ℝ = ⟪z, T w⟫_ℝ)
    (h1 : T (supportedOne μ) = supportedOne μ) (z : meanZeroSpace μ) :
    (restrictMeanZero μ T hT h1 z : SupportedSpace μ) = T z := rfl

theorem restrictMeanZero_symmetric (μ : FinDist Ω) (T : SupportedSpace μ →ₗ[ℝ] SupportedSpace μ)
    (hT : ∀ z w, ⟪T z, w⟫_ℝ = ⟪z, T w⟫_ℝ)
    (h1 : T (supportedOne μ) = supportedOne μ) (z w : meanZeroSpace μ) :
    ⟪restrictMeanZero μ T hT h1 z, w⟫_ℝ = ⟪z, restrictMeanZero μ T hT h1 w⟫_ℝ := hT z w

theorem restrictMeanZero_idempotent (μ : FinDist Ω) (T : SupportedSpace μ →ₗ[ℝ] SupportedSpace μ)
    (hT : ∀ z w, ⟪T z, w⟫_ℝ = ⟪z, T w⟫_ℝ)
    (h1 : T (supportedOne μ) = supportedOne μ) (hTT : ∀ z, T (T z) = T z) (z : meanZeroSpace μ) :
    restrictMeanZero μ T hT h1 (restrictMeanZero μ T hT h1 z) = restrictMeanZero μ T hT h1 z := by
  apply Subtype.ext
  exact hTT z

theorem restrictMeanZero_commute (μ : FinDist Ω)
    (T U : SupportedSpace μ →ₗ[ℝ] SupportedSpace μ)
    (hT : ∀ z w, ⟪T z, w⟫_ℝ = ⟪z, T w⟫_ℝ)
    (hU : ∀ z w, ⟪U z, w⟫_ℝ = ⟪z, U w⟫_ℝ)
    (hT1 : T (supportedOne μ) = supportedOne μ) (hU1 : U (supportedOne μ) = supportedOne μ)
    (hTU : ∀ z, T (U z) = U (T z)) (z : meanZeroSpace μ) :
    restrictMeanZero μ T hT hT1 (restrictMeanZero μ U hU hU1 z) =
      restrictMeanZero μ U hU hU1 (restrictMeanZero μ T hT hT1 z) := by
  apply Subtype.ext
  exact hTU z

end
end CI2ZF.Appendix.Girth
