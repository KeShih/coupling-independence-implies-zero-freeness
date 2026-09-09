import CI2ZF.Appendix.Girth.Spectral.SupportedSpace

/-! Linear maps on supported finite L². Null-set preservation and
orthogonal projection properties are proved from the actual weighted
expectation identities; no positive atom is assumed off the support. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω] (μ : FinDist Ω)

def WeightedSymmetric (T : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) : Prop :=
  ∀ f g, expectReal μ (fun ω => T f ω * g ω) = expectReal μ (fun ω => f ω * T g ω)

structure SupportedOperator where
  raw : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)
  preserves_null : ∀ f, supportedEmbed μ f = 0 → supportedEmbed μ (raw f) = 0

namespace SupportedOperator

variable {μ} (T : SupportedOperator μ)

def operator : SupportedSpace μ →ₗ[ℝ] SupportedSpace μ :=
  (supportedEmbed μ).comp (T.raw.comp (supportedRepresent μ))

theorem intertwine (f : Ω → ℝ) : T.operator (supportedEmbed μ f) = supportedEmbed μ (T.raw f) := by
  have hz : supportedEmbed μ (f - supportedRepresent μ (supportedEmbed μ f)) = 0 := by
    rw [map_sub, supportedEmbed_represent, sub_self]
  have h := T.preserves_null _ hz
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

theorem symmetric (hT : WeightedSymmetric μ T.raw) (z w : SupportedSpace μ) :
    ⟪T.operator z, w⟫_ℝ = ⟪z, T.operator w⟫_ℝ := by
  have h := hT (supportedRepresent μ z) (supportedRepresent μ w)
  rw [← supportedEmbed_inner, ← supportedEmbed_inner,
    supportedEmbed_represent, supportedEmbed_represent] at h
  exact h

theorem idempotent (hT : ∀ f, T.raw (T.raw f) = T.raw f) (z : SupportedSpace μ) :
    T.operator (T.operator z) = T.operator z := by
  change T.operator (supportedEmbed μ (T.raw (supportedRepresent μ z))) = _
  rw [T.intertwine, hT]
  rfl

end SupportedOperator

/-- Weighted self-adjointness automatically preserves the null space. -/
def supportedOperatorOfSymmetric (T : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hT : WeightedSymmetric μ T) : SupportedOperator μ where
  raw := T
  preserves_null f hf := by
    have h := hT f (T f)
    rw [← supportedEmbed_inner, ← supportedEmbed_inner, hf, inner_zero_left] at h
    exact inner_self_eq_zero.mp h

end

end CI2ZF.Appendix.Girth
