import CI2ZF.Appendix.Girth.Spectral.PlusOperators
import CI2ZF.Appendix.Girth.Spectral.SingletonCompression

/-! All data of the unequal-incidence Schur argument are instantiated
by the actual conditional-star subspaces and actual heat-bath operators. -/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem plusWeighted_additive (β : D → ℝ) (a : S.plusSector) (ha : a ∈ S.additivePlusSpace) :
    S.plusWeighted β a ∈ S.additivePlusSpace := by
  apply (S.additivePlusSpace_mem_iff _).mpr
  exact S.additiveSpace_weighted β ((S.additivePlusSpace_mem_iff a).mp ha)

theorem plusWeighted_singletonComplement (β : D → ℝ) (b : S.plusSector)
    (hb : b ∈ S.singletonComplementSpace) : S.plusWeighted β b ∈ S.singletonComplementSpace := by
  exact S.leafSectors.weighted_preserves_singleton_complement β S.additiveSpace
    (S.weighted_symmetric β) (fun _ ha => S.additiveSpace_weighted β ha) hb

theorem plusWeighted_higher (β : D → ℝ) (h : S.plusSector) (hh : h ∈ S.higherPlusSpace) :
    S.plusWeighted β h ∈ S.higherPlusSpace :=
  S.leafSectors.weighted_preserves_degrees β (Set.Ici 2) h hh

theorem plusHigher_additive (a : S.plusSector) (ha : a ∈ S.additivePlusSpace) : S.plusHigher a = 0 := by
  apply Subtype.ext
  exact S.leafSectors.higher_zero_on_singleton
    (S.additiveSpace_le_singletons ((S.additivePlusSpace_mem_iff a).mp ha))

theorem plusHigher_singletonComplement (b : S.plusSector) (hb : b ∈ S.singletonComplementSpace) :
    S.plusHigher b = 0 := by
  apply Subtype.ext
  exact S.leafSectors.higher_zero_on_singleton hb.1

theorem plus_orth_AB (a b : S.plusSector) (ha : a ∈ S.additivePlusSpace)
    (hb : b ∈ S.singletonComplementSpace) : ⟪a, b⟫_ℝ = 0 :=
  S.leafSectors.additive_singleton_orthogonal S.additiveSpace ((S.additivePlusSpace_mem_iff a).mp ha) hb

theorem plus_orth_AU (a h : S.plusSector) (ha : a ∈ S.additivePlusSpace)
    (hh : h ∈ S.higherPlusSpace) : ⟪a, h⟫_ℝ = 0 :=
  S.leafSectors.additive_higher_orthogonal S.additiveSpace S.additiveSpace_le_singletons
    ((S.additivePlusSpace_mem_iff a).mp ha) hh

theorem plus_orth_BU (b h : S.plusSector) (hb : b ∈ S.singletonComplementSpace)
    (hh : h ∈ S.higherPlusSpace) : ⟪b, h⟫_ℝ = 0 :=
  S.leafSectors.singleton_higher_orthogonal hb.1 hh

theorem plusHigher_bounds (β : D → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2)
    (h : S.plusSector) (hh : h ∈ S.higherPlusSpace) :
    ‖h‖ ^ 2 ≤ @Schur.energy S.plusSector (inferInstance) (inferInstance) S.plusHigher h / 2 ∧
    ‖S.plusWeighted β h‖ ^ 2 ≤ 8 * @Schur.energy S.plusSector (inferInstance) (inferInstance) S.plusHigher h ∧
    ‖S.plusWeighted β h - h‖ ^ 2 ≤ (9 / 2 : ℝ) * @Schur.energy S.plusSector (inferInstance) (inferInstance) S.plusHigher h := by
  exact S.leafSectors.higher_bounds β hβ h (fun χ hχ => hh χ (by change ¬ 2 ≤ _; omega))

namespace SchurParameters
variable {S} (p : S.SchurParameters)

def actualStarData (β : D → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2) :
    @Schur.StarData S.plusSector (inferInstance) (inferInstance) where
  A := S.additivePlusSpace
  B := S.singletonComplementSpace
  U := S.higherPlusSpace
  H := p.residualProjection
  W := S.plusWeighted β
  C := p.correction
  D := S.plusHigher
  L := S.plusWeighted (fun i => β i ^ 2)
  H_projection := p.residual_projection
  W_symmetric := S.plusWeighted_symmetric β
  C_symmetric := p.correction_symmetric
  D_symmetric := S.plusHigher_symmetric
  L_symmetric := S.plusWeighted_symmetric (fun i => β i ^ 2)
  C_positive := p.correction_positive
  L_positive := S.plusWeighted_positive (fun i => β i ^ 2) (fun i => sq_nonneg (β i))
  W_A := S.plusWeighted_additive β
  W_B := S.plusWeighted_singletonComplement β
  W_U := S.plusWeighted_higher β
  L_A := S.plusWeighted_additive (fun i => β i ^ 2)
  H_A := p.residual_additive_zero
  D_A := S.plusHigher_additive
  D_B := S.plusHigher_singletonComplement
  orth_AB := fun a ha b hb => S.plus_orth_AB a b ha hb
  orth_AU := fun a ha h hh => S.plus_orth_AU a h ha hh
  orth_BU := fun b hb h hh => S.plus_orth_BU b h hb hh
  decomposition := S.plus_decomposition
  W_B_positive := fun b _ => S.plusWeighted_positive β (fun i => (hβ i).1.le) b
  W_B_norm := fun b hb => S.leafSectors.singleton_weighted_norm β hβ b hb.1
  U_norm := fun h hh => (S.plusHigher_bounds β hβ h hh).1
  W_U_norm := fun h hh => (S.plusHigher_bounds β hβ h hh).2.1
  W_U_shift := fun h hh => (S.plusHigher_bounds β hβ h hh).2.2
  L_A_energy := fun a ha => S.leafSectors.singleton_square_energy β a
    (S.additiveSpace_le_singletons ((S.additivePlusSpace_mem_iff a).mp ha))

/-- The full zero/positive block Schur form is nonnegative with no
operator estimate left as an input hypothesis. -/
theorem actual_fullCorrection_nonneg (β : D → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2)
    (hd : 0 < Fintype.card D) (x : S.zeroSector) (f : S.plusSector) :
    0 ≤ @Schur.StarData.fullCorrection S.plusSector S.zeroSector (inferInstance) (inferInstance)
      (inferInstance) (inferInstance) (p.actualStarData β hβ) S.starProjectionBlocks.A S.starProjectionBlocks.B p.δ
      (Fintype.card D) x f := by
  exact @Schur.StarData.fullCorrection_nonneg S.plusSector S.zeroSector
    (inferInstance) (inferInstance) (inferInstance) (inferInstance)
    (p.actualStarData β hβ) S.starProjectionBlocks.A p.resolvent
    S.starProjectionBlocks.B (SchurParameters.zeroBlock_symmetric (S := S)) p.zeroBlock_positive p.resolvent_left p.correction_factor
    p.δ (p.bound + p.singletonError) p.bound p.delta_pos p.delta_le_one (add_nonneg p.bound_nonneg p.singletonError_nonneg) p.eta_le p.bound_le
    (fun b hb => p.singleton_residual_lower b hb.1 hb.2) p.correction_le (Fintype.card D) hd p.correction_additive_bound x f

end SchurParameters
end
end CI2ZF.Appendix.Girth.ConditionalStar
