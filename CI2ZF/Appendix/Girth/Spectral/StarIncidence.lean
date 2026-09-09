import CI2ZF.Appendix.Girth.Spectral.ActualSchurData

/-! Reassembly of the actual centre and positive leaf blocks into the
unequal-incidence star inequality on supported mean-zero L². -/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem root_plus_inner (x : S.zeroSector) (f : S.plusSector) :
    ⟪(x : meanZeroSpace S.jointLaw), (f : meanZeroSpace S.jointLaw)⟫_ℝ = 0 := f.property x x.property

theorem plus_root_inner (f : S.plusSector) (x : S.zeroSector) :
    ⟪(f : meanZeroSpace S.jointLaw), (x : meanZeroSpace S.jointLaw)⟫_ℝ = 0 := by
  rw [real_inner_comm, S.root_plus_inner]

theorem root_P_inner (x y : S.zeroSector) :
    ⟪(x : meanZeroSpace S.jointLaw), S.centreMeanHeatBath y⟫_ℝ = ⟪x, S.starProjectionBlocks.T y⟫_ℝ := by
  rw [S.starProjectionBlocks_T_apply]
  exact (S.zeroSector.inner_orthogonalProjectionOnto_eq_of_mem_left x _).symm

theorem root_plus_P_inner (x : S.zeroSector) (f : S.plusSector) :
    ⟪(x : meanZeroSpace S.jointLaw), S.centreMeanHeatBath f⟫_ℝ = ⟪x, S.starProjectionBlocks.B f⟫_ℝ := by
  rw [S.starProjectionBlocks_B_apply]
  exact (S.zeroSector.inner_orthogonalProjectionOnto_eq_of_mem_left x _).symm

theorem plus_root_P_inner (f : S.plusSector) (x : S.zeroSector) :
    ⟪(f : meanZeroSpace S.jointLaw), S.centreMeanHeatBath x⟫_ℝ = ⟪x, S.starProjectionBlocks.B f⟫_ℝ := by
  rw [← S.centreMeanHeatBath_projection.symmetric, real_inner_comm, S.root_plus_P_inner]

theorem plus_P_inner (f g : S.plusSector) :
    ⟪(f : meanZeroSpace S.jointLaw), S.centreMeanHeatBath g⟫_ℝ = ⟪f, S.starProjectionBlocks.D g⟫_ℝ := by
  rw [S.starProjectionBlocks_D_apply]
  exact (S.plusSector.inner_orthogonalProjectionOnto_eq_of_mem_left f _).symm

theorem weighted_zeroSector (β : D → ℝ) (x : S.zeroSector) :
    S.leafSectors.weighted β (x : meanZeroSpace S.jointLaw) = 0 := by
  rw [S.leafSectors.weighted_action β (fun _ => false) x.property]
  simp [Schur.CommutingProjections.sectorWeight, Schur.CommutingProjections.active]

theorem higher_zeroSector (x : S.zeroSector) :
    S.leafSectors.higher (x : meanZeroSpace S.jointLaw) = 0 := by
  change S.leafSectors.weighted (fun _ => 1) (S.leafSectors.weighted (fun _ => 1) x) -
    S.leafSectors.weighted (fun _ => 1) x = 0
  rw [S.weighted_zeroSector, map_zero, sub_self]

/-- This is Tβ−Q/2+(θ/(2d))Σβ²Qi, written as its exact quadratic form. -/
def meanStarDefect (β : D → ℝ) (δ : ℝ) (z : meanZeroSpace S.jointLaw) : ℝ :=
  ⟪z, z - S.centreMeanHeatBath z⟫_ℝ / 2 +
    ⟪z - S.centreMeanHeatBath z, S.leafSectors.weighted β z⟫_ℝ +
    Schur.energy S.leafSectors.higher z + Schur.StarData.theta δ / (2 * Fintype.card D) *
      Schur.energy (S.leafSectors.weighted (fun i => β i ^ 2)) z

namespace SchurParameters
variable {S} (p : S.SchurParameters)

set_option maxHeartbeats 800000 in
theorem fullCorrection_eq_starDefect (β : D → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2)
    (x : S.zeroSector) (f : S.plusSector) :
    @Schur.StarData.fullCorrection S.plusSector S.zeroSector (inferInstance) (inferInstance)
      (inferInstance) (inferInstance) (p.actualStarData β hβ) S.starProjectionBlocks.A S.starProjectionBlocks.B
      p.δ (Fintype.card D) x f = S.meanStarDefect β p.δ ((x : meanZeroSpace S.jointLaw) + f) := by
  change (@Schur.energy S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.A x / 2 -
      ⟪x, S.starProjectionBlocks.B (f + S.plusWeighted β f)⟫_ℝ +
      @Schur.energy S.plusSector (inferInstance) (inferInstance) (p.residualProjection + p.correction) f / 2 +
      ⟪(p.residualProjection + p.correction) f, S.plusWeighted β f⟫_ℝ +
      @Schur.energy S.plusSector (inferInstance) (inferInstance) S.plusHigher f + Schur.StarData.theta p.δ / (2 * Fintype.card D) *
        @Schur.energy S.plusSector (inferInstance) (inferInstance) (S.plusWeighted (fun i => β i ^ 2)) f) = _
  rw [p.residual_add_correction]
  have hw : S.leafSectors.weighted β ((x : meanZeroSpace S.jointLaw) + f) =
      (S.plusWeighted β f : meanZeroSpace S.jointLaw) := by rw [map_add, S.weighted_zeroSector, zero_add]; rfl
  have hl : S.leafSectors.weighted (fun i => β i ^ 2) ((x : meanZeroSpace S.jointLaw) + f) =
      (S.plusWeighted (fun i => β i ^ 2) f : meanZeroSpace S.jointLaw) := by
    rw [map_add, S.weighted_zeroSector, zero_add]; rfl
  have hd : S.leafSectors.higher ((x : meanZeroSpace S.jointLaw) + f) =
      (S.plusHigher f : meanZeroSpace S.jointLaw) := by rw [map_add, S.higher_zeroSector, zero_add]; rfl
  unfold meanStarDefect
  rw [hw]
  change _ = _ + _ + ⟪(x : meanZeroSpace S.jointLaw) + f,
    S.leafSectors.higher ((x : meanZeroSpace S.jointLaw) + f)⟫_ℝ + _ *
    ⟪(x : meanZeroSpace S.jointLaw) + f, S.leafSectors.weighted (fun i => β i ^ 2)
      ((x : meanZeroSpace S.jointLaw) + f)⟫_ℝ
  rw [hd, hl]
  simp only [Schur.energy, Schur.ProjectionBlocks.A_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_add, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    S.root_plus_inner, S.plus_root_inner, S.root_P_inner, S.root_plus_P_inner, S.plus_root_P_inner,
    S.plus_P_inner, real_inner_self_eq_norm_sq]
  have hcrossRoot : ⟪S.centreMeanHeatBath (x : meanZeroSpace S.jointLaw),
      (S.plusWeighted β f : meanZeroSpace S.jointLaw)⟫_ℝ =
      ⟪x, S.starProjectionBlocks.B (S.plusWeighted β f)⟫_ℝ := by
    rw [S.centreMeanHeatBath_projection.symmetric, S.root_plus_P_inner]
  have hcrossPlus : ⟪S.centreMeanHeatBath (f : meanZeroSpace S.jointLaw),
      (S.plusWeighted β f : meanZeroSpace S.jointLaw)⟫_ℝ =
      ⟪S.starProjectionBlocks.D f, S.plusWeighted β f⟫_ℝ := by
    calc
      _ = ⟪(S.plusWeighted β f : meanZeroSpace S.jointLaw),
          S.centreMeanHeatBath (f : meanZeroSpace S.jointLaw)⟫_ℝ := real_inner_comm _ _
      _ = ⟪S.plusWeighted β f, S.starProjectionBlocks.D f⟫_ℝ := S.plus_P_inner _ _
      _ = _ := real_inner_comm _ _
  rw [hcrossRoot, hcrossPlus]
  simp only [Submodule.coe_inner, Submodule.coe_sub, Submodule.coe_add,
    inner_sub_right, inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq, Submodule.norm_coe]
  ring

/-- The actual unequal-incidence star bound on the supported mean-zero
space, including every off-diagonal sector contribution. -/
theorem meanStarDefect_nonneg (β : D → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2)
    (hd : 0 < Fintype.card D) (z : meanZeroSpace S.jointLaw) : 0 ≤ S.meanStarDefect β p.δ z := by
  let x := S.zeroSector.orthogonalProjectionOnto z
  let f := S.plusSector.orthogonalProjectionOnto z
  have he : (x : meanZeroSpace S.jointLaw) + f = z := S.zeroSector.starProjection_add_starProjection_orthogonal z
  rw [← he, ← p.fullCorrection_eq_starDefect β hβ x f]
  exact p.actual_fullCorrection_nonneg β hβ hd x f

end SchurParameters
end
end CI2ZF.Appendix.Girth.ConditionalStar
