import ZeroFreeness.Coupling.Girth.Spectral.StarOperators
import ZeroFreeness.Coupling.Girth.Spectral.StarCentre
import ZeroFreeness.Coupling.Girth.Spectral.ProjectionBlocks
import ZeroFreeness.Coupling.Girth.Spectral.Threshold

/-! The actual degree-zero and positive-sector blocks of the conditional
star centre heat bath, on supported mean-zero L². -/
namespace ZeroFreeness.Appendix.Girth.ConditionalStar
open scoped BigOperators InnerProductSpace
open PottsCI Finset Schur
noncomputable section
attribute [local instance] Classical.propDecidable
variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

def plusSector : Submodule ℝ (meanZeroSpace S.jointLaw) := S.zeroSectorᗮ

/-- This is the literal block matrix of the actual centre heat bath. -/
def starProjectionBlocks : Schur.ProjectionBlocks S.zeroSector S.plusSector :=
  Schur.ProjectionBlocks.ofSplit S.centreMeanHeatBath S.centreMeanHeatBath_projection
    S.zeroSector.subtype S.plusSector.subtype
    S.zeroSector.orthogonalProjectionOnto.toLinearMap S.plusSector.orthogonalProjectionOnto.toLinearMap
    (fun z x => S.zeroSector.inner_orthogonalProjectionOnto_eq_of_mem_right x z)
    (fun z x => S.plusSector.inner_orthogonalProjectionOnto_eq_of_mem_right x z)
    (fun z => S.zeroSector.starProjection_add_starProjection_orthogonal z)

lemma starProjectionBlocks_T_apply (x : S.zeroSector) :
    S.starProjectionBlocks.T x = S.zeroSector.orthogonalProjectionOnto (S.centreMeanHeatBath x) := rfl

lemma starProjectionBlocks_B_apply (x : S.plusSector) :
    S.starProjectionBlocks.B x = S.zeroSector.orthogonalProjectionOnto (S.centreMeanHeatBath x) := rfl

lemma starProjectionBlocks_Bt_apply (x : S.zeroSector) :
    S.starProjectionBlocks.Bt x = S.plusSector.orthogonalProjectionOnto (S.centreMeanHeatBath x) := rfl

lemma starProjectionBlocks_D_apply (x : S.plusSector) :
    S.starProjectionBlocks.D x = S.plusSector.orthogonalProjectionOnto (S.centreMeanHeatBath x) := rfl

lemma starProjectionBlocks_T_energy (x : S.zeroSector) :
    @energy S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.T x = energy S.centreMeanHeatBath (x : meanZeroSpace S.jointLaw) := by
  unfold energy
  rw [S.starProjectionBlocks_T_apply]
  exact S.zeroSector.inner_orthogonalProjectionOnto_eq_of_mem_left x _

lemma starProjectionBlocks_D_energy (x : S.plusSector) :
    @energy S.plusSector (inferInstance) (inferInstance) S.starProjectionBlocks.D x = energy S.centreMeanHeatBath (x : meanZeroSpace S.jointLaw) := by
  unfold energy
  rw [S.starProjectionBlocks_D_apply]
  exact S.plusSector.inner_orthogonalProjectionOnto_eq_of_mem_left x _

/-- The zero-block compression estimate follows from the true root-only
representation of that sector and the proved centre-numerator expansion. -/
theorem zeroBlock_energy_le {B c₀ : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) (hc : 0 < c₀)
    (hp : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (hν : ∀ c, S.s * S.centreLaw.w c ≤ B)
    (hR : ∀ σ, c₀ ≤ S.leafDensity σ) (x : S.zeroSector) :
    @energy S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.T x ≤
      ((Fintype.card D : ℝ) * (B ^ 2 / (1 - B) ^ 2) *
        (1 + S.s * B / (1 - B) ^ 2) ^ (Fintype.card D - 1) / c₀) * ‖x‖ ^ 2 := by
  obtain ⟨h, hmean, he⟩ := S.zeroSector_representation x x.property
  have hproject := S.centre_projection_bound h hmean hB hB1 hc hp hν hR
  have hnorm : ‖S.centreMeanHeatBath (x : meanZeroSpace S.jointLaw)‖ ^ 2 =
      expectReal S.jointLaw (fun σ => S.centreProjection (fun τ => h τ.1) σ ^ 2) := by
    change ‖S.centreHeatBath.operator (x.val : SupportedSpace S.jointLaw)‖ ^ 2 = _
    rw [← he, SupportedOperator.intertwine]
    exact supportedEmbed_norm_sq _ _
  have hxnorm : ‖x‖ ^ 2 = expectReal S.centreLaw (fun c => h c ^ 2) := by
    change ‖(x.val : SupportedSpace S.jointLaw)‖ ^ 2 = _
    rw [← he, supportedEmbed_norm_sq]
    exact S.jointLaw_centre_expectation (fun c => h c ^ 2)
  rw [S.starProjectionBlocks_T_energy]
  change ⟪(x : meanZeroSpace S.jointLaw), S.centreMeanHeatBath x⟫_ℝ ≤ _
  rw [S.centreMeanHeatBath_projection.inner_self, hnorm, hxnorm]
  exact hproject

/-- The palette and degree budgets supply the exact density constant in
r*, so the displayed bound is now attached to the actual operator. -/
theorem zeroBlock_bound {δ Δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hB1 : B < 1)
    (hd : (Fintype.card D : ℝ) ≤ Δ)
    (hA : S.s * ((Fintype.card D : ℝ) + δ * Δ) ≤ S.palette)
    (hp : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (hν : ∀ c, S.s * S.centreLaw.w c ≤ B) (x : S.zeroSector) :
    @energy S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.T x ≤ starProjectionBound δ B S.s (Fintype.card D) * ‖x‖ ^ 2 :=
  S.zeroBlock_energy_le hB hB1 (by positivity) hp hν
    (S.leafDensity_budget hδ hd hA) x

end
end ZeroFreeness.Appendix.Girth.ConditionalStar
