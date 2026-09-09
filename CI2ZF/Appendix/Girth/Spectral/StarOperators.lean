import CI2ZF.Appendix.Girth.Spectral.MeanZero
import CI2ZF.Appendix.Girth.Spectral.SectorRepresentation
import CI2ZF.Appendix.Girth.Spectral.CommutingBounds

/-! The actual conditional-star heat baths on mean-zero supported L²,
instantiated as the complete family of commuting leaf projections. -/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem centreHeatBath_one : S.centreHeatBath.operator (supportedOne S.jointLaw) = supportedOne S.jointLaw := by
  change S.centreHeatBath.operator (supportedEmbed S.jointLaw (fun _ => 1)) = _
  rw [SupportedOperator.intertwine]
  exact congrArg (supportedEmbed S.jointLaw) (S.centreProjection_leafFunction (fun _ => 1))

theorem leafHeatBath_one (i : D) : (S.leafHeatBath i).operator (supportedOne S.jointLaw) = supportedOne S.jointLaw := by
  change (S.leafHeatBath i).operator (supportedEmbed S.jointLaw (fun _ => 1)) = _
  rw [SupportedOperator.intertwine]
  apply congrArg (supportedEmbed S.jointLaw)
  funext σ
  exact expectReal_const _ 1

def centreMeanHeatBath : meanZeroSpace S.jointLaw →ₗ[ℝ] meanZeroSpace S.jointLaw :=
  restrictMeanZero S.jointLaw S.centreHeatBath.operator S.centreHeatBath_symmetric S.centreHeatBath_one

def leafMeanHeatBath (i : D) : meanZeroSpace S.jointLaw →ₗ[ℝ] meanZeroSpace S.jointLaw :=
  restrictMeanZero S.jointLaw (S.leafHeatBath i).operator (S.leafHeatBath_symmetric i) (S.leafHeatBath_one i)

theorem centreMeanHeatBath_projection : Schur.Projection S.centreMeanHeatBath where
  symmetric := restrictMeanZero_symmetric S.jointLaw _ S.centreHeatBath_symmetric S.centreHeatBath_one
  idem := restrictMeanZero_idempotent S.jointLaw _ S.centreHeatBath_symmetric S.centreHeatBath_one
    S.centreHeatBath_idempotent

theorem leafMeanHeatBath_projection (i : D) : Schur.Projection (S.leafMeanHeatBath i) where
  symmetric := restrictMeanZero_symmetric S.jointLaw _ (S.leafHeatBath_symmetric i) (S.leafHeatBath_one i)
  idem := restrictMeanZero_idempotent S.jointLaw _ (S.leafHeatBath_symmetric i) (S.leafHeatBath_one i)
    (S.leafHeatBath_idempotent i)

theorem leafMeanHeatBath_commute (i j : D) (z : meanZeroSpace S.jointLaw) :
    S.leafMeanHeatBath i (S.leafMeanHeatBath j z) = S.leafMeanHeatBath j (S.leafMeanHeatBath i z) :=
  restrictMeanZero_commute S.jointLaw _ _ (S.leafHeatBath_symmetric i) (S.leafHeatBath_symmetric j)
    (S.leafHeatBath_one i) (S.leafHeatBath_one j) (S.leafHeatBath_commute i j) z

def leafComplement (i : D) : meanZeroSpace S.jointLaw →ₗ[ℝ] meanZeroSpace S.jointLaw :=
  LinearMap.id - S.leafMeanHeatBath i

theorem leafComplement_projection (i : D) : Schur.Projection (S.leafComplement i) where
  symmetric x y := by
    simp only [leafComplement, LinearMap.sub_apply, LinearMap.id_apply,
      inner_sub_left, inner_sub_right]
    exact congrArg (fun u : ℝ => ⟪x, y⟫_ℝ - u)
      ((S.leafMeanHeatBath_projection i).symmetric x y)
  idem x := by
    simp only [leafComplement, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, (S.leafMeanHeatBath_projection i).idem, sub_self, sub_zero]

theorem leafComplement_commute (i j : D) : Commute (S.leafComplement i) (S.leafComplement j) := by
  apply LinearMap.ext
  intro z
  change S.leafComplement i (S.leafComplement j z) = S.leafComplement j (S.leafComplement i z)
  simp only [leafComplement, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [S.leafMeanHeatBath_commute i j]
  abel

def leafSectors : Schur.CommutingProjections D (meanZeroSpace S.jointLaw) where
  Q := S.leafComplement
  projection := S.leafComplement_projection
  commute := S.leafComplement_commute

def zeroSector : Submodule ℝ (meanZeroSpace S.jointLaw) := S.leafSectors.sector (fun _ => false)

theorem zeroSector_mem_iff (z : meanZeroSpace S.jointLaw) :
    z ∈ S.zeroSector ↔ ∀ i, S.leafMeanHeatBath i z = z := by
  rw [zeroSector, S.leafSectors.mem_sector_iff]
  simp only [Bool.false_eq_true, ite_false, leafSectors, leafComplement,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact forall_congr' fun _ => eq_comm

theorem zeroSector_representation (z : meanZeroSpace S.jointLaw) (hz : z ∈ S.zeroSector) :
    ∃ h : C → ℝ, expectReal S.centreLaw h = 0 ∧
      supportedEmbed S.jointLaw (fun σ => h σ.1) = (z : SupportedSpace S.jointLaw) := by
  have hf := (S.zeroSector_mem_iff z).mp hz
  have he := S.supported_root_of_fixed (z : SupportedSpace S.jointLaw)
    (fun i => congrArg Subtype.val (hf i))
  refine ⟨S.rootAverage (supportedRepresent S.jointLaw z), ?_, he⟩
  have hm : expectReal S.jointLaw (fun σ =>
      S.rootAverage (supportedRepresent S.jointLaw z) σ.1) = 0 := by
    rw [← supportedMean_embed, he]
    exact z.property
  rwa [S.jointLaw_centre_expectation] at hm

end
end CI2ZF.Appendix.Girth.ConditionalStar
