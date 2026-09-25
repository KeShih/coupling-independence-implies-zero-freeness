import ZeroFreeness.Coupling.Girth.Spectral.AdditiveSpace
import ZeroFreeness.Coupling.Girth.Spectral.AdditiveCompression
import ZeroFreeness.Coupling.Girth.Spectral.StarBlocks
import ZeroFreeness.Coupling.Girth.Spectral.CommutingSpaces

/-! The actual additive space inside the positive leaf sectors,
together with its root-plus decomposition fixed by the centre update. -/

namespace ZeroFreeness.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem additiveEmbedding_val (h : D → C → ℝ) :
    (S.additiveEmbedding h : SupportedSpace S.jointLaw) =
      supportedEmbed S.jointLaw (S.additiveResidualSum h) := by
  change ((∑ i, S.additiveLeafMap i (h i) : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw) = _
  rw [Submodule.coe_sum]
  change (∑ i, supportedEmbed S.jointLaw (fun σ => S.additiveResidual i (h i) σ.1 (σ.2 i))) = _
  rw [← map_sum]
  apply congrArg (supportedEmbed S.jointLaw)
  funext σ
  simp only [Finset.sum_apply, additiveResidualSum, singletonFunction]

theorem additiveLeafMap_mem_plus (i : D) (h : C → ℝ) : S.additiveLeafMap i h ∈ S.plusSector := by
  apply (S.zeroSector.mem_orthogonal' _).mpr
  intro z hz
  have hz0 : S.leafComplement i z = 0 := by
    rw [leafComplement, LinearMap.sub_apply, LinearMap.id_apply, (S.zeroSector_mem_iff z).mp hz i, sub_self]
  have he := (S.leafComplement_projection i).symmetric (S.additiveLeafMap i h) z
  rw [S.additiveLeafMap_complement, if_pos rfl, hz0, inner_zero_right] at he
  exact he

theorem additiveSpace_le_plus : S.additiveSpace ≤ S.plusSector := by
  rintro z ⟨h, rfl⟩
  change (∑ i, S.additiveLeafMap i (h i)) ∈ S.plusSector
  exact S.plusSector.sum_mem fun i _ => S.additiveLeafMap_mem_plus i (h i)

def additivePlusMap : (D → C → ℝ) →ₗ[ℝ] S.plusSector :=
  S.additiveEmbedding.codRestrict S.plusSector (fun h => S.additiveSpace_le_plus ⟨h, rfl⟩)

def additivePlusSpace : Submodule ℝ S.plusSector := S.additivePlusMap.range

theorem additivePlusMap_val (h : D → C → ℝ) :
    (S.additivePlusMap h : meanZeroSpace S.jointLaw) = S.additiveEmbedding h := rfl

theorem additivePlusMap_norm_sq (h : D → C → ℝ) :
    ‖S.additivePlusMap h‖ ^ 2 = expectReal S.jointLaw (fun σ => S.additiveResidualSum h σ ^ 2) := by
  change ‖(S.additiveEmbedding h : SupportedSpace S.jointLaw)‖ ^ 2 = _
  rw [S.additiveEmbedding_val, supportedEmbed_norm_sq]

theorem additiveLeafMap_mem_singletons (i : D) (h : C → ℝ) :
    S.additiveLeafMap i h ∈ S.leafSectors.degreeSpace {1} := by
  have hs := S.singletonEmbed_sector i (S.additiveResidual i h) (S.additiveResidual_mean i h)
  change S.additiveLeafMap i h ∈ S.leafSectors.sector (singleSignature i) at hs
  intro χ hχ
  rw [S.leafSectors.part_on_sector χ (singleSignature i) hs]
  apply if_neg
  intro he
  subst χ
  apply hχ
  change Schur.CommutingProjections.degree (Schur.CommutingProjections.singleSignature i) ∈ ({1} : Set ℕ)
  rw [Schur.CommutingProjections.degree_singleSignature]
  exact Set.mem_singleton 1

theorem additiveSpace_le_singletons : S.additiveSpace ≤ S.leafSectors.degreeSpace {1} := by
  rintro z ⟨h, rfl⟩
  change (∑ i, S.additiveLeafMap i (h i)) ∈ S.leafSectors.degreeSpace {1}
  exact (S.leafSectors.degreeSpace {1}).sum_mem fun i _ => S.additiveLeafMap_mem_singletons i (h i)

def leafAdditiveFunction (h : D → C → ℝ) (σ : C × (D → C)) : ℝ := ∑ i, h i (σ.2 i)

theorem additiveResidualSum_eq (h : D → C → ℝ) (σ : C × (D → C)) :
    S.additiveResidualSum h σ = leafAdditiveFunction h σ - S.additiveMean h σ.1 := by
  unfold additiveResidualSum singletonFunction additiveResidual leafAdditiveFunction additiveMean
  rw [Finset.sum_sub_distrib]

theorem leafAdditiveFunction_mean (h : D → C → ℝ) :
    expectReal S.jointLaw (leafAdditiveFunction h) = expectReal S.centreLaw (S.additiveMean h) := by
  rw [S.jointLaw_expectation]
  apply congrArg (expectReal S.centreLaw)
  funext c
  unfold leafAdditiveFunction additiveMean leafChannel
  rw [expectReal_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact productLaw_coordinate_expectation _ i (h i)

def additiveRoot (h : D → C → ℝ) : meanZeroSpace S.jointLaw :=
  centeredEmbed S.jointLaw (fun σ => S.additiveMean h σ.1)

theorem additiveRoot_mem_zero (h : D → C → ℝ) : S.additiveRoot h ∈ S.zeroSector := by
  apply (S.zeroSector_mem_iff _).mpr
  intro i
  apply Subtype.ext
  change (S.leafHeatBath i).operator (supportedEmbed S.jointLaw _) = _
  rw [SupportedOperator.intertwine]
  apply congrArg (supportedEmbed S.jointLaw)
  funext σ
  change expectReal (edgeChannel (S.cavity i) S.s S.s_le_one σ.1 (S.edge_positive i σ.1))
    (fun _ => S.additiveMean h σ.1 - expectReal S.jointLaw (fun τ => S.additiveMean h τ.1)) = _
  exact expectReal_const (edgeChannel (S.cavity i) S.s S.s_le_one σ.1
    (S.edge_positive i σ.1)) _

def additiveRootZero (h : D → C → ℝ) : S.zeroSector := ⟨S.additiveRoot h, S.additiveRoot_mem_zero h⟩

theorem additive_root_plus (h : D → C → ℝ) :
    S.additiveRoot h + S.additiveEmbedding h = centeredEmbed S.jointLaw (leafAdditiveFunction h) := by
  apply Subtype.ext
  change (supportedEmbed S.jointLaw _) + (S.additiveEmbedding h : SupportedSpace S.jointLaw) = _
  rw [S.additiveEmbedding_val, ← map_add]
  apply congrArg (supportedEmbed S.jointLaw)
  funext σ
  change (S.additiveMean h σ.1 - expectReal S.jointLaw (fun τ => S.additiveMean h τ.1)) +
    S.additiveResidualSum h σ = leafAdditiveFunction h σ - expectReal S.jointLaw (leafAdditiveFunction h)
  rw [S.additiveResidualSum_eq, S.leafAdditiveFunction_mean, S.jointLaw_centre_expectation]
  ring

theorem additive_centre_fixed (h : D → C → ℝ) :
    S.centreMeanHeatBath (S.additiveRoot h + S.additiveEmbedding h) =
      S.additiveRoot h + S.additiveEmbedding h := by
  rw [S.additive_root_plus]
  apply Subtype.ext
  change S.centreHeatBath.operator (supportedEmbed S.jointLaw _) = _
  rw [SupportedOperator.intertwine]
  apply congrArg (supportedEmbed S.jointLaw)
  exact S.centreProjection_leafFunction (fun σ =>
    (∑ i, h i (σ i)) - expectReal S.jointLaw (leafAdditiveFunction h))

end
end ZeroFreeness.Appendix.Girth.ConditionalStar
