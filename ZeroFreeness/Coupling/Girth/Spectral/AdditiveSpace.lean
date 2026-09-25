import ZeroFreeness.Coupling.Girth.Spectral.Additive
import ZeroFreeness.Coupling.Girth.Spectral.StarOperators

/-! The actual leaf-additive subspace in supported mean-zero L².
Its generators are genuine residual functions; invariance under the
unequal-incidence operator follows from their exact joint eigenvalues. -/

namespace ZeroFreeness.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem singleton_mean_zero (i : D) (g : C → C → ℝ)
    (hg : ∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) = 0) :
    expectReal S.jointLaw (fun σ => g σ.1 (σ.2 i)) = 0 := by
  rw [S.jointLaw_expectation]
  have he (c : C) : expectReal (S.leafChannel c) (fun τ => g c (τ i)) = 0 := by
    unfold leafChannel
    rw [productLaw_coordinate_expectation]
    exact hg c
  simp only [he, expectReal_const]

theorem leafProjection_singleton (i j : D) (g : C → C → ℝ)
    (hg : ∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) = 0) :
    S.leafProjection j (fun σ => g σ.1 (σ.2 i)) =
      if j = i then (fun _ => 0) else (fun σ => g σ.1 (σ.2 i)) := by
  by_cases hji : j = i
  · subst j
    simp only [ite_true]
    funext σ
    unfold leafProjection productProjection
    simp only [Function.update_self]
    exact hg σ.1
  · rw [if_neg hji]
    funext σ
    unfold leafProjection productProjection
    simp only [Function.update_of_ne (Ne.symm hji)]
    exact expectReal_const _ _

def singletonEmbed (i : D) (g : C → C → ℝ)
    (hg : ∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) = 0) :
    meanZeroSpace S.jointLaw :=
  ⟨supportedEmbed S.jointLaw (fun σ => g σ.1 (σ.2 i)),
    (embed_mem_meanZeroSpace S.jointLaw _).mpr (S.singleton_mean_zero i g hg)⟩

theorem singletonEmbed_leaf (i j : D) (g : C → C → ℝ)
    (hg : ∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) = 0) :
    S.leafMeanHeatBath j (S.singletonEmbed i g hg) =
      if j = i then 0 else S.singletonEmbed i g hg := by
  apply Subtype.ext
  change (S.leafHeatBath j).operator (supportedEmbed S.jointLaw _) = _
  rw [SupportedOperator.intertwine]
  change supportedEmbed S.jointLaw (S.leafProjection j (fun σ => g σ.1 (σ.2 i))) = _
  rw [S.leafProjection_singleton i j g hg]
  by_cases hji : j = i
  · simp only [hji, ite_true]
    exact map_zero (supportedEmbed S.jointLaw)
  · simp only [hji, ite_false]
    rfl

theorem singletonEmbed_complement (i j : D) (g : C → C → ℝ)
    (hg : ∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) = 0) :
    S.leafComplement j (S.singletonEmbed i g hg) =
      if j = i then S.singletonEmbed i g hg else 0 := by
  simp only [leafComplement, LinearMap.sub_apply, LinearMap.id_apply, S.singletonEmbed_leaf]
  split_ifs <;> simp only [sub_self, sub_zero]

def singleSignature (i : D) : D → Bool := fun j => decide (j = i)

theorem singletonEmbed_sector (i : D) (g : C → C → ℝ)
    (hg : ∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) = 0) :
    S.singletonEmbed i g hg ∈ S.leafSectors.sector (singleSignature i) := by
  rw [S.leafSectors.mem_sector_iff]
  intro j
  simpa only [leafSectors, singleSignature, decide_eq_true_eq] using S.singletonEmbed_complement i j g hg

theorem additiveResidual_add (i : D) (h k : C → ℝ) (c t : C) :
    S.additiveResidual i (h + k) c t = S.additiveResidual i h c t + S.additiveResidual i k c t := by
  simp only [additiveResidual, expectReal, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem additiveResidual_smul (i : D) (a : ℝ) (h : C → ℝ) (c t : C) :
    S.additiveResidual i (a • h) c t = a * S.additiveResidual i h c t := by
  simp only [additiveResidual, Pi.smul_apply, smul_eq_mul]
  change a * h t - expectReal _ (fun u => a * h u) = _
  rw [expectReal_const_mul]
  ring

def additiveLeafMap (i : D) : (C → ℝ) →ₗ[ℝ] meanZeroSpace S.jointLaw where
  toFun h := S.singletonEmbed i (S.additiveResidual i h) (S.additiveResidual_mean i h)
  map_add' h k := by
    apply Subtype.ext
    change supportedEmbed S.jointLaw (fun σ => S.additiveResidual i (h + k) σ.1 (σ.2 i)) =
      supportedEmbed S.jointLaw _ + supportedEmbed S.jointLaw _
    rw [← map_add]
    apply congrArg (supportedEmbed S.jointLaw)
    funext σ
    exact S.additiveResidual_add i h k σ.1 (σ.2 i)
  map_smul' a h := by
    apply Subtype.ext
    change supportedEmbed S.jointLaw (fun σ => S.additiveResidual i (a • h) σ.1 (σ.2 i)) =
      a • supportedEmbed S.jointLaw _
    rw [← map_smul]
    apply congrArg (supportedEmbed S.jointLaw)
    funext σ
    exact S.additiveResidual_smul i a h σ.1 (σ.2 i)

def additiveEmbedding : (D → C → ℝ) →ₗ[ℝ] meanZeroSpace S.jointLaw where
  toFun h := ∑ i, S.additiveLeafMap i (h i)
  map_add' h k := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a h := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

def additiveSpace : Submodule ℝ (meanZeroSpace S.jointLaw) := S.additiveEmbedding.range

theorem additiveLeafMap_complement (i j : D) (h : C → ℝ) :
    S.leafComplement j (S.additiveLeafMap i h) = if j = i then S.additiveLeafMap i h else 0 :=
  S.singletonEmbed_complement i j (S.additiveResidual i h) (S.additiveResidual_mean i h)

theorem additiveLeafMap_weighted (β : D → ℝ) (i : D) (h : C → ℝ) :
    S.leafSectors.weighted β (S.additiveLeafMap i h) = β i • S.additiveLeafMap i h := by
  simp only [Schur.CommutingProjections.weighted, LinearMap.sum_apply, LinearMap.smul_apply, leafSectors]
  simp only [S.additiveLeafMap_complement, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem additiveEmbedding_weighted (β : D → ℝ) (h : D → C → ℝ) :
    S.leafSectors.weighted β (S.additiveEmbedding h) =
      S.additiveEmbedding (fun i => β i • h i) := by
  change S.leafSectors.weighted β (∑ i, S.additiveLeafMap i (h i)) =
    ∑ i, S.additiveLeafMap i (β i • h i)
  rw [map_sum]
  simp only [S.additiveLeafMap_weighted, map_smul]

theorem additiveSpace_weighted (β : D → ℝ) {z : meanZeroSpace S.jointLaw} (hz : z ∈ S.additiveSpace) :
    S.leafSectors.weighted β z ∈ S.additiveSpace := by
  obtain ⟨h, rfl⟩ := hz
  exact ⟨fun i => β i • h i, (S.additiveEmbedding_weighted β h).symm⟩

end
end ZeroFreeness.Appendix.Girth.ConditionalStar
