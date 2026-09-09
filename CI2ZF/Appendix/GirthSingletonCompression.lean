import CI2ZF.Appendix.GirthAdditiveLift
import CI2ZF.Appendix.GirthSupportTrim
import CI2ZF.Appendix.GirthStarSchur

/-! The singleton-complement estimate on the actual supported Hilbert
subspace, obtained from its proved conditional-function representation
and orthogonality to the actual additive range. -/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem additiveLeafMap_mem_additive (i : D) (h : C → ℝ) : S.additiveLeafMap i h ∈ S.additiveSpace := by
  refine ⟨Function.update (fun _ : D => (0 : C → ℝ)) i h, ?_⟩
  change (∑ j, S.additiveLeafMap j (Function.update (fun _ : D => (0 : C → ℝ)) i h j)) = _
  rw [Finset.sum_eq_single i]
  · rw [Function.update_self]
  · intro j _ hji
    rw [Function.update_of_ne hji, map_zero]
  · exact fun hi => (hi (Finset.mem_univ i)).elim

theorem single_sector_supported_representation (i : D) (z : meanZeroSpace S.jointLaw)
    (hz : z ∈ S.leafSectors.sector (Schur.CommutingProjections.singleSignature i)) :
    ∃ g : C → C → ℝ,
      (∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) = 0) ∧
      (∀ c t, (S.cavity i).w t = 0 → g c t = 0) ∧
      supportedEmbed S.jointLaw (fun σ => g σ.1 (σ.2 i)) = (z : SupportedSpace S.jointLaw) := by
  have hQ := (S.leafSectors.mem_sector_iff _ z).mp hz
  have hzi : S.leafMeanHeatBath i z = 0 := by
    have hi := hQ i
    simp only [Schur.CommutingProjections.singleSignature, decide_true, ite_true,
      leafSectors, leafComplement, LinearMap.sub_apply, LinearMap.id_apply] at hi
    exact sub_eq_self.mp hi
  have hzj : ∀ j, j ≠ i → S.leafMeanHeatBath j z = z := by
    intro j hji
    have hj := hQ j
    simp only [Schur.CommutingProjections.singleSignature, hji, decide_false, Bool.false_eq_true,
      ite_false, leafSectors, leafComplement, LinearMap.sub_apply, LinearMap.id_apply] at hj
    exact (sub_eq_zero.mp hj).symm
  exact S.singleton_representation_supported z i
    (congrArg Subtype.val hzi) (fun j hj => congrArg Subtype.val (hzj j hj))

/-- The complete singleton space is represented by a sum of actual
conditionally centred one-leaf functions. -/
theorem singleton_family_representation (b : meanZeroSpace S.jointLaw)
    (hb : b ∈ S.leafSectors.degreeSpace {1}) :
    ∃ g : D → C → C → ℝ,
      (∀ i c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) = 0) ∧
      (∀ i c t, (S.cavity i).w t = 0 → g i c t = 0) ∧
      supportedEmbed S.jointLaw (singletonFunction g) = (b : SupportedSpace S.jointLaw) := by
  have hrep (i : D) := S.single_sector_supported_representation i
    (S.leafSectors.part (Schur.CommutingProjections.singleSignature i) b)
    (S.leafSectors.part_mem _ b)
  choose g hmean hzero he using hrep
  refine ⟨g, hmean, hzero, ?_⟩
  calc
    _ = ∑ i, supportedEmbed S.jointLaw (fun σ => g i σ.1 (σ.2 i)) := by
      rw [← map_sum]
      apply congrArg (supportedEmbed S.jointLaw)
      funext σ
      simp only [singletonFunction, Finset.sum_apply]
    _ = ∑ i, ((S.leafSectors.part (Schur.CommutingProjections.singleSignature i) b) : SupportedSpace S.jointLaw) := by
      exact Finset.sum_congr rfl (fun i _ => he i)
    _ = ((∑ i, S.leafSectors.part (Schur.CommutingProjections.singleSignature i) b : meanZeroSpace S.jointLaw) :
        SupportedSpace S.jointLaw) := (Submodule.coe_sum _ _ _).symm
    _ = (b : SupportedSpace S.jointLaw) := congrArg Subtype.val (S.leafSectors.sum_singleSignature_eq_self hb)

theorem singleton_complement_projection_bound {B c₀ : ℝ}
    (hB : 0 ≤ B) (hB1 : B < 1) (hc : 0 < c₀)
    (hp : ∀ i c, S.s * (S.cavity i).w c ≤ B) (hν : ∀ c, S.s * S.centreLaw.w c ≤ B)
    (hR : ∀ σ, c₀ ≤ S.leafDensity σ)
    (b : meanZeroSpace S.jointLaw) (hb : b ∈ S.leafSectors.degreeSpace {1})
    (horth : b ∈ S.additiveSpaceᗮ) :
    ‖S.centreMeanHeatBath b‖ ^ 2 ≤
      (2 * ((Fintype.card D - 1 : ℕ) : ℝ) * (B ^ 2 / (1 - B) ^ 2) *
        (1 + S.s * B / (1 - B) ^ 2) ^ (Fintype.card D - 2) / (c₀ * (1 - B))) * ‖b‖ ^ 2 := by
  obtain ⟨g, hmean, hzero, he⟩ := S.singleton_family_representation b hb
  have hcancel : ∀ i t, (∑ c, S.centreLaw.w c * g i c t * edgeLikelihood S.s (S.cavity i) c t) = 0 := by
    apply S.singleton_cancellation_of_orthogonal g hmean hzero
    intro i h
    rw [← supportedEmbed_inner, he]
    change ⟪b, S.additiveLeafMap i h⟫_ℝ = 0
    exact (S.additiveSpace.mem_orthogonal' b).mp horth _ (S.additiveLeafMap_mem_additive i h)
  have hn : ‖S.centreMeanHeatBath b‖ ^ 2 =
      expectReal S.jointLaw (fun σ => S.centreProjection (singletonFunction g) σ ^ 2) := by
    change ‖S.centreHeatBath.operator (b : SupportedSpace S.jointLaw)‖ ^ 2 = _
    rw [← he, SupportedOperator.intertwine]
    exact supportedEmbed_norm_sq _ _
  have hbn : ‖b‖ ^ 2 = ∑ i, S.leafResidualEnergy g i := by
    change ‖(b : SupportedSpace S.jointLaw)‖ ^ 2 = _
    rw [← he, supportedEmbed_norm_sq, S.singletonFunction_energy g hmean]
  rw [hn, hbn]
  exact S.singleton_projection_bound g hmean hcancel hB hB1 hc hp hν hR

namespace SchurParameters

variable {S} (p : S.SchurParameters)

/-- The actual singleton-complement compression of P₊₊. -/
theorem singleton_block_bound (b : S.plusSector)
    (hb : (b : meanZeroSpace S.jointLaw) ∈ S.leafSectors.degreeSpace {1})
    (horth : (b : meanZeroSpace S.jointLaw) ∈ S.additiveSpaceᗮ) :
    @Schur.energy S.plusSector (inferInstance) (inferInstance) S.starProjectionBlocks.D b ≤
      p.singletonError * ‖b‖ ^ 2 := by
  obtain ⟨_, _, hB0, _, hB1, _⟩ := girthFiveThreshold_bounds p.delta_pos p.delta_le_one p.threshold
  have hδ := p.delta_pos
  have hp := S.singleton_complement_projection_bound hB0.le (by linarith) (by positivity : 0 < p.δ / (1 + p.δ))
    p.cavity_cap p.centre_cap (S.leafDensity_budget p.delta_pos (by exact_mod_cast p.degree_le) p.palette_budget)
    b hb horth
  rw [S.starProjectionBlocks_D_energy]
  change ⟪(b : meanZeroSpace S.jointLaw), S.centreMeanHeatBath b⟫_ℝ ≤ _
  rw [S.centreMeanHeatBath_projection.inner_self]
  change ‖S.centreMeanHeatBath (b : meanZeroSpace S.jointLaw)‖ ^ 2 ≤ _
  have he : p.singletonError =
      (2 * ((Fintype.card D - 1 : ℕ) : ℝ) * (starCap p.δ p.Δ ^ 2 / (1 - starCap p.δ p.Δ) ^ 2) *
        (1 + S.s * starCap p.δ p.Δ / (1 - starCap p.δ p.Δ) ^ 2) ^ (Fintype.card D - 2) /
        ((p.δ / (1 + p.δ)) * (1 - starCap p.δ p.Δ))) := by
    unfold singletonError starSingletonError starKappa starOmega starDensityConstant
    split_ifs with hd
    · rfl
    · have hz : Fintype.card D - 1 = 0 := by omega
      simp only [hz, Nat.cast_zero, mul_zero, zero_mul, zero_div]
  rw [he]
  exact hp

theorem singleton_residual_lower (b : S.plusSector)
    (hb : (b : meanZeroSpace S.jointLaw) ∈ S.leafSectors.degreeSpace {1})
    (horth : (b : meanZeroSpace S.jointLaw) ∈ S.additiveSpaceᗮ) :
    (1 - (p.bound + p.singletonError)) * ‖b‖ ^ 2 ≤
      @Schur.energy S.plusSector (inferInstance) (inferInstance) p.residualProjection b :=
  p.residual_lower b (p.singleton_block_bound b hb horth)

end SchurParameters
end
end CI2ZF.Appendix.Girth.ConditionalStar
