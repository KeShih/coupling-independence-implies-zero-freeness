import CI2ZF.Appendix.GirthStarIncidence
import CI2ZF.Appendix.GirthCenteredOperators

/-! The local unequal-incidence inequality for arbitrary actual star
observables, with all centering and supported-space identifications
proved explicitly. -/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

def centreDifference (f : C × (D → C) → ℝ) (σ : C × (D → C)) : ℝ := f σ - S.centreProjection f σ

def leafDifference (i : D) (f : C × (D → C) → ℝ) (σ : C × (D → C)) : ℝ := f σ - S.leafProjection i f σ

def weightedDifference (β : D → ℝ) (f : C × (D → C) → ℝ) (σ : C × (D → C)) : ℝ :=
  ∑ i, β i * S.leafDifference i f σ

theorem centre_complement_centered (f : C × (D → C) → ℝ) :
    ((centeredEmbed S.jointLaw f - S.centreMeanHeatBath (centeredEmbed S.jointLaw f) :
      meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw) =
      supportedEmbed S.jointLaw (S.centreDifference f) :=
  S.centreHeatBath.complement_centered S.centreHeatBath_one f

theorem leaf_complement_centered (i : D) (f : C × (D → C) → ℝ) :
    ((S.leafComplement i (centeredEmbed S.jointLaw f) : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw) =
      supportedEmbed S.jointLaw (S.leafDifference i f) :=
  (S.leafHeatBath i).complement_centered (S.leafHeatBath_one i) f

theorem weighted_centered_val (β : D → ℝ) (f : C × (D → C) → ℝ) :
    ((S.leafSectors.weighted β (centeredEmbed S.jointLaw f) : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw) =
      supportedEmbed S.jointLaw (S.weightedDifference β f) := by
  simp only [Schur.CommutingProjections.weighted, LinearMap.sum_apply, LinearMap.smul_apply, leafSectors]
  rw [Submodule.coe_sum]
  change (∑ i, β i • (((S.leafComplement i (centeredEmbed S.jointLaw f) : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw))) = _
  simp only [S.leaf_complement_centered]
  simp only [← map_smul]
  rw [← map_sum]
  apply congrArg (supportedEmbed S.jointLaw)
  funext σ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, weightedDifference]

theorem leaf_centered_norm_sq (i : D) (f : C × (D → C) → ℝ) :
    ‖S.leafComplement i (centeredEmbed S.jointLaw f)‖ ^ 2 =
      expectReal S.jointLaw (fun σ => S.leafDifference i f σ ^ 2) := by
  change ‖((S.leafComplement i (centeredEmbed S.jointLaw f) : meanZeroSpace S.jointLaw) :
    SupportedSpace S.jointLaw)‖ ^ 2 = _
  rw [S.leaf_complement_centered, supportedEmbed_norm_sq]

theorem weighted_energy_by_leaves (β : D → ℝ) (z : meanZeroSpace S.jointLaw) :
    Schur.energy (S.leafSectors.weighted β) z = ∑ i, β i * ‖S.leafComplement i z‖ ^ 2 := by
  simp only [Schur.energy, Schur.CommutingProjections.weighted, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, real_inner_smul_right, leafSectors]
  apply Finset.sum_congr rfl
  intro i _
  rw [(S.leafComplement_projection i).inner_self]

theorem higher_energy_by_number (z : meanZeroSpace S.jointLaw) :
    Schur.energy S.leafSectors.higher z = ‖S.leafSectors.number z‖ ^ 2 -
      ∑ i, ‖S.leafComplement i z‖ ^ 2 := by
  have hn : ⟪z, S.leafSectors.number (S.leafSectors.number z)⟫_ℝ = ‖S.leafSectors.number z‖ ^ 2 := by
    change ⟪z, S.leafSectors.weighted (fun _ => 1) (S.leafSectors.number z)⟫_ℝ = _
    rw [← S.weighted_symmetric (fun _ => 1)]
    change ⟪S.leafSectors.number z, S.leafSectors.number z⟫_ℝ = _
    exact real_inner_self_eq_norm_sq _
  change ⟪z, S.leafSectors.number (S.leafSectors.number z) - S.leafSectors.number z⟫_ℝ = _
  rw [inner_sub_right, hn]
  have he := S.weighted_energy_by_leaves (fun _ => 1) z
  simpa only [one_mul, Schur.energy, Schur.CommutingProjections.number] using congrArg (fun t => ‖S.leafSectors.number z‖ ^ 2 - t) he

def rawStarDefect (β : D → ℝ) (δ : ℝ) (f : C × (D → C) → ℝ) : ℝ :=
  expectReal S.jointLaw (fun σ => S.centreDifference f σ ^ 2) / 2 +
    expectReal S.jointLaw (fun σ => S.centreDifference f σ * S.weightedDifference β f σ) +
    expectReal S.jointLaw (fun σ => S.weightedDifference (fun _ => 1) f σ ^ 2) -
    (∑ i, expectReal S.jointLaw (fun σ => S.leafDifference i f σ ^ 2)) +
    Schur.StarData.theta δ / (2 * Fintype.card D) *
      ∑ i, β i ^ 2 * expectReal S.jointLaw (fun σ => S.leafDifference i f σ ^ 2)

theorem meanStarDefect_eq_raw (β : D → ℝ) (δ : ℝ) (f : C × (D → C) → ℝ) :
    S.meanStarDefect β δ (centeredEmbed S.jointLaw f) = S.rawStarDefect β δ f := by
  let z := centeredEmbed S.jointLaw f
  have hc : ⟪z, z - S.centreMeanHeatBath z⟫_ℝ =
      expectReal S.jointLaw (fun σ => S.centreDifference f σ ^ 2) := by
    calc
      _ = ‖z - S.centreMeanHeatBath z‖ ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq, S.centreMeanHeatBath_projection.defect_energy]
        rfl
      _ = _ := by
        change ‖((z - S.centreMeanHeatBath z : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw)‖ ^ 2 = _
        rw [S.centre_complement_centered, supportedEmbed_norm_sq]
  have hcross : ⟪z - S.centreMeanHeatBath z, S.leafSectors.weighted β z⟫_ℝ =
      expectReal S.jointLaw (fun σ => S.centreDifference f σ * S.weightedDifference β f σ) := by
    change ⟪((z - S.centreMeanHeatBath z : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw),
      ((S.leafSectors.weighted β z : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw)⟫_ℝ = _
    rw [S.centre_complement_centered, S.weighted_centered_val, supportedEmbed_inner]
  have hnum : ‖S.leafSectors.number z‖ ^ 2 =
      expectReal S.jointLaw (fun σ => S.weightedDifference (fun _ => 1) f σ ^ 2) := by
    change ‖((S.leafSectors.weighted (fun _ => 1) z : meanZeroSpace S.jointLaw) : SupportedSpace S.jointLaw)‖ ^ 2 = _
    rw [S.weighted_centered_val, supportedEmbed_norm_sq]
  unfold meanStarDefect rawStarDefect
  change ⟪z, z - S.centreMeanHeatBath z⟫_ℝ / 2 +
    ⟪z - S.centreMeanHeatBath z, S.leafSectors.weighted β z⟫_ℝ +
    Schur.energy S.leafSectors.higher z + _ = _
  rw [hc, hcross, S.higher_energy_by_number, hnum, S.weighted_energy_by_leaves]
  dsimp only [z]
  simp_rw [S.leaf_centered_norm_sq]
  ring

namespace SchurParameters
variable {S} (p : S.SchurParameters)

/-- The actual local star inequality, for every observable and every
supported conditional star, including activity zero and degree zero. -/
theorem raw_star_inequality (β : D → ℝ) (hβ : ∀ i, β i ∈ Set.Ioo (0 : ℝ) 2)
    (f : C × (D → C) → ℝ) : 0 ≤ S.rawStarDefect β p.δ f := by
  by_cases hd : 0 < Fintype.card D
  · rw [← S.meanStarDefect_eq_raw]
    exact p.meanStarDefect_nonneg β hβ hd (centeredEmbed S.jointLaw f)
  · have hz : Fintype.card D = 0 := by omega
    let : IsEmpty D := Fintype.card_eq_zero_iff.mp hz
    have hn : 0 ≤ expectReal S.jointLaw (fun σ => S.centreDifference f σ ^ 2) :=
      Finset.sum_nonneg fun σ _ => mul_nonneg (S.jointLaw.nonneg σ) (sq_nonneg _)
    simpa only [rawStarDefect, weightedDifference, Finset.univ_eq_empty, Finset.sum_empty,
      mul_zero, zero_pow (by norm_num : 2 ≠ 0), expectReal_const, add_zero, sub_zero] using
      div_nonneg hn (by norm_num : (0 : ℝ) ≤ 2)

end SchurParameters
end
end CI2ZF.Appendix.Girth.ConditionalStar
