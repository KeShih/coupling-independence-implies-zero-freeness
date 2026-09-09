import CI2ZF.Appendix.GirthStarBlocks

/-! The actual star Schur operators, constructed using only raw degree,
palette and scaled-atom budgets. No operator estimate is an input field. -/
namespace CI2ZF.Appendix.Girth.ConditionalStar
open scoped BigOperators InnerProductSpace
open PottsCI Finset Schur
noncomputable section
attribute [local instance] Classical.propDecidable
variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

/-- The raw local assumptions for a star in the fixed-girth regime. -/
structure SchurParameters where
  δ : ℝ
  Δ : ℕ
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  threshold : girthFiveThreshold δ ≤ Δ
  degree_le : Fintype.card D ≤ Δ
  palette_budget : S.s * ((Fintype.card D : ℝ) + δ * Δ) ≤ S.palette
  cavity_cap : ∀ i c, S.s * (S.cavity i).w c ≤ starCap δ Δ
  centre_cap : ∀ c, S.s * S.centreLaw.w c ≤ starCap δ Δ

namespace SchurParameters
variable {S} (p : S.SchurParameters)

def bound : ℝ := starProjectionBound p.δ (starCap p.δ p.Δ) S.s (Fintype.card D)

def singletonError : ℝ := starSingletonError p.δ (starCap p.δ p.Δ) S.s (Fintype.card D)

lemma bound_nonneg : 0 ≤ p.bound :=
  (girthFive_star_bounds p.delta_pos p.delta_le_one p.threshold S.s_nonneg S.s_le_one p.degree_le).1

lemma bound_le : p.bound ≤ p.δ / 2048 :=
  (girthFive_star_bounds p.delta_pos p.delta_le_one p.threshold S.s_nonneg S.s_le_one p.degree_le).2.1

lemma bound_lt_one : p.bound < 1 := by
  have hh := p.bound_le
  have hd := p.delta_le_one
  linarith

lemma singletonError_nonneg : 0 ≤ p.singletonError :=
  (girthFive_star_bounds p.delta_pos p.delta_le_one p.threshold S.s_nonneg S.s_le_one p.degree_le).2.2.1

lemma eta_le : p.bound + p.singletonError ≤ 5 / 2048 :=
  (girthFive_star_bounds p.delta_pos p.delta_le_one p.threshold S.s_nonneg S.s_le_one p.degree_le).2.2.2

lemma zero_bound (x : S.zeroSector) :
    @energy S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.T x ≤ p.bound * ‖x‖ ^ 2 := by
  obtain ⟨_, _, hB0, _, hB1, _⟩ := girthFiveThreshold_bounds p.delta_pos p.delta_le_one p.threshold
  exact S.zeroBlock_bound p.delta_pos hB0.le (by linarith) (by exact_mod_cast p.degree_le)
    p.palette_budget p.cavity_cap p.centre_cap x

/-- The inverse of the actual degree-zero block. -/
def resolvent : S.zeroSector →ₗ[ℝ] S.zeroSector :=
  S.starProjectionBlocks.R p.bound_lt_one p.zero_bound

/-- The literal actual C=P₊₀(I−P₀₀)⁻¹P₀₊. -/
def correction : S.plusSector →ₗ[ℝ] S.plusSector :=
  S.starProjectionBlocks.C p.bound_lt_one p.zero_bound

/-- The literal actual H=I−P₊₊−C. -/
def residualProjection : S.plusSector →ₗ[ℝ] S.plusSector :=
  S.starProjectionBlocks.H p.bound_lt_one p.zero_bound

lemma zeroBlock_symmetric : @Schur.Symmetric S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.A := S.starProjectionBlocks.A_symmetric

include p in
lemma zeroBlock_positive : @Schur.Positive S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.A :=
  S.starProjectionBlocks.A_positive p.bound_lt_one p.zero_bound

lemma resolvent_left (x : S.zeroSector) : S.starProjectionBlocks.A (p.resolvent x) = x :=
  S.starProjectionBlocks.A_R p.bound_lt_one p.zero_bound x

lemma resolvent_right (x : S.zeroSector) : p.resolvent (S.starProjectionBlocks.A x) = x :=
  S.starProjectionBlocks.R_A p.bound_lt_one p.zero_bound x

lemma correction_factor (a : S.plusSector) :
    @energy S.plusSector (inferInstance) (inferInstance) p.correction a =
      ⟪S.starProjectionBlocks.B a, p.resolvent (S.starProjectionBlocks.B a)⟫_ℝ :=
  S.starProjectionBlocks.C_factor p.bound_lt_one p.zero_bound a

lemma correction_symmetric : @Schur.Symmetric S.plusSector (inferInstance) (inferInstance) p.correction :=
  S.starProjectionBlocks.C_symmetric p.bound_lt_one p.zero_bound

lemma correction_positive : @Schur.Positive S.plusSector (inferInstance) (inferInstance) p.correction :=
  S.starProjectionBlocks.C_positive p.bound_lt_one p.zero_bound

lemma correction_le (a : S.plusSector) :
    @energy S.plusSector (inferInstance) (inferInstance) p.correction a ≤ p.bound * ‖a‖ ^ 2 :=
  S.starProjectionBlocks.C_le p.bound_nonneg p.bound_lt_one p.zero_bound a

lemma residual_projection : @Schur.Projection S.plusSector (inferInstance) (inferInstance) p.residualProjection :=
  S.starProjectionBlocks.H_projection p.bound_lt_one p.zero_bound

lemma residual_add_correction : p.residualProjection + p.correction = LinearMap.id - S.starProjectionBlocks.D :=
  S.starProjectionBlocks.H_add_C p.bound_lt_one p.zero_bound

lemma residual_lower (a : S.plusSector)
    (hD : @energy S.plusSector (inferInstance) (inferInstance) S.starProjectionBlocks.D a ≤
      p.singletonError * ‖a‖ ^ 2) :
    (1 - (p.bound + p.singletonError)) * ‖a‖ ^ 2 ≤
      @energy S.plusSector (inferInstance) (inferInstance) p.residualProjection a :=
  S.starProjectionBlocks.H_lower_of_D p.bound_nonneg p.bound_lt_one p.zero_bound a hD

end SchurParameters

lemma fixed_block_equations (x : S.zeroSector) (a : S.plusSector)
    (hfix : S.centreMeanHeatBath ((x : meanZeroSpace S.jointLaw) + a) =
      (x : meanZeroSpace S.jointLaw) + a) :
    S.starProjectionBlocks.T x + S.starProjectionBlocks.B a = x ∧
    S.starProjectionBlocks.Bt x + S.starProjectionBlocks.D a = a := by
  constructor
  · rw [S.starProjectionBlocks_T_apply, S.starProjectionBlocks_B_apply, ← map_add, ← map_add, hfix, map_add]
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      S.zeroSector.orthogonalProjectionOnto_apply_of_mem_orthogonal a.property, add_zero]
  · rw [S.starProjectionBlocks_Bt_apply, S.starProjectionBlocks_D_apply, ← map_add, ← map_add, hfix, map_add]
    have hx : S.plusSector.orthogonalProjectionOnto (x : meanZeroSpace S.jointLaw) = 0 :=
      S.zeroSector.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.property
    rw [hx, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, zero_add]

namespace SchurParameters
variable {S} (p : S.SchurParameters)

/-- Fixed vectors of the actual centre heat bath are killed by H in
their positive-sector coordinate. -/
theorem residual_eq_zero_of_fixed (x : S.zeroSector) (a : S.plusSector)
    (hfix : S.centreMeanHeatBath ((x : meanZeroSpace S.jointLaw) + a) =
      (x : meanZeroSpace S.jointLaw) + a) : p.residualProjection a = 0 := by
  obtain ⟨hx, ha⟩ := S.fixed_block_equations x a hfix
  exact S.starProjectionBlocks.H_eq_zero_of_fixed p.bound_lt_one p.zero_bound x a hx ha

/-- The exact additive-sector identity, derived from the actual fixed
vector and both actual projection blocks. -/
theorem correction_energy_of_fixed (x : S.zeroSector) (a : S.plusSector)
    (hfix : S.centreMeanHeatBath ((x : meanZeroSpace S.jointLaw) + a) =
      (x : meanZeroSpace S.jointLaw) + a) :
    @energy S.plusSector (inferInstance) (inferInstance) p.correction a =
      ‖(x : meanZeroSpace S.jointLaw) - S.centreMeanHeatBath x‖ ^ 2 := by
  obtain ⟨hx, _⟩ := S.fixed_block_equations x a hfix
  have hB : S.starProjectionBlocks.B a = S.starProjectionBlocks.A x := by
    rw [Schur.ProjectionBlocks.A_apply]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hx)
  calc
    _ = ⟪S.starProjectionBlocks.B a, p.resolvent (S.starProjectionBlocks.B a)⟫_ℝ := p.correction_factor a
    _ = ⟪S.starProjectionBlocks.A x, x⟫_ℝ := by rw [hB, p.resolvent_right]
    _ = @energy S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.A x := by
      exact real_inner_comm _ _
    _ = ‖x‖ ^ 2 - @energy S.zeroSector (inferInstance) (inferInstance) S.starProjectionBlocks.T x :=
      S.starProjectionBlocks.A_energy x
    _ = ‖x‖ ^ 2 - energy S.centreMeanHeatBath (x : meanZeroSpace S.jointLaw) := by
      rw [S.starProjectionBlocks_T_energy]
    _ = _ := (S.centreMeanHeatBath_projection.defect_energy x).symm

end SchurParameters
end
end CI2ZF.Appendix.Girth.ConditionalStar
