import ZeroFreeness.Coupling.Girth.Spectral.SingletonExpansion

/-! Actual conditional-star L² identities. The centre heat-bath map is
proved self-adjoint and idempotent by finite disintegration, including
all zero-probability configurations. -/

namespace ZeroFreeness.Appendix.Girth.ConditionalStar

open scoped BigOperators
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem jointLaw_expectation (f : C × (D → C) → ℝ) :
    expectReal S.jointLaw f = expectReal S.centreLaw (fun c => expectReal (S.leafChannel c) (fun σ => f (c, σ))) := by
  simp only [expectReal, jointLaw, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem singletonFunction_energy (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal
      (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) = 0) :
    expectReal S.jointLaw (fun σ => singletonFunction g σ ^ 2) = ∑ i, S.leafResidualEnergy g i := by
  rw [S.jointLaw_expectation]
  unfold singletonFunction leafChannel
  simp_rw [productLaw_centered_additive_energy _ _ (fun i => hmean i _)]
  exact expectReal_finset_sum _ _ _

def leafLaw : FinDist (D → C) := S.centreLaw.bind S.leafChannel

theorem leafLaw_weight (σ : D → C) : S.leafLaw.w σ = (productLaw S.cavity).w σ * S.leafDensity σ :=
  S.leaf_marginal_density σ

def centreConditionalLaw (σ : D → C) : FinDist C where
  w c := S.centreLaw.w c * (∏ i, edgeLikelihood S.s (S.cavity i) c (σ i)) / S.leafDensity σ
  nonneg c := div_nonneg (mul_nonneg (S.centreLaw.nonneg c)
    (Finset.prod_nonneg fun i _ => edgeLikelihood_nonneg (S.cavity i) S.s_le_one c (σ i) (S.edge_positive i c)))
    (S.leafDensity_pos σ).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (S.leafDensity_pos σ).ne'

theorem centreAverage_expectation (f : C × (D → C) → ℝ) (σ : D → C) :
    S.centreAverage f σ = expectReal (S.centreConditionalLaw σ) (fun c => f (c, σ)) := by
  unfold centreAverage centreNumerator expectReal centreConditionalLaw
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem jointLaw_disintegration_weight (c : C) (σ : D → C) :
    S.jointLaw.w (c, σ) = S.leafLaw.w σ * (S.centreConditionalLaw σ).w c := by
  rw [S.leafLaw_weight]
  change S.centreLaw.w c * (∏ i, (S.cavity i).w (σ i) * edgeLikelihood S.s (S.cavity i) c (σ i)) =
    ((∏ i, (S.cavity i).w (σ i)) * S.leafDensity σ) *
      (S.centreLaw.w c * (∏ i, edgeLikelihood S.s (S.cavity i) c (σ i)) / S.leafDensity σ)
  rw [Finset.prod_mul_distrib]
  field_simp [S.leafDensity_pos σ |>.ne']

theorem jointLaw_disintegration (f : C × (D → C) → ℝ) :
    expectReal S.jointLaw f = expectReal S.leafLaw (fun σ =>
      expectReal (S.centreConditionalLaw σ) (fun c => f (c, σ))) := by
  unfold expectReal
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [S.jointLaw_disintegration_weight]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem centreProjection_leafFunction (h : (D → C) → ℝ) :
    S.centreProjection (fun σ => h σ.2) = (fun σ => h σ.2) := by
  funext σ
  unfold centreProjection
  rw [S.centreAverage_expectation]
  exact expectReal_const (S.centreConditionalLaw σ.2) (h σ.2)

theorem centreProjection_idempotent (f : C × (D → C) → ℝ) :
    S.centreProjection (S.centreProjection f) = S.centreProjection f :=
  S.centreProjection_leafFunction (S.centreAverage f)

theorem centreProjection_selfAdjoint (f g : C × (D → C) → ℝ) :
    expectReal S.jointLaw (fun σ => S.centreProjection f σ * g σ) =
      expectReal S.jointLaw (fun σ => f σ * S.centreProjection g σ) := by
  rw [S.jointLaw_disintegration, S.jointLaw_disintegration]
  congr 1
  funext σ
  unfold centreProjection
  change expectReal (S.centreConditionalLaw σ) (fun c => S.centreAverage f σ * g (c, σ)) =
    expectReal (S.centreConditionalLaw σ) (fun c => f (c, σ) * S.centreAverage g σ)
  rw [expectReal_const_mul (S.centreConditionalLaw σ) (S.centreAverage f σ) (fun c => g (c, σ)),
    S.centreAverage_expectation f σ, S.centreAverage_expectation g σ]
  unfold expectReal
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem centreComplement_energy (f : C × (D → C) → ℝ) :
    expectReal S.jointLaw (fun σ => (f σ - S.centreProjection f σ) ^ 2) =
      expectReal S.jointLaw (fun σ => f σ ^ 2) -
        expectReal S.jointLaw (fun σ => S.centreProjection f σ ^ 2) := by
  have hcross := S.centreProjection_selfAdjoint f (S.centreProjection f)
  rw [S.centreProjection_idempotent] at hcross
  have he : expectReal S.jointLaw (fun σ => (f σ - S.centreProjection f σ) ^ 2) =
      expectReal S.jointLaw (fun σ => f σ ^ 2) -
        2 * expectReal S.jointLaw (fun σ => f σ * S.centreProjection f σ) +
        expectReal S.jointLaw (fun σ => S.centreProjection f σ ^ 2) := by
    unfold expectReal
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [he]
  simp only [← pow_two] at hcross
  linarith

theorem centreComplement_energy_le (f : C × (D → C) → ℝ) :
    expectReal S.jointLaw (fun σ => (f σ - S.centreProjection f σ) ^ 2) ≤
      expectReal S.jointLaw (fun σ => f σ ^ 2) := by
  rw [S.centreComplement_energy]
  have hn : 0 ≤ expectReal S.jointLaw (fun σ => S.centreProjection f σ ^ 2) :=
    Finset.sum_nonneg fun σ _ => mul_nonneg (S.jointLaw.nonneg σ) (sq_nonneg _)
  linarith

end

end ZeroFreeness.Appendix.Girth.ConditionalStar
