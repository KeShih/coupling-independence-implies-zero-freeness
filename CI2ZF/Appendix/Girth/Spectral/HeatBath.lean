import CI2ZF.Appendix.Girth.Spectral.StarL2
import CI2ZF.Appendix.Girth.Spectral.SupportedOperator

/-! Actual centre and leaf heat-bath projections on the supported
conditional-star space. Their projection and commutation properties
are derived from finite product disintegration. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D]

private def updateSwap (i : D) : ((D → C) × C) ≃ ((D → C) × C) :=
  { toFun := fun z => (Function.update z.1 i z.2, z.1 i)
    invFun := fun z => (Function.update z.1 i z.2, z.1 i)
    left_inv := by intro z; simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
    right_inv := by intro z; simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }

theorem productLaw_swap_weight (p : D → FinDist C) (i : D) (σ : D → C) (t : C) :
    (productLaw p).w (Function.update σ i t) * (p i).w (σ i) =
      (productLaw p).w σ * (p i).w t := by
  change (∏ j, (p j).w (Function.update σ i t j)) * _ = (∏ j, (p j).w (σ j)) * _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, (p j).w (Function.update σ i t j)) =
      ∏ j ∈ Finset.univ.erase i, (p j).w (σ j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  ring

def productProjection (p : D → FinDist C) (i : D) (f : (D → C) → ℝ) (σ : D → C) : ℝ :=
  expectReal (p i) (fun t => f (Function.update σ i t))

theorem productProjection_selfAdjoint (p : D → FinDist C) (i : D)
    (f g : (D → C) → ℝ) :
    expectReal (productLaw p) (fun σ => productProjection p i f σ * g σ) =
      expectReal (productLaw p) (fun σ => f σ * productProjection p i g σ) := by
  unfold expectReal productProjection
  simp only [expectReal, Finset.sum_mul, Finset.mul_sum]
  rw [← Fintype.sum_prod_type (f := fun z : (D → C) × C =>
    (productLaw p).w z.1 * ((p i).w z.2 * f (Function.update z.1 i z.2) * g z.1)),
    ← Fintype.sum_prod_type (f := fun z : (D → C) × C =>
    (productLaw p).w z.1 * (f z.1 * ((p i).w z.2 * g (Function.update z.1 i z.2))))]
  apply Fintype.sum_equiv (updateSwap i)
  intro z
  simp only [updateSwap, Equiv.coe_fn_mk]
  rw [Function.update_idem, Function.update_eq_self]
  have hw := productLaw_swap_weight p i z.1 z.2
  calc
    _ = ((productLaw p).w z.1 * (p i).w z.2) *
      (f (Function.update z.1 i z.2) * g z.1) := by ring
    _ = _ := by rw [← hw]; ring

omit [Fintype D] in
theorem productProjection_idempotent (p : D → FinDist C) (i : D)
    (f : (D → C) → ℝ) : productProjection p i (productProjection p i f) = productProjection p i f := by
  funext σ
  unfold productProjection
  simp only [Function.update_idem]
  exact expectReal_const (p i) _

omit [Fintype D] in
theorem productProjection_commute (p : D → FinDist C) (i j : D)
    (f : (D → C) → ℝ) :
    productProjection p i (productProjection p j f) = productProjection p j (productProjection p i f) := by
  by_cases hij : i = j
  · subst j; rfl
  funext σ
  unfold productProjection expectReal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  rw [Function.update_comm hij]
  ring

namespace ConditionalStar

variable [DecidableEq C] (S : ConditionalStar C D)

def centreRaw : (C × (D → C) → ℝ) →ₗ[ℝ] (C × (D → C) → ℝ) where
  toFun := S.centreProjection
  map_add' f g := by
    funext σ
    simp [centreProjection, centreAverage, centreNumerator, Pi.add_apply,
      mul_add, Finset.sum_add_distrib, add_div]
  map_smul' a f := by
    funext σ
    simp only [centreProjection, centreAverage, centreNumerator, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [← mul_div_assoc, Finset.mul_sum]
    apply congrArg (fun z : ℝ => z / S.leafDensity σ.2)
    apply Finset.sum_congr rfl
    intro c _
    ring

def leafProjection (i : D) (f : C × (D → C) → ℝ) (σ : C × (D → C)) : ℝ :=
  productProjection (fun j => edgeChannel (S.cavity j) S.s S.s_le_one σ.1
    (S.edge_positive j σ.1)) i (fun τ => f (σ.1, τ)) σ.2

def leafRaw (i : D) : (C × (D → C) → ℝ) →ₗ[ℝ] (C × (D → C) → ℝ) where
  toFun := S.leafProjection i
  map_add' f g := by
    funext σ
    simp only [leafProjection, productProjection, expectReal, Pi.add_apply,
      mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext σ
    simp only [leafProjection, productProjection, expectReal, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

theorem leafProjection_selfAdjoint (i : D) (f g : C × (D → C) → ℝ) :
    expectReal S.jointLaw (fun σ => S.leafProjection i f σ * g σ) =
      expectReal S.jointLaw (fun σ => f σ * S.leafProjection i g σ) := by
  rw [S.jointLaw_expectation, S.jointLaw_expectation]
  apply congrArg (expectReal S.centreLaw)
  funext c
  exact productProjection_selfAdjoint _ i (fun σ => f (c, σ)) (fun σ => g (c, σ))

theorem leafProjection_idempotent (i : D) (f : C × (D → C) → ℝ) :
    S.leafProjection i (S.leafProjection i f) = S.leafProjection i f := by
  funext σ
  exact congrFun (productProjection_idempotent _ i (fun τ => f (σ.1, τ))) σ.2

theorem leafProjection_commute (i j : D) (f : C × (D → C) → ℝ) :
    S.leafProjection i (S.leafProjection j f) = S.leafProjection j (S.leafProjection i f) := by
  funext σ
  exact congrFun (productProjection_commute _ i j (fun τ => f (σ.1, τ))) σ.2

def centreHeatBath : SupportedOperator S.jointLaw :=
  supportedOperatorOfSymmetric S.jointLaw S.centreRaw S.centreProjection_selfAdjoint

def leafHeatBath (i : D) : SupportedOperator S.jointLaw :=
  supportedOperatorOfSymmetric S.jointLaw (S.leafRaw i) (S.leafProjection_selfAdjoint i)

theorem centreHeatBath_symmetric (z w : SupportedSpace S.jointLaw) :
    ⟪S.centreHeatBath.operator z, w⟫_ℝ = ⟪z, S.centreHeatBath.operator w⟫_ℝ :=
  S.centreHeatBath.symmetric S.centreProjection_selfAdjoint z w

theorem centreHeatBath_idempotent (z : SupportedSpace S.jointLaw) :
    S.centreHeatBath.operator (S.centreHeatBath.operator z) = S.centreHeatBath.operator z :=
  S.centreHeatBath.idempotent S.centreProjection_idempotent z

theorem leafHeatBath_symmetric (i : D) (z w : SupportedSpace S.jointLaw) :
    ⟪(S.leafHeatBath i).operator z, w⟫_ℝ = ⟪z, (S.leafHeatBath i).operator w⟫_ℝ :=
  (S.leafHeatBath i).symmetric (S.leafProjection_selfAdjoint i) z w

theorem leafHeatBath_idempotent (i : D) (z : SupportedSpace S.jointLaw) :
    (S.leafHeatBath i).operator ((S.leafHeatBath i).operator z) = (S.leafHeatBath i).operator z :=
  (S.leafHeatBath i).idempotent (S.leafProjection_idempotent i) z

theorem leafHeatBath_commute (i j : D) (z : SupportedSpace S.jointLaw) :
    (S.leafHeatBath i).operator ((S.leafHeatBath j).operator z) =
      (S.leafHeatBath j).operator ((S.leafHeatBath i).operator z) := by
  change (S.leafHeatBath i).operator (supportedEmbed S.jointLaw _) =
    (S.leafHeatBath j).operator (supportedEmbed S.jointLaw _)
  rw [SupportedOperator.intertwine, SupportedOperator.intertwine]
  exact congrArg (supportedEmbed S.jointLaw) (S.leafProjection_commute i j _)

end ConditionalStar
end
end CI2ZF.Appendix.Girth
