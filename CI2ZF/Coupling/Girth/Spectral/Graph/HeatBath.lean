import CI2ZF.Coupling.Girth.Spectral.Graph.HeatBathWeights

/-! Actual one-site conditional expectations for the pinned graph Gibbs law. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators InnerProductSpace
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
  (hlocal : ∀ σ v, 0 < sitePartition I x σ v)

/-- The normalized colour law is constructed from the actual incident constraints. -/
def siteLaw (σ : V → C) (v : V) : FinDist C where
  w c := siteWeight I x σ v c / sitePartition I x σ v
  nonneg c := div_nonneg (pow_nonneg hx _) (hlocal σ v).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (hlocal σ v).ne'

theorem siteLaw_update_of_not_adj (σ : V → C) (v u : V)
    (hu : ¬ I.graph.Adj v u) (a : C) :
    siteLaw I x hx hlocal (Function.update σ u a) v = siteLaw I x hx hlocal σ v := by
  apply FinDist.ext
  funext c
  simp only [siteLaw, sitePartition, siteWeight_update_of_not_adj I x σ v u hu]

private def updateSwap (v : V) : ((V → C) × C) ≃ ((V → C) × C) :=
  { toFun := fun z => (Function.update z.1 v z.2, z.1 v)
    invFun := fun z => (Function.update z.1 v z.2, z.1 v)
    left_inv := by intro z; simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
    right_inv := by intro z; simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }

theorem gibbs_swap_weight (hZ : 0 < I.partition x) (σ : V → C) (v : V) (c : C) :
    (I.gibbs x hx hZ).w (Function.update σ v c) *
        (siteLaw I x hx hlocal (Function.update σ v c) v).w (σ v) =
      (I.gibbs x hx hZ).w σ * (siteLaw I x hx hlocal σ v).w c := by
  rw [siteLaw_update_of_not_adj I x hx hlocal σ v v I.graph.irrefl]
  change (_ / I.partition x) * (_ / sitePartition I x σ v) =
    (_ / I.partition x) * (_ / sitePartition I x σ v)
  rw [div_mul_div_comm, div_mul_div_comm, weight_swap]

def projection (v : V) (f : (V → C) → ℝ) (σ : V → C) : ℝ :=
  expectReal (siteLaw I x hx hlocal σ v) (fun c => f (Function.update σ v c))

theorem projection_selfAdjoint (hZ : 0 < I.partition x) (v : V)
    (f g : (V → C) → ℝ) :
    expectReal (I.gibbs x hx hZ) (fun σ => projection I x hx hlocal v f σ * g σ) =
      expectReal (I.gibbs x hx hZ) (fun σ => f σ * projection I x hx hlocal v g σ) := by
  unfold expectReal projection
  simp only [expectReal, Finset.sum_mul, Finset.mul_sum]
  rw [← Fintype.sum_prod_type (f := fun z : (V → C) × C =>
    (I.gibbs x hx hZ).w z.1 *
      ((siteLaw I x hx hlocal z.1 v).w z.2 * f (Function.update z.1 v z.2) * g z.1)),
    ← Fintype.sum_prod_type (f := fun z : (V → C) × C =>
    (I.gibbs x hx hZ).w z.1 *
      (f z.1 * ((siteLaw I x hx hlocal z.1 v).w z.2 * g (Function.update z.1 v z.2))))]
  apply Fintype.sum_equiv (updateSwap v)
  intro z
  simp only [updateSwap, Equiv.coe_fn_mk]
  rw [Function.update_idem, Function.update_eq_self]
  have hw := gibbs_swap_weight I x hx hlocal hZ z.1 v z.2
  calc
    _ = ((I.gibbs x hx hZ).w z.1 * (siteLaw I x hx hlocal z.1 v).w z.2) *
      (f (Function.update z.1 v z.2) * g z.1) := by ring
    _ = _ := by rw [← hw]; ring

theorem projection_idempotent (v : V) (f : (V → C) → ℝ) :
    projection I x hx hlocal v (projection I x hx hlocal v f) =
      projection I x hx hlocal v f := by
  funext σ
  unfold projection
  simp only [Function.update_idem,
    siteLaw_update_of_not_adj I x hx hlocal σ v v I.graph.irrefl]
  exact expectReal_const _ _

theorem projection_commute (v u : V) (hu : ¬ I.graph.Adj v u) (f : (V → C) → ℝ) :
    projection I x hx hlocal v (projection I x hx hlocal u f) =
      projection I x hx hlocal u (projection I x hx hlocal v f) := by
  by_cases hvu : v = u
  · subst u; rfl
  funext σ
  have huv : ¬ I.graph.Adj u v := fun h => hu h.symm
  unfold projection
  simp only [siteLaw_update_of_not_adj I x hx hlocal σ u v huv,
    siteLaw_update_of_not_adj I x hx hlocal σ v u hu, expectReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [Function.update_comm hvu]
  ring

theorem projection_const (v : V) (a : ℝ) :
    projection I x hx hlocal v (fun _ => a) = fun _ => a := by
  funext σ
  exact expectReal_const _ _

def raw (v : V) : ((V → C) → ℝ) →ₗ[ℝ] ((V → C) → ℝ) where
  toFun := projection I x hx hlocal v
  map_add' f g := by
    funext σ
    simp only [projection, expectReal, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext σ
    simp only [projection, expectReal, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring

def heatBath (hZ : 0 < I.partition x) (v : V) : SupportedOperator (I.gibbs x hx hZ) :=
  supportedOperatorOfSymmetric (I.gibbs x hx hZ) (raw I x hx hlocal v)
    (projection_selfAdjoint I x hx hlocal hZ v)

theorem heatBath_symmetric (hZ : 0 < I.partition x) (v : V)
    (z w : SupportedSpace (I.gibbs x hx hZ)) :
    ⟪(heatBath I x hx hlocal hZ v).operator z, w⟫_ℝ =
      ⟪z, (heatBath I x hx hlocal hZ v).operator w⟫_ℝ :=
  (heatBath I x hx hlocal hZ v).symmetric (projection_selfAdjoint I x hx hlocal hZ v) z w

theorem heatBath_idempotent (hZ : 0 < I.partition x) (v : V)
    (z : SupportedSpace (I.gibbs x hx hZ)) :
    (heatBath I x hx hlocal hZ v).operator ((heatBath I x hx hlocal hZ v).operator z) =
      (heatBath I x hx hlocal hZ v).operator z :=
  (heatBath I x hx hlocal hZ v).idempotent (projection_idempotent I x hx hlocal v) z

theorem heatBath_commute (hZ : 0 < I.partition x) (v u : V) (hu : ¬ I.graph.Adj v u)
    (z : SupportedSpace (I.gibbs x hx hZ)) :
    (heatBath I x hx hlocal hZ v).operator ((heatBath I x hx hlocal hZ u).operator z) =
      (heatBath I x hx hlocal hZ u).operator ((heatBath I x hx hlocal hZ v).operator z) := by
  change (heatBath I x hx hlocal hZ v).operator (supportedEmbed _ _) =
    (heatBath I x hx hlocal hZ u).operator (supportedEmbed _ _)
  rw [SupportedOperator.intertwine, SupportedOperator.intertwine]
  exact congrArg (supportedEmbed _) (projection_commute I x hx hlocal v u hu _)

end GraphHeatBath
end
end CI2ZF.Appendix.Girth
