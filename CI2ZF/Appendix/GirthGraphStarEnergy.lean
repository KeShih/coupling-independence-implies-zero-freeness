import CI2ZF.Appendix.GirthGraphStarLocal
import CI2ZF.Appendix.GirthGraphStarBounds
import CI2ZF.ActivationAverage

/-! Convert the actual graph's supported operator energy into finite star residuals. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators InnerProductSpace
open PottsCI Finset Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

private theorem linearMap_ite_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Prop) [Decidable p] (T U : E →ₗ[ℝ] E) (z : E) :
    (if p then T else U) z = if p then T z else U z := by
  split_ifs <;> rfl

private theorem sum_quotient_product {A : Type*} [Fintype A] (a b : A → ℝ) (d : ℝ) :
    (∑ i, a i / d * b i) = (∑ i, a i * b i) / d := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
  (hlocal : ∀ σ v, 0 < sitePartition I x σ v) (hZ : 0 < I.partition x)

def residual (v : V) (f : (V → C) → ℝ) (σ : V → C) : ℝ :=
  f σ - projection I x hx hlocal v f σ

theorem complement_embed (v : V) (f : (V → C) → ℝ) :
    complement I x hx hlocal hZ v (supportedEmbed (I.gibbs x hx hZ) f) =
      supportedEmbed (I.gibbs x hx hZ) (residual I x hx hlocal v f) := by
  change supportedEmbed _ f - (heatBath I x hx hlocal hZ v).operator (supportedEmbed _ f) = _
  rw [SupportedOperator.intertwine, ← map_sub]
  rfl

theorem complement_energy (v : V) (f : (V → C) → ℝ) :
    energy ((system I x hx hlocal hZ).Q v) (supportedEmbed (I.gibbs x hx hZ) f) =
      expectReal (I.gibbs x hx hZ) (fun σ => residual I x hx hlocal v f σ ^ 2) := by
  rw [energy, (system I x hx hlocal hZ).projection v |>.inner_self]
  change ‖complement I x hx hlocal hZ v (supportedEmbed _ f)‖ ^ 2 = _
  rw [complement_embed, supportedEmbed_norm_sq]

end GraphHeatBath

namespace GraphStar
local instance (priority := 2000) graphStarEnergyLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _

variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
  (hlocal : ∀ σ v, 0 < GraphHeatBath.sitePartition I x σ v) (hZ : 0 < I.partition x) (v : V)

theorem sum_leaf {E : Type*} [AddCommMonoid E] (f : V → E) :
    (∑ u, if I.graph.Adj v u then f u else 0) = ∑ u : Leaf I v, f u.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (p := fun u : V => I.graph.Adj v u)
    (F := inferInstanceAs (Fintype (Leaf I v))) _
    (fun _ => by simp) f

def beta (u : Leaf I v) : ℝ := incidenceWeight (I.graph.degree v) (I.graph.degree u.val)

theorem beta_pos (u : Leaf I v) : 0 < beta I v u := by
  apply incidenceWeight_pos
  · exact_mod_cast degree_pos_of_adj I.graph u.property
  · exact_mod_cast degree_pos_of_adj I.graph u.property.symm

theorem beta_lt_two (u : Leaf I v) : beta I v u < 2 := by
  apply incidenceWeight_lt_two
  · exact_mod_cast degree_pos_of_adj I.graph u.property
  · exact_mod_cast degree_pos_of_adj I.graph u.property.symm

def neighbourResidual (f : (V → C) → ℝ) (σ : V → C) : ℝ :=
  ∑ u : Leaf I v, GraphHeatBath.residual I x hx hlocal u.val f σ

def incidenceResidual (f : (V → C) → ℝ) (σ : V → C) : ℝ :=
  ∑ u : Leaf I v, beta I v u * GraphHeatBath.residual I x hx hlocal u.val f σ

theorem neighbourSum_embed (f : (V → C) → ℝ) :
    (GraphHeatBath.system I x hx hlocal hZ).neighbourSum v (supportedEmbed (I.gibbs x hx hZ) f) =
      supportedEmbed (I.gibbs x hx hZ) (neighbourResidual I x hx hlocal v f) := by
  simp only [GraphProjections.neighbourSum, LinearMap.sum_apply, linearMap_ite_apply, LinearMap.zero_apply]
  rw [sum_leaf]
  change (∑ u : Leaf I v, GraphHeatBath.complement I x hx hlocal hZ u.val (supportedEmbed _ f)) = _
  simp only [GraphHeatBath.complement_embed]
  rw [← map_sum]
  congr 1
  funext σ
  simp only [neighbourResidual, Finset.sum_apply]

theorem incidenceSum_embed (f : (V → C) → ℝ) :
    (GraphHeatBath.system I x hx hlocal hZ).incidenceSum v (supportedEmbed (I.gibbs x hx hZ) f) =
      supportedEmbed (I.gibbs x hx hZ) (incidenceResidual I x hx hlocal v f) := by
  simp only [GraphProjections.incidenceSum, LinearMap.sum_apply, linearMap_ite_apply, LinearMap.zero_apply,
    LinearMap.smul_apply]
  rw [sum_leaf]
  change (∑ u : Leaf I v, beta I v u •
    GraphHeatBath.complement I x hx hlocal hZ u.val (supportedEmbed _ f)) = _
  simp only [GraphHeatBath.complement_embed, ← map_smul]
  rw [← map_sum]
  congr 1
  funext σ
  simp only [incidenceResidual, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem neighbourSum_energy (f : (V → C) → ℝ) :
    energy ((GraphHeatBath.system I x hx hlocal hZ).neighbourSum v) (supportedEmbed (I.gibbs x hx hZ) f) =
      ∑ u : Leaf I v, expectReal (I.gibbs x hx hZ)
        (fun σ => GraphHeatBath.residual I x hx hlocal u.val f σ ^ 2) := by
  simp only [energy, GraphProjections.neighbourSum, LinearMap.sum_apply, inner_sum]
  have hh (u : V) :
      ⟪supportedEmbed (I.gibbs x hx hZ) f,
        (if I.graph.Adj v u then (GraphHeatBath.system I x hx hlocal hZ).Q u else 0)
          (supportedEmbed (I.gibbs x hx hZ) f)⟫_ℝ =
      if I.graph.Adj v u then expectReal (I.gibbs x hx hZ)
        (fun σ => GraphHeatBath.residual I x hx hlocal u f σ ^ 2) else 0 := by
    split_ifs
    · exact GraphHeatBath.complement_energy I x hx hlocal hZ u f
    · simp
  simp_rw [hh]
  exact sum_leaf I v _

theorem starOperator_energy (f : (V → C) → ℝ) :
    energy ((GraphHeatBath.system I x hx hlocal hZ).starOperator v) (supportedEmbed (I.gibbs x hx hZ) f) =
      expectReal (I.gibbs x hx hZ) (fun σ => GraphHeatBath.residual I x hx hlocal v f σ ^ 2) +
      expectReal (I.gibbs x hx hZ) (fun σ => GraphHeatBath.residual I x hx hlocal v f σ * incidenceResidual I x hx hlocal v f σ) +
      expectReal (I.gibbs x hx hZ) (fun σ => neighbourResidual I x hx hlocal v f σ ^ 2) -
      ∑ u : Leaf I v, expectReal (I.gibbs x hx hZ) (fun σ => GraphHeatBath.residual I x hx hlocal u.val f σ ^ 2) := by
  rw [GraphProjections.starOperator_energy, GraphHeatBath.complement_energy,
    neighbourSum_embed, incidenceSum_embed, neighbourSum_energy]
  change _ + ⟪GraphHeatBath.complement I x hx hlocal hZ v (supportedEmbed _ f), _⟫_ℝ + _ - _ = _
  rw [GraphHeatBath.complement_embed, supportedEmbed_inner, supportedEmbed_norm_sq]

theorem correction_energy (f : (V → C) → ℝ) :
    (GraphHeatBath.system I x hx hlocal hZ).correction v (supportedEmbed (I.gibbs x hx hZ) f) =
      ∑ u : Leaf I v, beta I v u ^ 2 / (I.graph.degree v : ℝ) *
        expectReal (I.gibbs x hx hZ) (fun σ => GraphHeatBath.residual I x hx hlocal u.val f σ ^ 2) := by
  simp only [GraphProjections.correction, GraphHeatBath.complement_energy]
  exact sum_leaf I v _

/-- The raw integrand of T_v - Q_v/2 plus the directed incidence correction. -/
def integrand (θ : ℝ) (f : (V → C) → ℝ) (σ : V → C) : ℝ :=
  GraphHeatBath.residual I x hx hlocal v f σ ^ 2 / 2 +
    GraphHeatBath.residual I x hx hlocal v f σ * incidenceResidual I x hx hlocal v f σ +
    neighbourResidual I x hx hlocal v f σ ^ 2 -
    (∑ u : Leaf I v, GraphHeatBath.residual I x hx hlocal u.val f σ ^ 2) +
    θ / (2 * (Fintype.card (Leaf I v) : ℝ)) *
      ∑ u : Leaf I v, beta I v u ^ 2 * GraphHeatBath.residual I x hx hlocal u.val f σ ^ 2

theorem integrand_expectation (θ : ℝ) (f : (V → C) → ℝ) :
    expectReal (I.gibbs x hx hZ) (integrand I x hx hlocal v θ f) =
      energy ((GraphHeatBath.system I x hx hlocal hZ).starOperator v) (supportedEmbed (I.gibbs x hx hZ) f) -
      energy ((GraphHeatBath.system I x hx hlocal hZ).Q v) (supportedEmbed (I.gibbs x hx hZ) f) / 2 +
      θ / 2 * (GraphHeatBath.system I x hx hlocal hZ).correction v (supportedEmbed (I.gibbs x hx hZ) f) := by
  rw [starOperator_energy, GraphHeatBath.complement_energy, correction_energy]
  unfold integrand
  simp only [expectReal_add, expectReal_sub, expectReal_const_mul, expectReal_finset_sum]
  have hd : Fintype.card (Leaf I v) = I.graph.degree v := I.graph.card_neighborSet_eq_degree v
  rw [hd]
  have he : expectReal (I.gibbs x hx hZ)
      (fun σ => GraphHeatBath.residual I x hx hlocal v f σ ^ 2 / 2) =
      expectReal (I.gibbs x hx hZ) (fun σ => GraphHeatBath.residual I x hx hlocal v f σ ^ 2) / 2 := by
    simp only [expectReal, mul_div_assoc, Finset.sum_div]
  rw [he]
  rw [sum_quotient_product]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end GraphStar
end
end CI2ZF.Appendix.Girth
