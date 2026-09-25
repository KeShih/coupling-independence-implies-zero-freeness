import ZeroFreeness.Coupling.Girth.Spectral.Graph.StarModel

/-! The local conditional-star law is the actual Gibbs block conditional law. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace GraphStar
local instance (priority := 2000) graphStarLawLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _
variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
  (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (v : V)

def law (σ : V → C) : FinDist (Configuration I v) where
  w τ := (model I x hx hx1 hd hq v σ).jointLaw.w (τ none, fun u => τ (some u))
  nonneg τ := (model I x hx hx1 hd hq v σ).jointLaw.nonneg _
  sum_one := by
    calc
      _ = ∑ z, (model I x hx hx1 hd hq v σ).jointLaw.w z := by
        exact Fintype.sum_equiv Equiv.piOptionEquivProd _ _ (fun _ => rfl)
      _ = 1 := (model I x hx hx1 hd hq v σ).jointLaw.sum_one

theorem law_weight (σ : V → C) (τ : Configuration I v) :
    (law I x hx hx1 hd hq v σ).w τ = rawWeight I x v σ τ / normalizer I x hx hx1 hd hq v σ :=
  jointLaw_weight I x hx hx1 hd hq v σ τ

theorem law_expectation (σ : V → C) (f : Configuration I v → ℝ) :
    expectReal (law I x hx hx1 hd hq v σ) f =
      expectReal (model I x hx hx1 hd hq v σ).jointLaw
        (fun z => f (Equiv.piOptionEquivProd.symm z)) := by
  unfold expectReal
  apply Fintype.sum_equiv Equiv.piOptionEquivProd
  intro τ
  simp only [law, Equiv.symm_apply_apply]
  rfl

theorem law_extend (hg : 5 ≤ I.graph.egirth) (σ : V → C) (τ : Configuration I v) :
    law I x hx hx1 hd hq v (extend I v σ τ) = law I x hx hx1 hd hq v σ := by
  apply FinDist.ext
  funext ρ
  simp only [law, model_extend I hg]

theorem law_swap_weight (hg : 5 ≤ I.graph.egirth) (hx0 : 0 < x)
    (hZ : 0 < I.partition x) (σ : V → C) (τ : Configuration I v) :
    (I.gibbs x hx hZ).w (extend I v σ τ) *
        (law I x hx hx1 hd hq v (extend I v σ τ)).w (restrict I v σ) =
      (I.gibbs x hx hZ).w σ * (law I x hx hx1 hd hq v σ).w τ := by
  rw [law_extend I x hx hx1 hd hq v hg, law_weight, law_weight]
  change (_ / I.partition x) * (_ / normalizer I x hx hx1 hd hq v σ) =
    (_ / I.partition x) * (_ / normalizer I x hx hx1 hd hq v σ)
  rw [div_mul_div_comm, div_mul_div_comm]
  congr 1
  have hw := graph_weight_cross I hg hx0 v σ τ (restrict I v σ)
  simpa only [extend_restrict] using hw

private def blockSwap : ((V → C) × Configuration I v) ≃ ((V → C) × Configuration I v) :=
  { toFun := fun z => (extend I v z.1 z.2, restrict I v z.1)
    invFun := fun z => (extend I v z.1 z.2, restrict I v z.1)
    left_inv z := by simp only [extend_extend, extend_restrict, restrict_extend]
    right_inv z := by simp only [extend_extend, extend_restrict, restrict_extend] }

/-- Disintegrate any actual Gibbs expectation by resampling its star, with all
external graph factors retained. No independence of exterior spins is used. -/
theorem gibbs_expectation (hg : 5 ≤ I.graph.egirth) (hx0 : 0 < x)
    (hZ : 0 < I.partition x) (f : (V → C) → ℝ) :
    expectReal (I.gibbs x hx hZ) f =
      expectReal (I.gibbs x hx hZ) (fun σ => expectReal (law I x hx hx1 hd hq v σ)
        (fun τ => f (extend I v σ τ))) := by
  have he : expectReal (I.gibbs x hx hZ) (fun σ => expectReal (law I x hx hx1 hd hq v σ)
      (fun _ => f σ)) = expectReal (I.gibbs x hx hZ) f := by
    simp only [expectReal_const]
  rw [← he]
  unfold expectReal
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (f := fun z : (V → C) × Configuration I v =>
    (I.gibbs x hx hZ).w z.1 * ((law I x hx hx1 hd hq v z.1).w z.2 * f z.1)),
    ← Fintype.sum_prod_type (f := fun z : (V → C) × Configuration I v =>
    (I.gibbs x hx hZ).w z.1 * ((law I x hx hx1 hd hq v z.1).w z.2 * f (extend I v z.1 z.2)))]
  apply Fintype.sum_equiv (blockSwap I v)
  intro z
  simp only [blockSwap, Equiv.coe_fn_mk, extend_extend, extend_restrict]
  have hw := law_swap_weight I x hx hx1 hd hq v hg hx0 hZ z.1 z.2
  linear_combination -f z.1 * hw

end GraphStar
end
end ZeroFreeness.Appendix.Girth
