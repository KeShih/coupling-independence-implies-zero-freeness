import CI2ZF.Appendix.Girth.Spectral.Graph.StarEnergy

/-! Integrating the proved local-star form yields the actual graph operator inequality. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace ConditionalStar
variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

def localForm (S : ConditionalStar C D) (β : D → ℝ) (θ : ℝ)
    (f : C × (D → C) → ℝ) (z : C × (D → C)) : ℝ :=
  (f z - S.centreProjection f z) ^ 2 / 2 +
    (f z - S.centreProjection f z) * (∑ i, β i * (f z - S.leafProjection i f z)) +
    (∑ i, (f z - S.leafProjection i f z)) ^ 2 -
    (∑ i, (f z - S.leafProjection i f z) ^ 2) +
    θ / (2 * (Fintype.card D : ℝ)) * ∑ i, β i ^ 2 * (f z - S.leafProjection i f z) ^ 2

end ConditionalStar

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
namespace GraphStar
local instance (priority := 2000) graphStarTransferLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _
variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
  (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (v : V)

theorem residual_root_pair (σ : V → C) (f : (V → C) → ℝ) (z : C × (Leaf I v → C)) :
    GraphHeatBath.residual I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) v f
        (extend I v σ (Equiv.piOptionEquivProd.symm z)) =
      pull I v σ f z - (model I x hx hx1 hd hq v σ).centreProjection (pull I v σ f) z := by
  have h := congrFun (pull_root_projection I x hx hx1 hd hq v σ f) z
  change _ - _ = _ - _
  exact congrArg (fun t => pull I v σ f z - t) h

theorem residual_leaf_pair (hg : 5 ≤ I.graph.egirth) (σ : V → C)
    (f : (V → C) → ℝ) (z : C × (Leaf I v → C)) (u : Leaf I v) :
    GraphHeatBath.residual I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) u.val f
        (extend I v σ (Equiv.piOptionEquivProd.symm z)) =
      pull I v σ f z - (model I x hx hx1 hd hq v σ).leafProjection u (pull I v σ f) z := by
  have h := congrFun (pull_leaf_projection I x hx hx1 hd hq v hg σ f u) z
  change _ - _ = _ - _
  exact congrArg (fun t => pull I v σ f z - t) h

theorem pull_integrand (hg : 5 ≤ I.graph.egirth) (σ : V → C)
    (θ : ℝ) (f : (V → C) → ℝ) :
    pull I v σ (integrand I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) v θ f) =
      (model I x hx hx1 hd hq v σ).localForm (beta I v) θ (pull I v σ f) := by
  funext z
  unfold pull integrand incidenceResidual neighbourResidual
  simp only [residual_root_pair I x hx hx1 hd hq v,
    residual_leaf_pair I x hx hx1 hd hq v hg]
  rfl

/-- This internal assembly lemma has no spectral or mixing hypothesis. Its
local-form premise is discharged by the separately proved conditional-star estimate. -/
theorem localStarBound_of_conditional (hg : 5 ≤ I.graph.egirth) (hx0 : 0 < x)
    (hZ : 0 < I.partition x) (θ : ℝ)
    (hstar : ∀ v σ f, 0 ≤ expectReal (model I x hx hx1 hd hq v σ).jointLaw
      ((model I x hx hx1 hd hq v σ).localForm (beta I v) θ (pull I v σ f))) :
    (GraphHeatBath.system I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) hZ).LocalStarBound θ := by
  intro v z
  let μ := I.gibbs x hx hZ
  let f := supportedRepresent μ z
  have hn : 0 ≤ expectReal μ (integrand I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) v θ f) := by
    rw [gibbs_expectation I x hx hx1 hd hq v hg hx0 hZ]
    apply Finset.sum_nonneg
    intro σ _
    apply mul_nonneg (μ.nonneg σ)
    dsimp only
    rw [law_expectation I x hx hx1 hd hq v]
    change 0 ≤ expectReal (model I x hx hx1 hd hq v σ).jointLaw
      (pull I v σ (integrand I x hx (GraphHeatBath.sitePartition_pos I hx hx1 hd hq) v θ f))
    rw [pull_integrand I x hx hx1 hd hq v hg]
    exact hstar v σ f
  rw [integrand_expectation] at hn
  have he : supportedEmbed (I.gibbs x hx hZ) f = z := supportedEmbed_represent μ z
  rw [he] at hn
  linarith

end GraphStar
end
end CI2ZF.Appendix.Girth
