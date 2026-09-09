import CI2ZF.Coupling.Girth.Spectral.Graph.HeatBath
import CI2ZF.Coupling.Girth.Spectral.Graph.Operators
import CI2ZF.Coupling.Girth.Spectral.MeanZero

/-! The graph-projection system is instantiated by actual Gibbs heat baths. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators InnerProductSpace
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
  (hlocal : ∀ σ v, 0 < sitePartition I x σ v) (hZ : 0 < I.partition x)

def complement (v : V) : SupportedSpace (I.gibbs x hx hZ) →ₗ[ℝ]
    SupportedSpace (I.gibbs x hx hZ) :=
  LinearMap.id - (heatBath I x hx hlocal hZ v).operator

theorem complement_projection (v : V) : Schur.Projection (complement I x hx hlocal hZ v) where
  symmetric z w := by
    simp only [complement, LinearMap.sub_apply, LinearMap.id_apply,
      inner_sub_left, inner_sub_right, heatBath_symmetric]
  idem z := by
    simp only [complement, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      heatBath_idempotent, sub_self, sub_zero]

theorem complement_commute (v u : V) (hu : ¬ I.graph.Adj v u) :
    Commute (complement I x hx hlocal hZ v) (complement I x hx hlocal hZ u) := by
  show _ * _ = _ * _
  apply LinearMap.ext
  intro z
  change complement I x hx hlocal hZ v (complement I x hx hlocal hZ u z) =
    complement I x hx hlocal hZ u (complement I x hx hlocal hZ v z)
  simp only [complement, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [heatBath_commute I x hx hlocal hZ v u hu z]
  abel

def system : GraphProjections I.graph (SupportedSpace (I.gibbs x hx hZ)) where
  Q := complement I x hx hlocal hZ
  projection := complement_projection I x hx hlocal hZ
  nonadjacent_commute := complement_commute I x hx hlocal hZ

/-- The degree and colour assumptions discharge every local normalizer. -/
def boundedSystem (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) : GraphProjections I.graph (SupportedSpace (I.gibbs x hx hZ)) :=
  system I x hx (sitePartition_pos I hx hx1 hd hq) hZ

theorem heatBath_one (v : V) :
    (heatBath I x hx hlocal hZ v).operator (supportedOne (I.gibbs x hx hZ)) =
      supportedOne (I.gibbs x hx hZ) := by
  unfold supportedOne
  rw [SupportedOperator.intertwine]
  exact congrArg (supportedEmbed _) (projection_const I x hx hlocal v 1)

theorem complement_one (v : V) :
    complement I x hx hlocal hZ v (supportedOne (I.gibbs x hx hZ)) = 0 := by
  simp only [complement, LinearMap.sub_apply, LinearMap.id_apply, heatBath_one, sub_self]

theorem laplacian_one :
    (system I x hx hlocal hZ).laplacian (supportedOne (I.gibbs x hx hZ)) = 0 := by
  simp only [GraphProjections.laplacian, LinearMap.sum_apply, system, complement_one,
    Finset.sum_const_zero]

end GraphHeatBath
end
end CI2ZF.Appendix.Girth
