import CI2ZF.Appendix.Girth.Five.Poincare
import PottsCI.Potts.Endpoint
import CI2ZF.PottsModel

/-! The actual girth-five Poincaré inequality at every activity in [0,1].
The hard endpoint follows from continuity of finite normalized sums; no
irreducibility or spectral-gap hypothesis is imposed at activity zero. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts Finset Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

namespace GraphHeatBath

def projectionValue (I : PinningData V C) (x : ℝ) (v : V) (f : (V → C) → ℝ) (σ : V → C) : ℝ :=
  ∑ c, (siteWeight I x σ v c / sitePartition I x σ v) * f (Function.update σ v c)

def meanValue (I : PinningData V C) (x : ℝ) (f : (V → C) → ℝ) : ℝ :=
  ∑ σ, (I.weight x σ / I.partition x) * f σ

def varianceValue (I : PinningData V C) (x : ℝ) (f : (V → C) → ℝ) : ℝ :=
  ∑ σ, (I.weight x σ / I.partition x) * (f σ - meanValue I x f) ^ 2

def dirichletValue (I : PinningData V C) (x : ℝ) (f : (V → C) → ℝ) : ℝ :=
  ∑ v, ∑ σ, (I.weight x σ / I.partition x) * (f σ - projectionValue I x v f σ) ^ 2

theorem projection_eq_value (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    (hlocal : ∀ σ v, 0 < sitePartition I x σ v) (v : V) (f : (V → C) → ℝ) (σ : V → C) :
    projection I x hx hlocal v f σ = projectionValue I x v f σ := rfl

theorem variance_eq_value (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < I.partition x) (f : (V → C) → ℝ) :
    variance (I.gibbs x hx hZ) f = varianceValue I x f := rfl

theorem dirichlet_eq_value (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
    (hlocal : ∀ σ v, 0 < sitePartition I x σ v) (hZ : 0 < I.partition x) (f : (V → C) → ℝ) :
    (∑ v, expectReal (I.gibbs x hx hZ) (fun σ => (f σ - projection I x hx hlocal v f σ) ^ 2)) =
      dirichletValue I x f := rfl

theorem continuous_siteWeight (I : PinningData V C) (σ : V → C) (v : V) (c : C) :
    Continuous (fun x : ℝ => siteWeight I x σ v c) := continuous_id.pow _

theorem continuous_sitePartition (I : PinningData V C) (σ : V → C) (v : V) :
    Continuous (fun x : ℝ => sitePartition I x σ v) := by
  unfold sitePartition
  exact continuous_finsetSum _ fun c _ => continuous_siteWeight I σ v c

theorem continuousAt_projectionValue (I : PinningData V C) {x : ℝ}
    (hlocal : ∀ σ v, sitePartition I x σ v ≠ 0) (v : V) (f : (V → C) → ℝ) (σ : V → C) :
    ContinuousAt (fun y => projectionValue I y v f σ) x := by
  unfold projectionValue
  apply tendsto_finsetSum
  intro c _
  exact (((continuous_siteWeight I σ v c).continuousAt).div
    ((continuous_sitePartition I σ v).continuousAt) (hlocal σ v)).mul continuousAt_const

theorem continuousAt_meanValue (I : PinningData V C) {x : ℝ} (hZ : I.partition x ≠ 0)
    (f : (V → C) → ℝ) : ContinuousAt (fun y => meanValue I y f) x := by
  unfold meanValue
  apply tendsto_finsetSum
  intro σ _
  exact ((I.continuous_weight σ).continuousAt.div I.continuous_partition.continuousAt hZ).mul continuousAt_const

theorem continuousAt_varianceValue (I : PinningData V C) {x : ℝ} (hZ : I.partition x ≠ 0)
    (f : (V → C) → ℝ) : ContinuousAt (fun y => varianceValue I y f) x := by
  unfold varianceValue
  apply tendsto_finsetSum
  intro σ _
  exact ((I.continuous_weight σ).continuousAt.div I.continuous_partition.continuousAt hZ).mul
    ((continuousAt_const.sub (continuousAt_meanValue I hZ f)).pow 2)

theorem continuousAt_dirichletValue (I : PinningData V C) {x : ℝ} (hZ : I.partition x ≠ 0)
    (hlocal : ∀ σ v, sitePartition I x σ v ≠ 0) (f : (V → C) → ℝ) :
    ContinuousAt (fun y => dirichletValue I y f) x := by
  unfold dirichletValue
  apply tendsto_finsetSum
  intro v _
  apply tendsto_finsetSum
  intro σ _
  exact ((I.continuous_weight σ).continuousAt.div I.continuous_partition.continuousAt hZ).mul
    ((continuousAt_const.sub (continuousAt_projectionValue I hlocal v f σ)).pow 2)

end GraphHeatBath

variable [Nonempty C]

theorem girth_five_poincare_value (I : PinningData V C)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (f : (V → C) → ℝ) :
    GraphProjections.spectralGap δ * GraphHeatBath.varianceValue I x f ≤ GraphHeatBath.dirichletValue I x f := by
  have hq1 : Δ + 1 ≤ Fintype.card C := by
    have hh := girthFive_colour_slack hδ hδ1 hΔ hq
    omega
  have hp {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
      GraphProjections.spectralGap δ * GraphHeatBath.varianceValue I y f ≤ GraphHeatBath.dirichletValue I y f := by
    exact girth_five_positive_poincare I hy hy1 hδ hδ1 hΔ hdegree hg hq
      (partition_pos_of_succ_le I hy.le hdegree hq1) f
  rcases hx.eq_or_lt with hzero | hpos
  · subst x
    have hZ : I.partition 0 ≠ 0 := (partition_zero_pos_of_succ_le I hdegree hq1).ne'
    have hlocal : ∀ σ v, GraphHeatBath.sitePartition I 0 σ v ≠ 0 := fun σ v =>
      (GraphHeatBath.sitePartition_pos I le_rfl (by norm_num) hdegree hq1 σ v).ne'
    have hc : ContinuousAt (fun y => GraphProjections.spectralGap δ * GraphHeatBath.varianceValue I y f -
        GraphHeatBath.dirichletValue I y f) 0 :=
      (continuousAt_const.mul (GraphHeatBath.continuousAt_varianceValue I hZ f)).sub
        (GraphHeatBath.continuousAt_dirichletValue I hZ hlocal f)
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hh : ∀ n : ℕ, GraphProjections.spectralGap δ * GraphHeatBath.varianceValue I (1 / (n + 1)) f -
        GraphHeatBath.dirichletValue I (1 / (n + 1)) f ≤ 0 := by
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hn1 : (1 : ℝ) / (n + 1) ≤ 1 := (div_le_one hn).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
      exact sub_nonpos.mpr (hp (one_div_pos.mpr hn) hn1)
    have he := le_of_tendsto (hc.tendsto.comp ht) (Filter.Eventually.of_forall hh)
    exact sub_nonpos.mp he
  · exact hp hpos hx1

/-- All activities, including the hard-colouring endpoint, with only the
original graph, palette and degree assumptions. -/
theorem girth_five_closed_poincare (I : PinningData V C)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (f : (V → C) → ℝ) :
    let hq1 : Δ + 1 ≤ Fintype.card C := by have hh := girthFive_colour_slack hδ hδ1 hΔ hq; omega
    let hZ := partition_pos_of_succ_le I hx hdegree hq1
    let hlocal := GraphHeatBath.sitePartition_pos I hx hx1 hdegree hq1
    GraphProjections.spectralGap δ * variance (I.gibbs x hx hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx hZ) (fun σ => (f σ - GraphHeatBath.projection I x hx hlocal v f σ) ^ 2) :=
  girth_five_poincare_value I hx hx1 hδ hδ1 hΔ hdegree hg hq f

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 ≤ x)
  (hlocal : ∀ σ v, 0 < sitePartition I x σ v) (hZ : 0 < I.partition x)

theorem projection_update_nonnegative (v : V) (f : (V → C) → ℝ) (σ : V → C) (c : C) :
    projection I x hx hlocal v f (Function.update σ v c) = projection I x hx hlocal v f σ := by
  unfold projection
  simp only [Function.update_idem,
    siteLaw_update_of_not_adj I x hx hlocal σ v v I.graph.irrefl]

theorem projection_stationary_nonnegative (v : V) (f : (V → C) → ℝ) :
    expectReal (I.gibbs x hx hZ) (projection I x hx hlocal v f) = expectReal (I.gibbs x hx hZ) f := by
  have hh := projection_selfAdjoint I x hx hlocal hZ v f (fun _ => 1)
  rw [projection_const] at hh
  simpa only [mul_one] using hh

theorem expect_siteVariance (v : V) (f : (V → C) → ℝ) :
    expectReal (I.gibbs x hx hZ) (fun σ =>
      variance (siteLaw I x hx hlocal σ v) (fun c => f (Function.update σ v c))) =
    expectReal (I.gibbs x hx hZ) (fun σ => (f σ - projection I x hx hlocal v f σ) ^ 2) := by
  have hh (σ : V → C) : variance (siteLaw I x hx hlocal σ v) (fun c => f (Function.update σ v c)) =
      projection I x hx hlocal v (fun τ => (f τ - projection I x hx hlocal v f τ) ^ 2) σ := by
    change expectReal (siteLaw I x hx hlocal σ v)
      (fun c => (f (Function.update σ v c) - projection I x hx hlocal v f σ) ^ 2) = _
    unfold projection
    apply congrArg (expectReal _)
    funext c
    congr 2
    exact (projection_update_nonnegative I x hx hlocal v f σ c).symm
  simp_rw [hh]
  exact projection_stationary_nonnegative I x hx hlocal hZ v _

end GraphHeatBath

/-- The same closed-interval result in the actual conditional-variance form. -/
theorem girth_five_closed_poincare_conditional (I : PinningData V C)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveThreshold δ ≤ Δ)
    (hdegree : I.DegreeBound Δ) (hg : 5 ≤ I.graph.egirth)
    (hq : (1+δ) * Δ ≤ (Fintype.card C : ℝ)) (f : (V → C) → ℝ) :
    let hq1 : Δ + 1 ≤ Fintype.card C := by have hh := girthFive_colour_slack hδ hδ1 hΔ hq; omega
    let hZ := partition_pos_of_succ_le I hx hdegree hq1
    let hlocal := GraphHeatBath.sitePartition_pos I hx hx1 hdegree hq1
    GraphProjections.spectralGap δ * variance (I.gibbs x hx hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx hZ) (fun σ =>
        variance (GraphHeatBath.siteLaw I x hx hlocal σ v) (fun c => f (Function.update σ v c))) := by
  dsimp only
  simp_rw [GraphHeatBath.expect_siteVariance]
  exact girth_five_closed_poincare I hx hx1 hδ hδ1 hΔ hdegree hg hq f

end
end CI2ZF.Appendix.Girth
