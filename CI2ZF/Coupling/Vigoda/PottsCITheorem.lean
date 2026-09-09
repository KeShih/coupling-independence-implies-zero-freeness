import CI2ZF.Coupling.Vigoda.HardCouplingCost
import CI2ZF.Coupling.Vigoda.ActiveDegree
import CI2ZF.Coupling.Vigoda.RootCI

/-! Coupling independence for the actual pinned Potts distributions.
The conditional hard estimate is proved here, rather than supplied as an
assumption to the stationary-comparison theorem. -/

namespace CI2ZF
open PottsCI PottsCI.FinDist PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C]

/-- The paper's conditional hard estimate for the two actual common-coin
activation outcomes, with no coupling or drift assumptions. -/
theorem conditionalHardCouplingEstimate [Nonempty V] [Nonempty C]
    (I : PinningData V C) : ConditionalHardCouplingEstimate I := by
  intro X Y v hroot hagree ω
  have hb := hardStep_W_drift_le
    (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree)
  change _ ≤ (11 / 6 : ℝ) * (((activeGraph I (activatedSet I X ω)) ⊔
      (activeGraph I (activatedSet I Y ω))).degree v : ℕ) -
    ((activeList I (activatedSet I X ω) v ∩ activeList I (activatedSet I Y ω) v).card : ℝ) at hb
  rw [union_active_degree_eq_coin_count I X Y ω v hroot hagree,
    ← rootCommonListCount_eq_card] at hb
  exact hb

namespace Potts
variable [Nonempty C]

/-- The exact root coupling-independence bound in the strict regime.
This includes activities `0` and `1`, an empty remaining graph, and
arbitrary original pinning. -/
theorem root_strict_ci
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.le) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      ciBound (Fintype.card C) Δ x := by
  apply root_strict_ci_from_hard_coupling tau G r a b hΔ hdegree hq
  · intro hV
    exact conditionalHardCouplingEstimate _
  · intro hV
    exact conditionalHardCouplingEstimate _
  · exact hx1

/-- A root CI constant depending only on `q` and `Δ`, uniformly over
all finite graphs, pinning data and real activities in `[0,1]`. -/
theorem root_strict_uniform_ci
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.le) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      2 / ciGap (Fintype.card C) Δ := by
  apply root_strict_uniform_ci_from_hard_coupling tau G r a b hΔ hdegree hq
  · intro hV
    exact conditionalHardCouplingEstimate _
  · intro hV
    exact conditionalHardCouplingEstimate _
  · exact hx1

/-- On the critical line, every compact interval `[δ,1]` with `δ>0`
has the paper's uniform CI constant. The critical hard endpoint is a
separate theorem and is not part of this statement. -/
theorem root_critical_uniform_ci
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    {δ : ℝ} (hδ : 0 < δ) (x : PinningData.NonnegativeParameter)
    (hx : (x : ℝ) ∈ Set.Icc δ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x) ≤
      12 / (11 * δ) := by
  apply root_critical_uniform_ci_from_hard_coupling tau G r a b hΔ hdegree hq
  · intro hV
    exact conditionalHardCouplingEstimate _
  · intro hV
    exact conditionalHardCouplingEstimate _
  · exact hδ
  · exact hx

end Potts
end
end CI2ZF
