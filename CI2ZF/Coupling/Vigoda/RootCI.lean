import CI2ZF.Coupling.Vigoda.RootBoundary
import CI2ZF.Coupling.Vigoda.RootCoupling
import CI2ZF.Coupling.Vigoda.HardCouplingInput

/-!
# Actual root coupling independence from the conditional hard estimate

All activation averaging, boundary perturbation, stationary comparison,
root-state identifications, and strict-regime endpoint limits are theorems.
This module exposes the local estimate for the actual hard flip kernels
as an input. `PottsCITheorem.lean` proves that estimate and discharges it.
-/

namespace CI2ZF.Potts

open PottsCI PottsCI.FinDist
attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]

/-- For actual root children, the hard estimate is the only remaining
one-step input: the two boundary comparisons are already discharged. -/
theorem root_soft_inputs_of_conditional_hard
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (a b : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hA : ConditionalHardCouplingEstimate (rootChildData tau G r a))
    (hB : ConditionalHardCouplingEstimate (rootChildData tau G r b))
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    SoftVigodaCouplingInputs (rootChildData tau G r a) (rootChildData tau G r b)
      (rootMiddleData tau G r) Δ x hx0 hx1 := by
  apply softVigoda_inputs_of_conditional_hard _ _ _
    (rootChildData_degreeBound tau G r a hdegree)
    (rootChildData_degreeBound tau G r b hdegree) hA hB x hx0 hx1
  · intro X
    exact rootChild_soft_boundary_W_le tau G r a hdegree X x hx0 hx1
  · intro X
    exact rootChild_soft_boundary_W_le tau G r b hdegree X x hx0 hx1

/-- The paper's exact strict-line root bound, including activities zero
and one and an empty remaining vertex set, from the actual hard estimate. -/
theorem root_strict_ci_from_hard_coupling
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hA : ∀ [Nonempty (RootRemaining tau r)],
      ConditionalHardCouplingEstimate (rootChildData tau G r a))
    (hB : ∀ [Nonempty (RootRemaining tau r)],
      ConditionalHardCouplingEstimate (rootChildData tau G r b))
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.le) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      ciBound (Fintype.card C) Δ x := by
  apply actual_root_children_strict_ci tau G r a b hΔ hdegree hq _ x hx1
  intro hV y hy0 hy1
  exact root_soft_inputs_of_conditional_hard tau G r a b hdegree hA hB y hy0 hy1

/-- Uniform strict-line root CI with the paper's constant `2/gap`. -/
theorem root_strict_uniform_ci_from_hard_coupling
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hA : ∀ [Nonempty (RootRemaining tau r)],
      ConditionalHardCouplingEstimate (rootChildData tau G r a))
    (hB : ∀ [Nonempty (RootRemaining tau r)],
      ConditionalHardCouplingEstimate (rootChildData tau G r b))
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.le) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      2 / ciGap (Fintype.card C) Δ := by
  apply actual_root_children_strict_uniform_ci tau G r a b hΔ hdegree hq _ x hx1
  intro hV y hy0 hy1
  exact root_soft_inputs_of_conditional_hard tau G r a b hdegree hA hB y hy0 hy1

/-- The critical-line compact-interval bound. A critical hard-endpoint
colouring estimate is a distinct result and is not silently assumed here. -/
theorem root_critical_uniform_ci_from_hard_coupling
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hA : ∀ [Nonempty (RootRemaining tau r)],
      ConditionalHardCouplingEstimate (rootChildData tau G r a))
    (hB : ∀ [Nonempty (RootRemaining tau r)],
      ConditionalHardCouplingEstimate (rootChildData tau G r b))
    {δ : ℝ} (hδ : 0 < δ) (x : PinningData.NonnegativeParameter)
    (hx : (x : ℝ) ∈ Set.Icc δ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x) ≤
      12 / (11 * δ) := by
  apply actual_root_children_critical_uniform_ci tau G r a b hΔ hdegree hq _ hδ x hx
  intro hV y hy0 hy1
  exact root_soft_inputs_of_conditional_hard tau G r a b hdegree hA hB y hy0 hy1

end

end CI2ZF.Potts
