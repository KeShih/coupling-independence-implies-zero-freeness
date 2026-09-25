import ZeroFreeness.Potts.Model.RootChildren
import ZeroFreeness.Coupling.Vigoda.CouplingIndependence

/-!
# Coupling bounds for the actual newly pinned root laws

This file instantiates the stationary-comparison endgame on the two actual
`pinVertex` children and their common root-deleted middle instance.
The remaining concrete one-step inputs remain explicit in each theorem.
-/

namespace ZeroFreeness.Potts

open PottsCI PottsCI.FinDist
attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]

/-- The paper's newly pinned Gibbs law on the common remaining free set. -/
def actualRootChildGibbs (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    (hcolours : Δ + 2 ≤ Fintype.card C) (x : PinningData.NonnegativeParameter) :
    FinDist (RootRemaining tau r → C) :=
  (pinVertex tau r a).childGibbs G x x.property
    ((rootChildData tau G r a).partition_pos x.property
      (rootChildData_degreeBound tau G r a hdegree) hcolours)

/-- The state-space identification is exact and also valid at activity zero. -/
theorem actualRootChildGibbs_eq (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    (hcolours : Δ + 2 ≤ Fintype.card C) (x : PinningData.NonnegativeParameter) :
    actualRootChildGibbs tau G r a hdegree hcolours x =
      (rootChildData tau G r a).nonnegativeGibbs
        (rootChildData_degreeBound tau G r a hdegree) hcolours x := rfl

/-- Strict-line CI for actual root pinnings, conditional only on the concrete
one-step estimates. The empty remaining state set and both endpoints are
handled by the previously proved endgame. -/
theorem actual_root_children_strict_ci (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hinputs : ∀ [Nonempty (RootRemaining tau r)],
      ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs (rootChildData tau G r a) (rootChildData tau G r b)
        (rootMiddleData tau G r) Δ x hx0 hx1)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.le) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      ciBound (Fintype.card C) Δ x := by
  rw [actualRootChildGibbs_eq, actualRootChildGibbs_eq]
  convert strict_ci_including_empty
    (rootChildData tau G r a) (rootChildData tau G r b) (rootMiddleData tau G r)
    hΔ (rootChildData_degreeBound tau G r a hdegree)
    (rootChildData_degreeBound tau G r b hdegree) hq hinputs x hx1 using 1
  all_goals congr 2 <;> exact Subsingleton.elim _ _

/-- The actual root laws satisfy the strict uniform `2 / gap` bound. -/
theorem actual_root_children_strict_uniform_ci
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hinputs : ∀ [Nonempty (RootRemaining tau r)],
      ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs (rootChildData tau G r a) (rootChildData tau G r b)
        (rootMiddleData tau G r) Δ x hx0 hx1)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.le) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.le) x) ≤
      2 / ciGap (Fintype.card C) Δ := by
  have hΔpos : (0 : ℝ) < Δ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hΔ)
  exact (actual_root_children_strict_ci tau G r a b hΔ hdegree hq hinputs x hx1).trans
    (ciBound_le_strict_uniform hΔpos ⟨x.property, hx1⟩ hq)

/-- The compact positive-interval critical bound for actual root laws.
The critical hard endpoint is proved separately (`critical_hard_colouring_input`). -/
theorem actual_root_children_critical_uniform_ci
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hinputs : ∀ [Nonempty (RootRemaining tau r)],
      ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      SoftVigodaCouplingInputs (rootChildData tau G r a) (rootChildData tau G r b)
        (rootMiddleData tau G r) Δ x hx0 hx1)
    {δ : ℝ} (hδ : 0 < δ) (x : PinningData.NonnegativeParameter)
    (hx : (x : ℝ) ∈ Set.Icc δ 1) :
    W ham
      (actualRootChildGibbs tau G r a hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x)
      (actualRootChildGibbs tau G r b hdegree (colours_slack_of_vigoda_line hΔ hq.ge) x) ≤
      12 / (11 * δ) := by
  rw [actualRootChildGibbs_eq, actualRootChildGibbs_eq]
  convert critical_uniform_ci_including_empty
    (rootChildData tau G r a) (rootChildData tau G r b) (rootMiddleData tau G r)
    hΔ (rootChildData_degreeBound tau G r a hdegree)
    (rootChildData_degreeBound tau G r b hdegree) hq hinputs hδ x hx using 1
  all_goals congr 2 <;> exact Subsingleton.elim _ _

end

end ZeroFreeness.Potts
