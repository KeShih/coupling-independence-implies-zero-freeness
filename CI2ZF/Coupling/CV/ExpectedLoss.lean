import CI2ZF.Coupling.CV.DiscountTotal
import CI2ZF.Coupling.CV.GlobalEnvelope

/-!
# Lemma `lem:cv-expected` (companion appendix CV, Lemma 5.14), per neighbour

For a regular root neighbour `u` with input discount `s_u =
incidenceDiscount I x X Y v u`, the charged loss `discountLoss` (root
recoloured: `s_u`; `u` recoloured into a target colour: `s_u`; every new
target blocker at an off-root neighbour: `θ s_u`) dominates the true decrease
of the `(v,u)` output summand (`discountLoss_dominates`), and
`crossCreditAt` is the same-neighbour ordered-incidence credit.  With
`L_x = lowAvailabilityMass I X Y v x` (equal to the paper's sum over regular
colours of multiplicity 1 or 2, `lowAvailabilityMass_eq_paper`) and
`β⁺_x = q - P₂ θ L_x + (1+P₂)Δ + 2`, `P₂ = 81/250`, `θ = 1 - x`:

  `E[Loss_u] - E[Credit_u] ≤ β⁺_x s_u / (nq)`  (`cv_expected`).

No root-event hypothesis remains: the root-event rate `eq:cv-root-event` is
supplied by `expected_active_rootEvent_le`.
-/

namespace CI2ZF.Appendix.CV

open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]

/-- `L_x` written as in `eq:cv-Lx`: regular colours of physical multiplicity
`1` or `2`. -/
theorem lowAvailabilityMass_eq_paper (I : PinningData V C) (X Y : V → C) (v : V) (x : ℝ) :
    lowAvailabilityMass I X Y v x =
      ∑ c ∈ Finset.univ.filter (fun c => c ≠ X v ∧ c ≠ Y v ∧
          ((physicalColourIncidences I X v c).card = 1 ∨
            (physicalColourIncidences I X v c).card = 2)),
        ((physicalColourIncidences I X v c).card : ℝ) * x ^ I.boundaryCount v c := by
  unfold lowAvailabilityMass physicalLowColours
  symm
  apply Finset.sum_subset
  · intro c hc
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, by omega⟩
  · intro c hc hnot
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.mp hc
    have h12 : ¬ ((physicalColourIncidences I X v c).card = 1 ∨
        (physicalColourIncidences I X v c).card = 2) :=
      fun hh => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, hh⟩)
    have h0 : (physicalColourIncidences I X v c).card = 0 := by omega
    simp [h0]

/-- The coefficient `β⁺_x`. -/
def betaPlus (q : ℝ) (Δ : ℕ) (x Lx : ℝ) : ℝ := q - (81 / 250) * (1 - x) * Lx + (1 + 81 / 250) * Δ + 2

/-- The root-event rate `eq:cv-root-event` in the form used by
`net_cost_average_le`. -/
theorem rootEvent_rate [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx) (fun ω =>
      rootEventMass (adjacentHardCoupling I X Y v hroot hagree choice ω) X Y v) ≤
        ((Fintype.card C : ℝ) - (81 / 250) * (1 - x) * lowAvailabilityMass I X Y v x) /
          ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hp := expected_active_rootEvent_le I X Y v hroot hagree choice
    (physicalLowColours I X Y v) (by intro c hc; exact (Finset.mem_filter.mp hc).2) x hx
  apply (le_div_iff₀ (by positivity : 0 < (Fintype.card V : ℝ) * Fintype.card C)).mpr
  simpa only [mul_comm, activityCoins, adjacentHardCoupling, lowAvailabilityMass] using hp

/-- The charged loss dominates the true decrease of the `(v,u)` summand. -/
theorem discountLoss_dominates (I : PinningData V C) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (X Y U Z : V → C) (v u : V) (hagree : ∀ w, w ≠ v → X w = Y w) :
    incidenceDiscount I x X Y v u -
        (if rootFixed X Y U Z v then incidenceDiscount I x U Z v u else 0) ≤
      discountLoss I x X Y U Z v u := by
  have h := incidenceDiscount_loss_le I hx X Y U Z v u hagree
  linarith

/-- `lem:cv-expected` for one regular neighbour `u`, with the explicit
`β⁺_x`, both for the charged loss and for the true loss of the `(v,u)`
summand. -/
theorem cv_expected [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (u : I.graph.neighborSet v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (Δ : ℕ) (hdegree : I.graph.degree u.val ≤ Δ) :
    averagedCost I X Y v hroot hagree choice x hx (fun U Z => discountLoss I x X Y U Z v u.val) -
        averagedCost I X Y v hroot hagree choice x hx (crossCreditAt I x X Y v u.val) ≤
      betaPlus (Fintype.card C) Δ x (lowAvailabilityMass I X Y v x) /
          ((Fintype.card V : ℝ) * Fintype.card C) * incidenceDiscount I x X Y v u.val ∧
    averagedCost I X Y v hroot hagree choice x hx (fun U Z =>
        incidenceDiscount I x X Y v u.val -
          (if rootFixed X Y U Z v then incidenceDiscount I x U Z v u.val else 0)) -
        averagedCost I X Y v hroot hagree choice x hx (crossCreditAt I x X Y v u.val) ≤
      betaPlus (Fintype.card C) Δ x (lowAvailabilityMass I X Y v x) /
          ((Fintype.card V : ℝ) * Fintype.card C) * incidenceDiscount I x X Y v u.val := by
  have hnet := net_cost_average_le I X Y v hroot hagree choice u x hx Δ hdegree _
    (rootEvent_rate I X Y v hroot hagree choice x hx)
  have hsplit : averagedCost I X Y v hroot hagree choice x hx (fun U Z =>
        discountLoss I x X Y U Z v u.val - crossCreditAt I x X Y v u.val U Z) =
      averagedCost I X Y v hroot hagree choice x hx (fun U Z => discountLoss I x X Y U Z v u.val) -
        averagedCost I X Y v hroot hagree choice x hx (crossCreditAt I x X Y v u.val) := by
    unfold averagedCost
    simp only [coupling_cost_sub, expectReal_sub]
  have hfirst : averagedCost I X Y v hroot hagree choice x hx
        (fun U Z => discountLoss I x X Y U Z v u.val) -
        averagedCost I X Y v hroot hagree choice x hx (crossCreditAt I x X Y v u.val) ≤
      betaPlus (Fintype.card C) Δ x (lowAvailabilityMass I X Y v x) /
          ((Fintype.card V : ℝ) * Fintype.card C) * incidenceDiscount I x X Y v u.val := by
    rw [← hsplit]
    apply hnet.trans_eq
    unfold betaPlus
    ring
  refine ⟨hfirst, le_trans ?_ hfirst⟩
  apply sub_le_sub_right
  unfold averagedCost
  apply expectReal_mono
  intro ω
  apply cost_le_cost
  intro U Z
  exact discountLoss_dominates I hx X Y U Z v u.val hagree

end

end CI2ZF.Appendix.CV
