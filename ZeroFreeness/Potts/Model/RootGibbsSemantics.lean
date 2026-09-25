import ZeroFreeness.Coupling.Vigoda.RootCoupling

/-!
# Original-graph semantics of the root laws, including the hard endpoint

At positive activity the pinned-only scalar always cancels. At zero,
this cancellation is valid for feasible pinnings, here expressed as zero
monochromatic edges inside the pinned vertex set.
-/

namespace ZeroFreeness.Potts

open PottsCI PottsCI.PartialColouring
attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C]

/-- A nonzero pinned-only scalar suffices to identify the original-graph
conditional weights with the normalized free law. -/
theorem normalized_full_weight_eq_childGibbs_of_scalar_ne_zero
    (tau : PartialColouring V C) (G : SimpleGraph V) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < (tau.toPinningData G).partition x) (hscalar : tau.pinnedScalar G x ≠ 0)
    (sigma : tau.FreeVertex → C) :
    fullPottsWeight G x (tau.extend sigma) / tau.conditionalFullPartition G x =
      (tau.childGibbs G x hx hZ).w sigma := by
  rw [tau.fullPottsWeight_extend G x sigma, tau.conditionalFullPartition_eq G x]
  rw [tau.childGibbs_apply G x hx hZ sigma]
  exact mul_div_mul_left _ _ hscalar

/-- For a proper hard pinning the original conditional coloring weights
are exactly the hard free Gibbs law. -/
theorem normalized_full_weight_eq_childGibbs_at_zero
    (tau : PartialColouring V C) (G : SimpleGraph V)
    (hZ : 0 < (tau.toPinningData G).partition 0)
    (hproper : tau.pinnedConflictCount G = 0) (sigma : tau.FreeVertex → C) :
    fullPottsWeight G 0 (tau.extend sigma) / tau.conditionalFullPartition G 0 =
      (tau.childGibbs G 0 le_rfl hZ).w sigma := by
  apply normalized_full_weight_eq_childGibbs_of_scalar_ne_zero
  simp [PartialColouring.pinnedScalar, hproper]

/-- Positive-activity root laws used in root CI are the original graph's
normalized conditional weights under `pinVertex`. -/
theorem actualRootChildGibbs_full_weight_pos [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a : C)
    {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx : 0 < (x : ℝ))
    (sigma : RootRemaining tau r → C) :
    fullPottsWeight G x ((pinVertex tau r a).extend sigma) /
        (pinVertex tau r a).conditionalFullPartition G x =
      (actualRootChildGibbs tau G r a hdegree hcolours x).w sigma := by
  exact (pinVertex tau r a).normalized_fullPottsWeight_eq_childGibbs G hx _ sigma

/-- The same identification at zero requires the new pinning to be proper
on its pinned vertices. The degree/color assumptions ensure an extension. -/
theorem actualRootChildGibbs_full_weight_zero [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a : C)
    {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (hproper : (pinVertex tau r a).pinnedConflictCount G = 0)
    (sigma : RootRemaining tau r → C) :
    fullPottsWeight G 0 ((pinVertex tau r a).extend sigma) /
        (pinVertex tau r a).conditionalFullPartition G 0 =
      (actualRootChildGibbs tau G r a hdegree hcolours PinningData.hardParameter).w sigma := by
  exact normalized_full_weight_eq_childGibbs_at_zero (pinVertex tau r a) G _ hproper sigma

end

end ZeroFreeness.Potts
