import ZeroFreeness.Coupling.Vigoda.HardRegularCost
import ZeroFreeness.Coupling.Vigoda.HardBaselinePartition
import ZeroFreeness.Coupling.Vigoda.HardChargeSum

/-!
# The actual conditional hard coupling bound

The full matrix contains the common moves, every regular-colour matching,
and the two root-colour matchings. All transition capacities, residual
support decompositions, and component cost bounds are already proved for
the actual hard kernels. This module sums their charges and completes the
remaining mass to a genuine coupling.
-/

namespace ZeroFreeness

open PottsCI PottsCI.FinDist PottsCI.Vigoda RegularColourCharge
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]

/-- The actual full partial plan's completion charge is at most the sum
of the established per-colour charges in probability units. -/
theorem fullHard_charge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    hamCompletionCharge (fullHardPartial h) X Y ≤
      (∑ c : C, hardColourCharge h c) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun (c : RegularColour a b) _ => selectedRegular_charge_baseline_le h c.property.1 c.property.2)
  rw [Finset.sum_add_distrib] at hs
  have hb := common_hamCompletionCharge_partition h
  have hrX := rootBaseline_add_correction FX FY X Y v
  have hrY := rootBaseline_add_correction FY FX Y X v
  rw [fullHard_charge_eq, globalRegular_charge_eq, sum_hardColourCharge_eq,
    add_div, add_div, Finset.sum_div]
  linarith

/-- The completed actual coupling realizes the conditional hard budget.
No matching, capacity, support, or cost hypothesis is supplied. -/
theorem fullHardCoupling_cost_drift_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (fullHardCoupling h).cost ham - 1 ≤
      ((11 / 6 : ℝ) * (FX.graph ⊔ FY.graph).degree v -
        ((FX.list v ∩ FY.list v).card : ℝ)) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hcomplete := (fullHardPartial h).complete_cost_le_completionCharge hamDrift
    (ham X) (ham Y) (hamDrift_le_moves (rootLocal_ham_one h))
  rw [coupling_hamDrift_cost] at hcomplete
  have hc := (fullHard_charge_le h).trans
    (div_le_div_of_nonneg_right (sum_hardColourCharge_le h) (by positivity))
  exact hcomplete.trans hc

/-- A concrete root-local pair of hard instances satisfies the exact
Wasserstein drift bound used in the paper. -/
theorem hardStep_W_drift_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
      (W ham (hardStep FX X) (hardStep FY Y) - 1) ≤
      (11 / 6 : ℝ) * (FX.graph ⊔ FY.graph).degree v -
        ((FX.list v ∩ FY.list v).card : ℝ) := by
  have hN : 0 < (Fintype.card V : ℝ) * Fintype.card C := by positivity
  have hW := (sub_le_sub_right (W_le_cost ham_nonneg (fullHardCoupling h)) 1).trans
    (fullHardCoupling_cost_drift_le h)
  simpa only [mul_comm] using (le_div_iff₀ hN).mp hW

end
end ZeroFreeness
