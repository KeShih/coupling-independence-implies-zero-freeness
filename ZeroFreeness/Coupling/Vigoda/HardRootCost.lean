import ZeroFreeness.Coupling.Vigoda.HardRootColourSeparation
import ZeroFreeness.Coupling.Vigoda.HardGlobalCost
import ZeroFreeness.Coupling.Vigoda.RootColourCharge

/-! Exact signed cost accounting for the two actual root-colour matches. -/
namespace ZeroFreeness
open PottsCI PottsCI.FinDist PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]
local instance hardRootCostConfigDecEq : DecidableEq (V → C) := Classical.decEq _

def rootBaseline (FX FY : HardListInstance V C) (X Y : V → C) (v : V) : ℝ :=
  let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
  rootColourOffCharge FX FY X Y v / ((Fintype.card V : ℝ) * Fintype.card C) +
    ham Y SY * (hardStep FY Y).w SY

def rootPointCorrection (FX FY : HardListInstance V C) (X Y : V → C) (v : V) : ℝ :=
  let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
  (hardStep FY Y).w SY * hamDefect X Y (rootColourPartner FX FY X Y v) SY

/-- Baseline size charges plus the exact prescribed match correction
are precisely the root-colour charge in probability units. -/
theorem rootBaseline_add_correction (FX FY : HardListInstance V C)
    (X Y : V → C) (v : V) :
    rootBaseline FX FY X Y v + rootPointCorrection FX FY X Y v =
      rootColourCharge FX FY X Y v / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hN : ((Fintype.card V : ℝ) * Fintype.card C) ≠ 0 := by positivity
  unfold rootBaseline rootPointCorrection rootColourCharge scaledMoveMass hamDefect
  field_simp
  ring

/-- The full constructed matrix adds exactly two root-colour corrections
to the already assembled regular-colour completion charge. -/
theorem fullHard_charge_eq
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    hamCompletionCharge (fullHardPartial h) X Y =
      hamCompletionCharge (globalRegularPartial h) X Y +
        rootPointCorrection FX FY X Y v + rootPointCorrection FY FX Y X v := by
  have hc : (fullHardPartial h).cost (hamDefect X Y) =
      (globalRegularPartial h).cost (hamDefect X Y) +
        rootPointCorrection FX FY X Y v + rootPointCorrection FY FX Y X v := by
    simp only [PartialCoupling.cost, fullHardPartial_w h, add_mul, Finset.sum_add_distrib]
    simp only [ite_mul, zero_mul, ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp only [rootPointCorrection]
    congr 1
    unfold hamDefect
    rw [ham_comm
      (flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v))]
    ring
  change _ + _ + (fullHardPartial h).cost (hamDefect X Y) = _
  rw [hc]
  unfold hamCompletionCharge PartialCoupling.completionCharge
  change _ + _ + ((globalRegularPartial h).cost (hamDefect X Y) + _ + _) =
    _ + _ + (globalRegularPartial h).cost (hamDefect X Y) + _ + _
  ring

end
end ZeroFreeness
