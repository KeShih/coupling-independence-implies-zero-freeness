import ZeroFreeness.Coupling.Vigoda.ActiveDegree
import ZeroFreeness.Coupling.Vigoda.HardChargeSum

/-! Specialization of every proved colour charge to the actual shared coins. -/
namespace ZeroFreeness
open PottsCI PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]

theorem activation_hardCharge_sum_le (I : PinningData V C) (X Y : V → C)
    (ω : I.Constraint → Bool) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ u, u ≠ v → X u = Y u) :
    ∑ c : C, hardColourCharge
      (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) c ≤
        (11 / 6 : ℝ) * rootFreeCoinCount I v ω - rootCommonListCount I X Y v ω := by
  have hb := sum_hardColourCharge_le
    (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree)
  change _ ≤ (11 / 6 : ℝ) * (((activeGraph I (activatedSet I X ω)) ⊔
      (activeGraph I (activatedSet I Y ω))).degree v : ℕ) -
    ((activeList I (activatedSet I X ω) v ∩ activeList I (activatedSet I Y ω) v).card : ℝ) at hb
  rw [union_active_degree_eq_coin_count I X Y ω v hroot hagree,
    ← rootCommonListCount_eq_card] at hb
  exact hb

end
end ZeroFreeness
