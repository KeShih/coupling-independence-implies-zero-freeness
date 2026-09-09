import CI2ZF.Coupling.CV.BaselinePartition

/-! Hamming drift of the actual full CV coupling, bounded by the derived
sum of its concrete graph-component charges. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]
local instance cvCouplingChargeDecEq : DecidableEq (V → C) := Classical.decEq _

def hardColourCharge {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (c : C) : ℝ :=
  if hca : c = a then rootColourCharge FX FY X Y v
  else if hcb : c = b then rootColourCharge FY FX Y X v
  else canonicalColourCharge h hca hcb (choice.left c) (choice.right c)

theorem sum_hardColourCharge_eq
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) :
    ∑ c : C, hardColourCharge h choice c =
      rootColourCharge FX FY X Y v + rootColourCharge FY FX Y X v +
        ∑ c : {c : C // c ≠ a ∧ c ≠ b},
          canonicalColourCharge h c.property.1 c.property.2 (choice.left c.val) (choice.right c.val) := by
  have heach (c : C) : hardColourCharge h choice c =
      (if c = a then rootColourCharge FX FY X Y v else 0) +
      (if c = b then rootColourCharge FY FX Y X v else 0) +
      (if c ≠ a ∧ c ≠ b then hardColourCharge h choice c else 0) := by
    by_cases hca : c = a
    · subst c
      simp [hardColourCharge, h.colours_ne]
    · by_cases hcb : c = b
      · subst c
        simp [hardColourCharge, hca]
      · simp [hca, hcb]
  have hreg : (∑ c : {c : C // c ≠ a ∧ c ≠ b},
        canonicalColourCharge h c.property.1 c.property.2 (choice.left c.val) (choice.right c.val)) =
      ∑ c : C, if c ≠ a ∧ c ≠ b then hardColourCharge h choice c else 0 := by
    calc
      _ = ∑ c : {c : C // c ≠ a ∧ c ≠ b}, hardColourCharge h choice c.val := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [hardColourCharge, dif_neg c.property.1, dif_neg c.property.2]
      _ = ∑ c ∈ Finset.univ.filter (fun c => c ≠ a ∧ c ≠ b), hardColourCharge h choice c :=
        (Finset.sum_subtype _ (by simp) _).symm
      _ = _ := by rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun c _ => heach c)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hreg]
/-- The actual full partial plan's completion charge is at most the sum
of the established per-colour charges in probability units. -/
theorem fullHard_charge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) :
    hamCompletionCharge (fullHardPartial h choice) X Y ≤
      (∑ c : C, hardColourCharge h choice c) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun (c : RegularColour a b) _ => selectedRegular_charge_baseline_le h choice c.property.1 c.property.2)
  rw [Finset.sum_add_distrib] at hs
  have hb := common_hamCompletionCharge_partition h
  have hrX := rootBaseline_add_correction FX FY X Y v
  have hrY := rootBaseline_add_correction FY FX Y X v
  rw [fullHard_charge_eq, globalRegular_charge_eq, sum_hardColourCharge_eq,
    add_div, add_div, Finset.sum_div]
  linarith

theorem fullHardCoupling_cost_charge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) :
    ((Fintype.card V : ℝ) * Fintype.card C) * ((fullHardCoupling h choice).cost ham - 1) ≤
      ∑ c : C, hardColourCharge h choice c := by
  have hcomplete := (fullHardPartial h choice).complete_cost_le_completionCharge hamDrift
    (ham X) (ham Y) (hamDrift_le_moves (rootLocal_ham_one h))
  rw [coupling_hamDrift_cost] at hcomplete
  have hb := hcomplete.trans (fullHard_charge_le h choice)
  have hN : 0 < (Fintype.card V : ℝ) * Fintype.card C := by positivity
  simpa only [fullHardCoupling, mul_comm] using (le_div_iff₀ hN).mp hb

end
end CI2ZF.Appendix.CV
