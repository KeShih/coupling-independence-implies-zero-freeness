import CI2ZF.Appendix.CV.GlobalCoupling
import CI2ZF.Appendix.CV.SingletonRegular
import CI2ZF.Appendix.CV.DiscountKernel

/-! The true root-recolouring event of the completed CV coupling, including
the saving from low-multiplicity available colours. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvRootEventDecEq : DecidableEq (V → C) := Classical.decEq _

def rootEventMass {μ ν : FinDist (V → C)} (γ : Coupling μ ν)
    (X Y : V → C) (v : V) : ℝ :=
  ∑ U, ∑ Z, if U v ≠ X v ∨ Z v ≠ Y v then γ.w U Z else 0

def rootBothMass {μ ν : FinDist (V → C)} (γ : Coupling μ ν)
    (X Y : V → C) (v : V) : ℝ :=
  ∑ U, ∑ Z, if U v ≠ X v ∧ Z v ≠ Y v then γ.w U Z else 0

def rootJointMass {μ ν : FinDist (V → C)} (γ : Coupling μ ν)
    (v : V) (c : C) : ℝ :=
  ∑ U, ∑ Z, if U v = c ∧ Z v = c then γ.w U Z else 0

lemma rootJointMass_nonneg {μ ν : FinDist (V → C)} (γ : Coupling μ ν)
    (v : V) (c : C) : 0 ≤ rootJointMass γ v c := by
  apply Finset.sum_nonneg
  intro U _
  apply Finset.sum_nonneg
  intro Z _
  split_ifs <;> simp_all [γ.nonneg]

lemma rootEventMass_union {μ ν : FinDist (V → C)} (γ : Coupling μ ν)
    (X Y : V → C) (v : V) :
    rootEventMass γ X Y v =
      (∑ U, if U v ≠ X v then μ.w U else 0) +
      (∑ Z, if Z v ≠ Y v then ν.w Z else 0) - rootBothMass γ X Y v := by
  have hx : (∑ U, if U v ≠ X v then μ.w U else 0) =
      ∑ U, ∑ Z, if U v ≠ X v then γ.w U Z else 0 := by
    apply Finset.sum_congr rfl
    intro U _
    split_ifs <;> simp [γ.sum_row]
  have hy : (∑ Z, if Z v ≠ Y v then ν.w Z else 0) =
      ∑ U, ∑ Z, if Z v ≠ Y v then γ.w U Z else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs <;> simp [γ.sum_col]
  rw [hx, hy]
  simp only [rootEventMass, rootBothMass, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro U _
  apply Finset.sum_congr rfl
  intro Z _
  by_cases hu : U v = X v <;> by_cases hz : Z v = Y v <;> simp [hu, hz]

lemma sum_regular_rootJointMass_le {μ ν : FinDist (V → C)} (γ : Coupling μ ν)
    (X Y : V → C) (v : V) :
    (∑ c, if c ≠ X v ∧ c ≠ Y v then rootJointMass γ v c else 0) ≤
      rootBothMass γ X Y v := by
  have hi (p : Prop) [Decidable p] (f : (V → C) → ℝ) :
      (if p then ∑ U, f U else 0) = ∑ U, if p then f U else 0 := by
    split_ifs <;> simp
  simp only [rootJointMass, hi]
  unfold rootBothMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro U _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro Z _
  rw [Finset.sum_eq_single (U v)]
  · by_cases hUZ : U v = Z v
    · rw [← hUZ]
      simp
    · have hZU := Ne.symm hUZ
      simp only [hZU, and_false, if_false, ite_self]
      split_ifs
      · exact γ.nonneg U Z
      · exact le_rfl
  · intro c _ hc
    simp [show U v ≠ c from Ne.symm hc]
  · simp

lemma rootJointMass_ge_point {μ ν : FinDist (V → C)} (γ : Coupling μ ν)
    (v : V) (c : C) (U Z : V → C) (hu : U v = c) (hz : Z v = c) :
    γ.w U Z ≤ rootJointMass γ v c := by
  calc
    _ = if U v = c ∧ Z v = c then γ.w U Z else 0 := by simp [hu, hz]
    _ ≤ ∑ W, if U v = c ∧ W v = c then γ.w U W else 0 := by
      apply Finset.single_le_sum _ (Finset.mem_univ Z)
      intro W _
      split_ifs <;> simp_all [γ.nonneg]
    _ ≤ _ := by
      unfold rootJointMass
      apply Finset.single_le_sum _ (Finset.mem_univ U)
      intro T _
      apply Finset.sum_nonneg
      intro W _
      split_ifs <;> simp_all [γ.nonneg]

lemma rootChangedMass_eq_rates [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (v : V) :
    (∑ U, if U v ≠ X v then (hardStep F X).w U else 0) =
      (∑ c, if c ≠ X v then rootRate F X v c else 0) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have ht (c : C) (hc : c ≠ X v) :
      targetProbability F X v c = rootRate F X v c /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
    rw [targetProbability_eq F X v c hc]
    unfold rootRate
    split_ifs <;> simp
  calc
    _ = ∑ c, if c ≠ X v then targetProbability F X v c else 0 := by
      have hi (p : Prop) [Decidable p] (f : (V → C) → ℝ) :
          (if p then ∑ U, f U else 0) = ∑ U, if p then f U else 0 := by
        split_ifs <;> simp
      simp only [targetProbability, hi]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _
      rw [Finset.sum_eq_single (U v)]
      · simp
      · intro c _ hc
        simp [show U v ≠ c from Ne.symm hc]
      · simp
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c ≠ X v
      · simp only [if_pos hc, ht c hc]
      · simp [hc]

def rootSingletonRebate (F : HardListInstance V C) (X : V → C)
    (v : V) (a b c : C) : ℝ :=
  if c ≠ a ∧ c ≠ b ∧ rootNeighbours F X v c = ∅ then
    if c ∈ F.list v then 1 else 0 else 0

lemma fullHardCoupling_rootJointMass_ge [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) :
    rootSingletonRebate FX X v a b c / ((Fintype.card V : ℝ) * Fintype.card C) ≤
      if c ≠ a ∧ c ≠ b then rootJointMass (fullHardCoupling h choice) v c else 0 := by
  unfold rootSingletonRebate
  by_cases hc : c ≠ a ∧ c ≠ b
  · rw [if_pos hc]
    by_cases hN : rootNeighbours FX X v c = ∅
    · rw [if_pos ⟨hc.1, hc.2, hN⟩]
      let U := flipConfiguration X (flipSet FX.graph X v c) (X v) c
      let Z := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
      have hs := singletonRegularPartial_full h choice hc.1 hc.2 hN U Z
      dsimp only at hs
      simp only [show U = flipConfiguration X (flipSet FX.graph X v c) (X v) c from rfl,
        show Z = flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c from rfl,
        and_self, if_true] at hs
      have hp := fullHardCoupling_dominate_selected h choice ⟨c, hc⟩ U Z
      have hn := (hardCommonOffRootPartial FX FY X Y v).nonneg U Z
      have hj := rootJointMass_ge_point (fullHardCoupling h choice) v c U Z
        (show U v = c from flipConfiguration_at_start)
        (show Z v = c from flipConfiguration_at_start)
      change (selectedRegularPartial h choice c).w U Z ≤ _ at hp
      linarith
    · rw [if_neg (by tauto), zero_div]
      exact rootJointMass_nonneg _ _ _
  · simp [hc, show ¬ (c ≠ a ∧ c ≠ b ∧ rootNeighbours FX X v c = ∅) from by tauto]

def rootEventCharge (FX FY : HardListInstance V C) (X Y : V → C)
    (v : V) (a b c : C) : ℝ :=
  (if c ≠ a then rootRate FX X v c else 0) +
    (if c ≠ b then rootRate FY Y v c else 0) - rootSingletonRebate FX X v a b c

theorem fullHardCoupling_rootEvent_charge_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
        rootEventMass (fullHardCoupling h choice) X Y v ≤
      ∑ c, rootEventCharge FX FY X Y v a b c := by
  have hreb := Finset.sum_le_sum (s := (Finset.univ : Finset C))
    (fun c _ => fullHardCoupling_rootJointMass_ge (c := c) h choice)
  have hboth := sum_regular_rootJointMass_le (fullHardCoupling h choice) X Y v
  rw [h.X_root, h.Y_root] at hboth
  have hb := hreb.trans hboth
  rw [← Finset.sum_div] at hb
  have he := rootEventMass_union (fullHardCoupling h choice) X Y v
  rw [rootChangedMass_eq_rates, rootChangedMass_eq_rates] at he
  simp only [h.X_root, h.Y_root] at he
  have hd : 0 < ((Fintype.card V : ℝ) * Fintype.card C) := by positivity
  have he' : rootEventMass (fullHardCoupling h choice) X Y v ≤
      (∑ c, rootEventCharge FX FY X Y v a b c) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
    simp only [rootEventCharge, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      sub_div, add_div]
    linarith
  simpa only [mul_comm] using (le_div_iff₀ hd).mp he'

lemma rootFlip_card_ge_neighbours (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) :
    (rootNeighbours F X v c).card + 1 ≤ (flipSet F.graph X v c).card := by
  classical
  have hs : insert v (rootNeighbours F X v c) ⊆ flipSet F.graph X v c := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact mem_flipSet.mpr .refl
    · exact (mem_root_flipSet_iff hc).mpr
        (Or.inr ⟨u, hu, self_mem_offRootComponent F X v u (X v) c⟩)
  have hv : v ∉ rootNeighbours F X v c := by simp
  simpa only [Finset.card_insert_of_notMem hv] using Finset.card_le_card hs

lemma rootRate_le_neighbour_profile (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) :
    rootRate F X v c ≤ mass ((rootNeighbours F X v c).card + 1) := by
  unfold rootRate
  split_ifs
  · exact mass_antitone (by omega) (rootFlip_card_ge_neighbours F X v c hc)
  · exact mass_nonneg _

lemma rootRate_le_one (F : HardListInstance V C) (X : V → C) (v : V) (c : C) :
    rootRate F X v c ≤ 1 := by
  unfold rootRate
  split_ifs
  · exact mass_le_one _
  · norm_num

lemma rootEventCharge_regular_zero
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : rootNeighbours FX X v c = ∅) :
    rootEventCharge FX FY X Y v a b c = if c ∈ FX.list v then 1 else 0 := by
  have hNY : rootNeighbours FY Y v c = ∅ := (h.rootNeighbours_eq hca hcb).symm.trans hN
  unfold rootEventCharge rootSingletonRebate
  rw [if_pos hca, if_pos hcb, if_pos ⟨hca, hcb, hN⟩,
    rootRate_of_no_neighbours FX X v c (by rwa [h.X_root]) hN,
    rootRate_of_no_neighbours FY Y v c (by rwa [h.Y_root]) hNY]
  simp only [← h.root_list_regular_iff c hca hcb]
  ring

lemma rootEventCharge_regular_nonzero_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : rootNeighbours FX X v c ≠ ∅) :
    rootEventCharge FX FY X Y v a b c ≤
      2 * mass ((rootNeighbours FX X v c).card + 1) := by
  have hx := rootRate_le_neighbour_profile FX X v c (by rwa [h.X_root])
  have hy := rootRate_le_neighbour_profile FY Y v c (by rwa [h.Y_root])
  rw [← h.rootNeighbours_eq hca hcb] at hy
  simp only [rootEventCharge, rootSingletonRebate, if_pos hca, if_pos hcb,
    hN, and_false, if_false, sub_zero]
  linarith

lemma rootEventCharge_le_one
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) :
    rootEventCharge FX FY X Y v a b c ≤ 1 := by
  by_cases hca : c = a
  · subst c
    simp only [rootEventCharge, rootSingletonRebate, ne_eq, not_true_eq_false,
      false_and, if_false, zero_add, sub_zero]
    split_ifs
    · norm_num
    · exact rootRate_le_one FY Y v a
  by_cases hcb : c = b
  · subst c
    simp only [rootEventCharge, rootSingletonRebate, ne_eq, not_true_eq_false,
      and_false, false_and, if_false, add_zero, sub_zero]
    simpa only [if_pos hca] using rootRate_le_one FX X v b
  by_cases hN : rootNeighbours FX X v c = ∅
  · rw [rootEventCharge_regular_zero h hca hcb hN]
    split_ifs <;> norm_num
  · have hp := rootEventCharge_regular_nonzero_le h hca hcb hN
    have hn : 0 < (rootNeighbours FX X v c).card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hN)
    have hm := mass_antitone (by norm_num : 1 ≤ 2)
      (by omega : 2 ≤ (rootNeighbours FX X v c).card + 1)
    change mass ((rootNeighbours FX X v c).card + 1) ≤ 81 / 250 at hm
    linarith

lemma rootEventCharge_low_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hk : (rootNeighbours FX X v c).card ≤ 2) :
    rootEventCharge FX FY X Y v a b c ≤
      1 - (81 / 250) * (if c ∈ FX.list v then ((rootNeighbours FX X v c).card : ℝ) else 0) := by
  by_cases hav : c ∈ FX.list v
  · rw [if_pos hav]
    by_cases hN : rootNeighbours FX X v c = ∅
    · rw [rootEventCharge_regular_zero h hca hcb hN]
      simp [hav, hN]
    · have hp := rootEventCharge_regular_nonzero_le h hca hcb hN
      have hn : 0 < (rootNeighbours FX X v c).card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hN)
      interval_cases he : (rootNeighbours FX X v c).card <;> norm_num [mass] at hp ⊢ <;>
        linarith
  · simp only [if_neg hav, mul_zero, sub_zero]
    exact rootEventCharge_le_one h

/-- The actual completed coupling pays at most one root event per colour,
with the required P₂ rebate for any set of regular colours of multiplicity
at most two. The set may be chosen from the original physical graph. -/
theorem fullHardCoupling_rootEvent_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (L : Finset C)
    (hL : ∀ c ∈ L, c ≠ a ∧ c ≠ b ∧ (rootNeighbours FX X v c).card ≤ 2) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
        rootEventMass (fullHardCoupling h choice) X Y v ≤
      Fintype.card C - (81 / 250) *
        ∑ c ∈ L, if c ∈ FX.list v then ((rootNeighbours FX X v c).card : ℝ) else 0 := by
  apply (fullHardCoupling_rootEvent_charge_le h choice).trans
  classical
  have hs : (∑ c, rootEventCharge FX FY X Y v a b c) ≤
      ∑ c, (1 - (81 / 250) *
        (if c ∈ L then if c ∈ FX.list v then ((rootNeighbours FX X v c).card : ℝ) else 0 else 0)) := by
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : c ∈ L
    · rw [if_pos hc]
      exact rootEventCharge_low_le h (hL c hc).1 (hL c hc).2.1 (hL c hc).2.2
    · simp only [if_neg hc, mul_zero, sub_zero]
      exact rootEventCharge_le_one h
  apply hs.trans_eq
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  congr 2
  simp

end
end CI2ZF.Appendix.CV
