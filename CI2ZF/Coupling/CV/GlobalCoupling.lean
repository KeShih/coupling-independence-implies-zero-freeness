import CI2ZF.Coupling.CV.RootColours
import CI2ZF.Coupling.CV.GlobalRegular
import CI2ZF.Coupling.Vigoda.HardRootColourSeparation

/-! One actual CV coupling containing all regular-colour and both root-colour
plans. Full row/column capacities follow from disjoint concrete move outputs. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvGlobalCouplingColouringDecEq : DecidableEq (V → C) := Classical.decEq _

lemma hardCommonOffRoot_transpose_w [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C) :
    (hardCommonOffRootPartial FY FX Y X v).w Z U =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  have hi : (Z v = Y v ∧ Z ≠ Y ∧ U = replaceRoot Z v (X v)) ↔
      (U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)) :=
    ⟨common_condition_reverse Y X Z U v (fun w hw => (h.agree_off_root w hw).symm),
      common_condition_reverse X Y U Z v h.agree_off_root⟩
  simp only [hardCommonOffRootPartial, commonOffRootPartial, hi, min_comm]
  split_ifs <;> rfl

def reverseRootColourPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  (rootColourPartial FY FX Y X v).transpose

theorem reverseRootColourPartial_full [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C) :
    (reverseRootColourPartial FX FY X Y v).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z +
        if U = flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v) ∧
          Z = rootColourPartner FY FX Y X v
        then (hardStep FX X).w U else 0 := by
  change (rootColourPartial FY FX Y X v).w Z U = _
  rw [rootColourPartial_full h.symm, hardCommonOffRoot_transpose_w h]
  congr 1
  by_cases hc : U = flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v) ∧
      Z = rootColourPartner FY FX Y X v
  · rw [if_pos hc, if_pos ⟨hc.2, hc.1⟩, hc.1]
  · rw [if_neg hc, if_neg (fun hh => hc ⟨hh.2, hh.1⟩)]

lemma globalRegularPartial_ge_common [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ (globalRegularPartial h choice).w U Z := by
  change _ ≤ _ + ∑ c : RegularColour a b, _
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun c _ => sub_nonneg.mpr (selectedRegularPartial_ge_common h choice c U Z)

lemma globalRegularPartial_eq_common_off_allRows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C)
    (hU : U ∉ allRegularRows FX X v a b) :
    (globalRegularPartial h choice).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  have hz (c : RegularColour a b) : (selectedRegularPartial h choice c).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z :=
    selectedRegularPartial_eq_common_off_rows h choice c.property.1 c.property.2 U Z
      (fun hm => hU (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hm⟩))
  change _ + (∑ c : RegularColour a b, _) = _
  simp only [hz, sub_self, Finset.sum_const_zero, add_zero]

lemma globalRegularPartial_eq_common_off_allCols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C)
    (hZ : Z ∉ allRegularRows FY Y v b a) :
    (globalRegularPartial h choice).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  have hz (c : RegularColour a b) : (selectedRegularPartial h choice c).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z :=
    selectedRegularPartial_eq_common_off_cols h choice c.property.1 c.property.2 U Z
      (fun hm => hZ (Finset.mem_biUnion.mpr
        ⟨⟨c.val, c.property.2, c.property.1⟩, Finset.mem_univ _, hm⟩))
  change _ + (∑ c : RegularColour a b, _) = _
  simp only [hz, sub_self, Finset.sum_const_zero, add_zero]

def fullColourPlans [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) : Fin 3 → PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  ![globalRegularPartial h choice, rootColourPartial FX FY X Y v, reverseRootColourPartial FX FY X Y v]

lemma fullColourPlans_ge_common [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (k : Fin 3) (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ (fullColourPlans h choice k).w U Z := by
  fin_cases k
  · exact globalRegularPartial_ge_common h choice U Z
  · change _ ≤ (rootColourPartial FX FY X Y v).w U Z
    rw [rootColourPartial_full h]
    apply le_add_of_nonneg_right
    split_ifs
    · exact (hardStep FY Y).nonneg _
    · exact le_rfl
  · change _ ≤ (reverseRootColourPartial FX FY X Y v).w U Z
    rw [reverseRootColourPartial_full h]
    apply le_add_of_nonneg_right
    split_ifs
    · exact (hardStep FX X).nonneg _
    · exact le_rfl

lemma fullColourPlans_eq_common_off_rows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (k : Fin 3) (U Z : V → C)
    (hU : U ∉ fullColourRows h k) :
    (fullColourPlans h choice k).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  fin_cases k
  · exact globalRegularPartial_eq_common_off_allRows h choice U Z hU
  · have hne : U ≠ rootColourPartner FX FY X Y v := by simpa [fullColourRows] using hU
    change (rootColourPartial FX FY X Y v).w U Z = _
    rw [rootColourPartial_full h]
    simp [hne]
  · have hne : U ≠ flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v) := by
      simpa [fullColourRows] using hU
    change (reverseRootColourPartial FX FY X Y v).w U Z = _
    rw [reverseRootColourPartial_full h]
    simp [hne]

lemma fullColourPlans_eq_common_off_cols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (k : Fin 3) (U Z : V → C)
    (hZ : Z ∉ fullColourCols h k) :
    (fullColourPlans h choice k).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  fin_cases k
  · exact globalRegularPartial_eq_common_off_allCols h choice U Z hZ
  · have hne : Z ≠ flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v) := by
      simpa [fullColourCols] using hZ
    change (rootColourPartial FX FY X Y v).w U Z = _
    rw [rootColourPartial_full h]
    simp [hne]
  · have hne : Z ≠ rootColourPartner FY FX Y X v := by simpa [fullColourCols] using hZ
    change (reverseRootColourPartial FX FY X Y v).w U Z = _
    rw [reverseRootColourPartial_full h]
    simp [hne]

/-- All regular and both root-colour allocations coexist inside the actual
hard transition marginals. No capacity or support hypothesis is supplied. -/
def fullHardPartial [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) : PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  PartialCoupling.combineDisjoint (hardCommonOffRootPartial FX FY X Y v)
    (fullColourPlans h choice) (fullColourRows h) (fullColourCols h)
    (fullColourPlans_ge_common h choice) (fullColourPlans_eq_common_off_rows h choice)
    (fullColourPlans_eq_common_off_cols h choice) (fullColourRows_disjoint h) (fullColourCols_disjoint h)

def fullHardCoupling [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) : Coupling (hardStep FX X) (hardStep FY Y) :=
  (fullHardPartial h choice).complete

theorem fullHardPartial_w [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C) :
    (fullHardPartial h choice).w U Z = (globalRegularPartial h choice).w U Z +
      (if U = rootColourPartner FX FY X Y v ∧
          Z = flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
        then (hardStep FY Y).w Z else 0) +
      (if U = flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v) ∧
          Z = rootColourPartner FY FX Y X v
        then (hardStep FX X).w U else 0) := by
  simp only [fullHardPartial, PartialCoupling.combineDisjoint]
  simp only [Fin.sum_univ_succ, fullColourPlans, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  rw [rootColourPartial_full h, reverseRootColourPartial_full h]
  by_cases hz : Z = flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
  · rw [hz]
    ring
  · simp only [hz, and_false, if_false]
    ring

lemma globalRegularPartial_dominate_selected [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (c : RegularColour a b) (U Z : V → C) :
    (selectedRegularPartial h choice c).w U Z ≤ (globalRegularPartial h choice).w U Z := by
  by_cases hU : U ∈ regularMoveRows FX X v b c.val
  · rw [globalRegularPartial_eq_selected_on_rows h choice c U Z hU]
  · rw [selectedRegularPartial_eq_common_off_rows h choice c.property.1 c.property.2 U Z hU]
    exact globalRegularPartial_ge_common h choice U Z

lemma fullHardPartial_dominate_plan [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (k : Fin 3) (U Z : V → C) :
    (fullColourPlans h choice k).w U Z ≤ (fullHardPartial h choice).w U Z := by
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => (fullColourPlans h choice j).w U Z -
      (hardCommonOffRootPartial FX FY X Y v).w U Z)
    (fun j _ => sub_nonneg.mpr (fullColourPlans_ge_common h choice j U Z)) (Finset.mem_univ k)
  change _ ≤ (hardCommonOffRootPartial FX FY X Y v).w U Z + _
  linarith

lemma fullHardCoupling_dominate_partial [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C) :
    (fullHardPartial h choice).w U Z ≤ (fullHardCoupling h choice).w U Z := by
  change _ ≤ (fullHardPartial h choice).w U Z + _
  apply le_add_of_nonneg_right
  exact div_nonneg (mul_nonneg ((fullHardPartial h choice).leftResidual_nonneg U)
    ((fullHardPartial h choice).rightResidual_nonneg Z)) (fullHardPartial h choice).residualTotal_nonneg

theorem fullHardCoupling_dominate_common [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ (fullHardCoupling h choice).w U Z :=
  (globalRegularPartial_ge_common h choice U Z).trans
    ((fullHardPartial_dominate_plan h choice 0 U Z).trans
      (fullHardCoupling_dominate_partial h choice U Z))

theorem fullHardCoupling_dominate_selected [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (c : RegularColour a b) (U Z : V → C) :
    (selectedRegularPartial h choice c).w U Z ≤ (fullHardCoupling h choice).w U Z :=
  (globalRegularPartial_dominate_selected h choice c U Z).trans
    ((fullHardPartial_dominate_plan h choice 0 U Z).trans
      (fullHardCoupling_dominate_partial h choice U Z))

theorem fullHardCoupling_dominate_canonical [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (c : RegularColour a b) (hN : (rootNeighbours FX X v c.val).Nonempty) (U Z : V → C) :
    (canonicalRegularPartial FX FY X Y v c (choice.left c) (choice.right c)).w U Z ≤
      (fullHardCoupling h choice).w U Z := by
  simpa only [selectedRegularPartial, if_pos hN] using
    fullHardCoupling_dominate_selected h choice c U Z

theorem fullHardCoupling_dominate_root [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C) :
    (rootColourPartial FX FY X Y v).w U Z ≤ (fullHardCoupling h choice).w U Z :=
  (fullHardPartial_dominate_plan h choice 1 U Z).trans (fullHardCoupling_dominate_partial h choice U Z)

theorem fullHardCoupling_dominate_reverseRoot [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (U Z : V → C) :
    (reverseRootColourPartial FX FY X Y v).w U Z ≤ (fullHardCoupling h choice).w U Z :=
  (fullHardPartial_dominate_plan h choice 2 U Z).trans (fullHardCoupling_dominate_partial h choice U Z)


end
end CI2ZF.Appendix.CV
