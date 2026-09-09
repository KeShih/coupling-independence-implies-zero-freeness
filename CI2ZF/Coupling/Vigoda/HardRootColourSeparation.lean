import CI2ZF.Coupling.Vigoda.HardRootColours
import CI2ZF.Coupling.Vigoda.HardGlobalRegular

/-! Both prescribed root-colour plans and all regular-colour plans fit in
one actual partial coupling. The row/column separation is proved on their
concrete output colourings. -/
namespace CI2ZF
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]
local instance : DecidableEq (V → C) := Classical.decEq _

def PartialCoupling.transpose {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (κ : PartialCoupling μ ν) : PartialCoupling ν μ where
  w y x := κ.w x y
  nonneg y x := κ.nonneg x y
  row_le := κ.col_le
  col_le := κ.row_le

lemma common_condition_reverse (X Y U Z : V → C) (v : V)
    (hagree : ∀ w, w ≠ v → X w = Y w)
    (hm : U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)) :
    Z v = Y v ∧ Z ≠ Y ∧ U = replaceRoot Z v (X v) := by
  have hinv : U = replaceRoot Z v (X v) := by
    rw [hm.2.2, replaceRoot_inverse U v (X v) (Y v) hm.1]
  refine ⟨by rw [hm.2.2, replaceRoot_at_root], ?_, hinv⟩
  intro hZY
  apply hm.2.1
  rw [hinv, hZY]
  exact replaceRoot_eq_of_agree_off_root Y X v (fun w hw => (hagree w hw).symm)

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

lemma rootColourPartner_not_regular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    rootColourPartner FX FY X Y v ∉ regularMoveRows FX X v b c := by
  intro hm
  rcases (mem_regularMoveRows FX X v b c _).mp hm with heq | ⟨w, hw, heq⟩
  · have hr := congrFun heq v
    rw [rootColourPartner_root, flipConfiguration_at_start, h.X_root] at hr
    exact hca hr.symm
  · by_cases hp : rootColourCanPair FX FY X Y v
    · have hu := hp.choose_spec
      have hn : rootNeighbours FY Y v a = {hp.choose} := by simpa only [h.X_root] using hu.1
      have huN : hp.choose ∈ rootNeighbours FY Y v a := hn.symm ▸ Finset.mem_singleton_self _
      have hXu : X hp.choose = a := (h.agree_off_root _ (rootNeighbour_ne_root huN)).trans
        (mem_rootNeighbours.mp huN).2
      have heq' : flipConfiguration X (flipSet FX.graph X hp.choose b) (X hp.choose) b =
          flipConfiguration X (flipSet FX.graph X w b) (X w) b := by
        simpa only [rootColourPartner, dif_pos hp, h.Y_root] using heq
      exact hca (component_move_colour_unique FX.graph X hp.choose w b a c hXu
        (mem_rootNeighbours.mp hw).2 h.colours_ne heq').symm
    · have heq' : X = flipConfiguration X (flipSet FX.graph X w b) (X w) b := by
        simpa only [rootColourPartner, dif_neg hp] using heq
      have hc := congrFun heq' w
      rw [flipConfiguration_at_start, (mem_rootNeighbours.mp hw).2] at hc
      exact hcb hc

lemma oppositeRootMove_not_regular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    flipConfiguration X (flipSet FX.graph X v b) (X v) b ∉ regularMoveRows FX X v b c := by
  intro hm
  rcases (mem_regularMoveRows FX X v b c _).mp hm with heq | ⟨w, hw, heq⟩
  · have hr := congrFun heq v
    simp only [flipConfiguration_at_start] at hr
    exact hcb hr.symm
  · have hwY : w ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ hw
    have hnot := regular_piece_no_root h.symm hca w hwY
    have hr := congrFun heq v
    rw [flipConfiguration_at_start, flipConfiguration_of_not_mem hnot, h.X_root] at hr
    exact h.colours_ne hr.symm

def allRegularRows (F : HardListInstance V C) (X : V → C) (v : V) (a b : C) : Finset (V → C) :=
  Finset.univ.biUnion fun c : RegularColour a b => regularMoveRows F X v b c.val

lemma rootColourPartner_not_allRegular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    rootColourPartner FX FY X Y v ∉ allRegularRows FX X v a b := by
  simp only [allRegularRows, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
  intro c
  exact rootColourPartner_not_regular h c.property.1 c.property.2

lemma oppositeRootMove_not_allRegular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    flipConfiguration X (flipSet FX.graph X v b) (X v) b ∉ allRegularRows FX X v a b := by
  simp only [allRegularRows, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
  intro c
  exact oppositeRootMove_not_regular h c.property.1 c.property.2

lemma globalRegularPartial_ge_common [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ (globalRegularPartial h).w U Z := by
  change _ ≤ _ + ∑ c : RegularColour a b, _
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun c _ => sub_nonneg.mpr (selectedRegularPartial_ge_common FX FY X Y v c U Z)

lemma globalRegularPartial_eq_common_off_allRows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C)
    (hU : U ∉ allRegularRows FX X v a b) :
    (globalRegularPartial h).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  have hz (c : RegularColour a b) : (selectedRegularPartial FX FY X Y v c).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z :=
    selectedRegularPartial_eq_common_off_rows h c.property.1 c.property.2 U Z
      (fun hm => hU (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hm⟩))
  change _ + (∑ c : RegularColour a b, _) = _
  simp only [hz, sub_self, Finset.sum_const_zero, add_zero]

lemma globalRegularPartial_eq_common_off_allCols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C)
    (hZ : Z ∉ allRegularRows FY Y v b a) :
    (globalRegularPartial h).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  have hz (c : RegularColour a b) : (selectedRegularPartial FX FY X Y v c).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z :=
    selectedRegularPartial_eq_common_off_cols h c.property.1 c.property.2 U Z
      (fun hm => hZ (Finset.mem_biUnion.mpr
        ⟨⟨c.val, c.property.2, c.property.1⟩, Finset.mem_univ _, hm⟩))
  change _ + (∑ c : RegularColour a b, _) = _
  simp only [hz, sub_self, Finset.sum_const_zero, add_zero]

def fullColourPlans [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) : Fin 3 → PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  ![globalRegularPartial h, rootColourPartial FX FY X Y v, reverseRootColourPartial FX FY X Y v]

def fullColourRows {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (_h : RootLocalPair FX FY X Y v a b) : Fin 3 → Finset (V → C) :=
  ![allRegularRows FX X v a b, {rootColourPartner FX FY X Y v},
    {flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v)}]

def fullColourCols {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (_h : RootLocalPair FX FY X Y v a b) : Fin 3 → Finset (V → C) :=
  ![allRegularRows FY Y v b a,
    {flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)}, {rootColourPartner FY FX Y X v}]

lemma fullColourPlans_ge_common [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (k : Fin 3) (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤ (fullColourPlans h k).w U Z := by
  fin_cases k
  · exact globalRegularPartial_ge_common h U Z
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
    (h : RootLocalPair FX FY X Y v a b) (k : Fin 3) (U Z : V → C)
    (hU : U ∉ fullColourRows h k) :
    (fullColourPlans h k).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  fin_cases k
  · exact globalRegularPartial_eq_common_off_allRows h U Z hU
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
    (h : RootLocalPair FX FY X Y v a b) (k : Fin 3) (U Z : V → C)
    (hZ : Z ∉ fullColourCols h k) :
    (fullColourPlans h k).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  fin_cases k
  · exact globalRegularPartial_eq_common_off_allCols h U Z hZ
  · have hne : Z ≠ flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v) := by
      simpa [fullColourCols] using hZ
    change (rootColourPartial FX FY X Y v).w U Z = _
    rw [rootColourPartial_full h]
    simp [hne]
  · have hne : Z ≠ rootColourPartner FY FX Y X v := by simpa [fullColourCols] using hZ
    change (reverseRootColourPartial FX FY X Y v).w U Z = _
    rw [reverseRootColourPartial_full h]
    simp [hne]

lemma fullColourRows_disjoint {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (h : RootLocalPair FX FY X Y v a b) (k l : Fin 3) (hkl : k ≠ l) :
    Disjoint (fullColourRows h k) (fullColourRows h l) := by
  have h0 := rootColourPartner_not_allRegular h
  have h1 := oppositeRootMove_not_allRegular h
  have h01 : rootColourPartner FX FY X Y v ≠
      flipConfiguration X (flipSet FX.graph X v b) (X v) b := by
    intro heq
    have hr := congrFun heq v
    rw [rootColourPartner_root, flipConfiguration_at_start, h.X_root] at hr
    exact h.colours_ne hr
  fin_cases k <;> fin_cases l <;> norm_num at hkl
  all_goals simp [fullColourRows, h.Y_root, h0, h1, h01, Ne.symm h01]

lemma fullColourCols_disjoint {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (h : RootLocalPair FX FY X Y v a b) (k l : Fin 3) (hkl : k ≠ l) :
    Disjoint (fullColourCols h k) (fullColourCols h l) := by
  have h0 := oppositeRootMove_not_allRegular h.symm
  have h1 := rootColourPartner_not_allRegular h.symm
  have h01 : flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a ≠
      rootColourPartner FY FX Y X v := by
    intro heq
    have hr := congrFun heq v
    rw [flipConfiguration_at_start, rootColourPartner_root, h.Y_root] at hr
    exact h.colours_ne hr
  fin_cases k <;> fin_cases l <;> norm_num at hkl
  all_goals simp [fullColourCols, h.X_root, h0, h1, h01, Ne.symm h01]

/-- All regular and both root-colour allocations coexist inside the actual
hard transition marginals. No capacity or support hypothesis is supplied. -/
def fullHardPartial [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) : PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  PartialCoupling.combineDisjoint (hardCommonOffRootPartial FX FY X Y v)
    (fullColourPlans h) (fullColourRows h) (fullColourCols h)
    (fullColourPlans_ge_common h) (fullColourPlans_eq_common_off_rows h)
    (fullColourPlans_eq_common_off_cols h) (fullColourRows_disjoint h) (fullColourCols_disjoint h)

def fullHardCoupling [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) : Coupling (hardStep FX X) (hardStep FY Y) :=
  (fullHardPartial h).complete

theorem fullHardPartial_w [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C) :
    (fullHardPartial h).w U Z = (globalRegularPartial h).w U Z +
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

end
end CI2ZF
