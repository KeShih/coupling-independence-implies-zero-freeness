import CI2ZF.Appendix.CV.RegularCost
import CI2ZF.Appendix.CV.RootCost
import CI2ZF.Appendix.CV.MoveClassification

/-! The true residual support is partitioned by colour. Consequently
the common matching's entire completion charge is the sum of the local
baseline charges, with zero holding contribution. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]
local instance cvBaselinePartitionConfigDecEq : DecidableEq (V → C) := Classical.decEq _

def baselineRootRows (FX FY : HardListInstance V C) (X Y : V → C) (v : V) :
    Finset (V → C) :=
  insert (flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v))
    (rootColourOffRows FX FY X Y v)

lemma rootColourOffRows_not_regular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (_hcb : c ≠ b)
    {U : V → C} (hU : U ∈ rootColourOffRows FX FY X Y v) :
    U ∉ regularMoveRows FX X v b c := by
  have hr := (Finset.mem_filter.mp hU).2
  obtain ⟨u, hu, hmove⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hU).1
  have hXu : X u = a := (h.agree_off_root u (rootNeighbour_ne_root hu)).trans
    ((mem_rootNeighbours.mp hu).2.trans h.X_root)
  intro hm
  rcases (mem_regularMoveRows FX X v b c U).mp hm with heq | ⟨w, hw, heq⟩
  · have he := congrFun heq v
    rw [flipConfiguration_at_start, hr, h.X_root] at he
    exact hca he.symm
  · have heq' : flipConfiguration X (flipSet FX.graph X u b) (X u) b =
        flipConfiguration X (flipSet FX.graph X w b) (X w) b := by
      simpa only [h.Y_root] using hmove.trans heq
    exact hca (component_move_colour_unique FX.graph X u w b a c hXu
      (mem_rootNeighbours.mp hw).2 h.colours_ne heq').symm

lemma baselineRootRows_disjoint_regular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    Disjoint (baselineRootRows FX FY X Y v) (regularMoveRows FX X v b c) := by
  apply Finset.disjoint_left.mpr
  intro U hU hreg
  rcases Finset.mem_insert.mp hU with rfl | hoff
  · exact oppositeRootMove_not_regular h hca hcb (by simpa only [h.Y_root] using hreg)
  · exact rootColourOffRows_not_regular h hca hcb hoff hreg

lemma baselineRootRows_disjoint_allRegular
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    Disjoint (baselineRootRows FX FY X Y v) (allRegularRows FX X v a b) := by
  apply Finset.disjoint_left.mpr
  intro U hU hreg
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hreg
  exact Finset.disjoint_left.mp
    (baselineRootRows_disjoint_regular h c.property.1 c.property.2) hU hc

/-- Every nonzero residual move-size term belongs to exactly one colour
block. This is derived from the concrete transition support. -/
theorem common_left_baseline_support
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U : V → C)
    (hU : U ∉ baselineRootRows FX FY X Y v ∪ allRegularRows FX X v a b) :
    (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U = 0 := by
  by_cases heq : U = X
  · simp [heq, ham_self]
  by_cases hz : (hardCommonOffRootPartial FX FY X Y v).leftResidual U = 0
  · rw [hz, zero_mul]
  have hp := lt_of_le_of_ne
    ((hardCommonOffRootPartial FX FY X Y v).leftResidual_nonneg U) (Ne.symm hz)
  exfalso
  apply hU
  rcases hardCommon_residual_exhaustion h U heq hp with
    ⟨c, hca, hout⟩ | ⟨c, u, hcb, hu, hout, hv⟩
  · by_cases hcb : c = b
    · apply Finset.mem_union_left
      apply Finset.mem_insert.mpr
      left
      simpa only [h.Y_root, hcb] using hout
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨⟨c, hca, hcb⟩, Finset.mem_univ _,
        (mem_regularMoveRows FX X v b c U).mpr (Or.inl hout)⟩
  · by_cases hca : c = a
    · apply Finset.mem_union_left
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_image.mpr
        refine ⟨u, ?_, ?_⟩
        · simpa only [h.X_root, hca] using hu
        · simpa only [h.Y_root] using hout.symm
      · rw [hout, flipConfiguration_of_not_mem hv]
    · apply Finset.mem_union_right
      have huX : u ∈ rootNeighbours FX X v c := (h.rootNeighbours_eq hca hcb).symm ▸ hu
      exact Finset.mem_biUnion.mpr ⟨⟨c, hca, hcb⟩, Finset.mem_univ _,
        (mem_regularMoveRows FX X v b c U).mpr (Or.inr ⟨u, huX, hout⟩)⟩

lemma rootColourOffRows_common_leftResidual
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {U : V → C}
    (hU : U ∈ rootColourOffRows FX FY X Y v) :
    (hardCommonOffRootPartial FX FY X Y v).leftResidual U = (hardStep FX X).w U := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hU).1
  have hbad := regular_piece_inverse_improper h.symm u hu
  rw [h.Y_root]
  unfold PartialCoupling.leftResidual
  simp only [hardCommonOffRoot_row_zero_of_improper FX FY X Y v h.properY _ hbad,
    Finset.sum_const_zero, sub_zero]

lemma rootMove_not_rootColourOffRows
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v) ∉
      rootColourOffRows FX FY X Y v := by
  intro hm
  have he := (Finset.mem_filter.mp hm).2
  rw [flipConfiguration_at_start, h.X_root, h.Y_root] at he
  exact h.colours_ne he.symm

lemma baselineRootRows_sum
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (∑ U ∈ baselineRootRows FX FY X Y v,
      (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) =
      rootColourOffCharge FX FY X Y v / ((Fintype.card V : ℝ) * Fintype.card C) +
        ham X (flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v)) *
          (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v)) := by
  rw [baselineRootRows, Finset.sum_insert (rootMove_not_rootColourOffRows h)]
  have hr := regular_root_common_leftResidual h (c := Y v)
    (by rw [h.Y_root]; exact h.colours_ne.symm)
  rw [hr]
  have hs : (∑ U ∈ rootColourOffRows FX FY X Y v,
      (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) =
      rootColourOffCharge FX FY X Y v / ((Fintype.card V : ℝ) * Fintype.card C) := by
    rw [rootColourOffCharge, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro U hU
    rw [rootColourOffRows_common_leftResidual h hU]
    have hN : ((Fintype.card V : ℝ) * Fintype.card C) ≠ 0 := by positivity
    field_simp
  rw [hs]
  ring

theorem common_left_baseline_partition
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (∑ U, (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) =
      (∑ c : RegularColour a b, ∑ U ∈ regularMoveRows FX X v b c.val,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      rootColourOffCharge FX FY X Y v / ((Fintype.card V : ℝ) * Fintype.card C) +
        ham X (flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v)) *
          (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v)) := by
  have hs : (∑ U, (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) =
      ∑ U ∈ baselineRootRows FX FY X Y v ∪ allRegularRows FX X v a b,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro U _ hU
    exact common_left_baseline_support h U hU
  rw [hs, Finset.sum_union (baselineRootRows_disjoint_allRegular h), baselineRootRows_sum h]
  have hdis : (↑(Finset.univ : Finset (RegularColour a b)) : Set (RegularColour a b)).PairwiseDisjoint
      (fun c => regularMoveRows FX X v b c.val) := by
    intro c _ d _ hcd
    exact regularMoveRows_disjoint h c.property.1 c.property.2 d.property.1 d.property.2
      (fun he => hcd (Subtype.ext he))
  rw [allRegularRows, Finset.sum_biUnion hdis]
  ring

lemma common_rightResidual_eq_swapped_left
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).rightResidual Z =
      (hardCommonOffRootPartial FY FX Y X v).leftResidual Z := by
  unfold PartialCoupling.rightResidual PartialCoupling.leftResidual
  simp only [hardCommonOffRoot_transpose_w h]

lemma sum_regularColour_swap (a b : C) (f : C → ℝ) :
    (∑ c : RegularColour b a, f c.val) = ∑ c : RegularColour a b, f c.val := by
  let e : RegularColour b a ≃ RegularColour a b :=
    { toFun := fun c => ⟨c.val, c.property.2, c.property.1⟩
      invFun := fun c => ⟨c.val, c.property.2, c.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem common_right_baseline_partition
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (∑ Z, (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) =
      (∑ c : RegularColour a b, ∑ Z ∈ regularMoveRows FY Y v a c.val,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) +
      rootColourOffCharge FY FX Y X v / ((Fintype.card V : ℝ) * Fintype.card C) +
        ham Y (flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)) *
          (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)) := by
  simp only [common_rightResidual_eq_swapped_left h]
  rw [common_left_baseline_partition h.symm]
  congr 2
  exact sum_regularColour_swap a b (fun c => ∑ Z ∈ regularMoveRows FY Y v a c,
    (hardCommonOffRootPartial FY FX Y X v).leftResidual Z * ham Y Z)

/-- Every pair in the common matching still differs at exactly the root,
so this part of the actual coupling has zero signed drift cost. -/
theorem hardCommonOffRoot_cost_hamDrift
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (hardCommonOffRootPartial FX FY X Y v).cost hamDrift = 0 := by
  have hz (U Z : V → C) :
      (hardCommonOffRootPartial FX FY X Y v).w U Z * hamDrift U Z = 0 := by
    by_cases hm : U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
    · have heq : (Finset.univ.filter fun w => U w ≠ replaceRoot U v (Y v) w) = {v} := by
        ext w
        by_cases hw : w = v
        · subst w
          simp [hm.1, h.X_root, h.Y_root, h.colours_ne]
        · simp [hw, replaceRoot_off_root _ _ _ _ hw]
      have hd : ham U Z = 1 := by
        rw [hm.2.2]
        simp [ham, hamCard, heq]
      simp only [hamDrift, hd, sub_self, mul_zero]
    · have hw : (hardCommonOffRootPartial FX FY X Y v).w U Z = 0 := if_neg hm
      rw [hw, zero_mul]
  simp only [PartialCoupling.cost, hz, Finset.sum_const_zero]

/-- Complete baseline accounting for the concrete hard transition rows.
The common component matches have zero drift; all remaining move-size
charges are exactly the regular blocks and the two root-colour baselines. -/
theorem common_hamCompletionCharge_partition
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y =
      (∑ c : RegularColour a b, regularBaseline FX FY X Y v c.val) +
        rootBaseline FX FY X Y v + rootBaseline FY FX Y X v := by
  rw [hamCompletionCharge, PartialCoupling.completionCharge_eq,
    hardCommonOffRoot_cost_hamDrift h, zero_add,
    common_left_baseline_partition h, common_right_baseline_partition h]
  simp only [regularBaseline, rootBaseline, h.X_root, h.Y_root, Finset.sum_add_distrib]
  ring

end
end CI2ZF.Appendix.CV
