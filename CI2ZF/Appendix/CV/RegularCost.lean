import CI2ZF.Appendix.CV.GlobalCoupling
import CI2ZF.Appendix.CV.PieceSums
import CI2ZF.Appendix.CV.SingletonRegular
import CI2ZF.Appendix.CV.ComponentCharge
import CI2ZF.HardRegularCost

/-! Local charge accounting of every actual CV colour plan, preserving the
canonical residual savings in the global coupling's completion charge. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvRegularCostDecEq : DecidableEq (V → C) := Classical.decEq _

namespace CanonicalMatching
lemma charge_extend {I S T : Type*} [Fintype I] [Fintype S] [Fintype T]
    {mu : FinDist S} {nu : FinDist T} (κ : PartialCoupling mu nu) (f : I → S) (g : I → T)
    (d : S → T → ℝ) (a : S → ℝ) (b : T → ℝ) :
    (extend κ f g).completionCharge d a b = κ.completionCharge d a b +
      ∑ i, atIncidence f g κ.leftResidual κ.rightResidual i * (d (f i) (g i) - a (f i) - b (g i)) := by
  unfold PartialCoupling.completionCharge
  rw [extend_cost]
  ring
end CanonicalMatching

def regularBaseline [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) : ℝ :=
  (∑ U ∈ regularMoveRows FX X v (Y v) c,
    (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
  ∑ Z ∈ regularMoveRows FY Y v (X v) c,
    (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z

/-- The common plan carries zero signed drift, including all common moves. -/
theorem hardCommon_cost_hamDrift [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (hardCommonOffRootPartial FX FY X Y v).cost hamDrift = 0 := by
  unfold PartialCoupling.cost hardCommonOffRootPartial commonOffRootPartial
  apply Finset.sum_eq_zero
  intro U _
  apply Finset.sum_eq_zero
  intro Z _
  dsimp only
  split_ifs with hp
  · have hne : U v ≠ Y v := by rw [hp.1, h.X_root, h.Y_root]; exact h.colours_ne
    rw [hp.2.2]
    unfold hamDrift
    rw [ham_replaceRoot_eq_one U v (Y v) hne, sub_self, mul_zero]
  · exact zero_mul _

/-- All incidence savings in the scalar certificate survive in the true
state-level partial plan, with the exact proposal normalization. -/
theorem regularColour_incidence_charge_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b) :
    hamCompletionCharge (canonicalRegularPartial FX FY X Y v c
      (choice.left c) (choice.right c)) X Y ≤
    hamCompletionCharge (selectedRootPlan h choice c) X Y -
      (∑ i, CanonicalMatching.atIncidence (componentOf FX X v c) (oppositeComponentOf h hca hcb)
        (fun S => componentResidual FX X v c (choice.left c) S.val) (fun S => componentResidual FY Y v c (choice.right c) S.val) i) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hcharge := CanonicalMatching.charge_extend
    (selectedRootPlan h choice c) (regularIncidenceLeft FX X Y v c)
    (regularIncidenceRight FX FY X Y v c) hamDrift (ham X) (ham Y)
  change hamCompletionCharge (CanonicalMatching.extend (selectedRootPlan h choice c)
    (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)) X Y ≤ _
  unfold hamCompletionCharge
  rw [hcharge]
  have hsum : (∑ i, CanonicalMatching.atIncidence
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan h choice c).leftResidual (selectedRootPlan h choice c).rightResidual i *
      hamDefect X Y (regularIncidenceLeft FX X Y v c i) (regularIncidenceRight FX FY X Y v c i)) ≤
    - (∑ i, CanonicalMatching.atIncidence
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan h choice c).leftResidual (selectedRootPlan h choice c).rightResidual i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hn := CanonicalMatching.atIncidence_nonneg
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan h choice c).leftResidual (selectedRootPlan h choice c).rightResidual
      (PartialCoupling.leftResidual_nonneg _) (PartialCoupling.rightResidual_nonneg _) i
    simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left
      (regularIncidence_defect_le h hca hcb i) hn
  simp_rw [selectedIncidence_atIncidence h choice hca hcb] at hsum
  rw [← Finset.sum_div] at hsum
  change _ + (∑ i, _ * hamDefect X Y _ _) ≤ _
  simp_rw [selectedIncidence_atIncidence h choice hca hcb]
  linarith

/-- The two selected root/piece matches realize precisely the two scalar
root charges, including their true proposal normalization. -/
theorem selectedRootPlan_cost [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (selectedRootPlan h choice c).cost hamDrift =
      (rootCharge FX X v c (choice.left c) + rootCharge FY Y v c (choice.right c)) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := choice.left_mem c hN
  have hw := choice.right_mem c hNY
  have hcost := PartialCoupling.cost_eq_add_of_w_eq
    (hardCommonOffRootPartial FX FY X Y v) (selectedRootPlan h choice c)
    _ (fun U Z => by simpa only [add_assoc] using regularRootPartial_full h hca hcb _ _ hu hw U Z)
    hamDrift
  rw [hardCommon_cost_hamDrift h, zero_add] at hcost
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, ite_and] at hcost
  simp at hcost
  rw [hcost, regular_root_match_drift h hca hcb _ hu]
  have hsym := regular_root_match_drift h.symm hcb hca _ hw
  rw [hamDrift, ham_comm] at hsym
  change hamDrift _ _ = _ at hsym
  rw [hsym, hardStep_rootRate FX X h.properX v c (by rwa [h.X_root]),
    hardStep_rootRate FY Y h.properY v c (by rwa [h.Y_root])]
  simp only [rootCharge, h.X_root, h.Y_root]
  ring

lemma selectedRootPlan_root_leftResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (selectedRootPlan h choice c).leftResidual
      (flipConfiguration X (flipSet FX.graph X v c) (X v) c) = 0 := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := choice.left_mem c hN
  have hw := choice.right_mem c hNY
  have hne : flipConfiguration X (flipSet FX.graph X v c) (X v) c ≠
      flipConfiguration X (flipSet FX.graph X (choice.right c) b)
        (X (choice.right c)) b := by
    intro heq
    have hv := congrFun heq v
    rw [flipConfiguration_at_start,
      flipConfiguration_of_not_mem (regular_piece_no_root h.symm hca _ hw), h.X_root] at hv
    exact hca hv
  rw [regularRootPartial_leftResidual h hca hcb _ _ hu hw,
    regular_root_common_leftResidual h hca, if_pos rfl, if_neg hne]
  ring

lemma selectedRootPlan_root_rightResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (selectedRootPlan h choice c).rightResidual
      (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) = 0 := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := choice.left_mem c hN
  have hw := choice.right_mem c hNY
  have hne : flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c ≠
      flipConfiguration Y (flipSet FY.graph Y (choice.left c) a)
        (Y (choice.left c)) a := by
    intro heq
    have hv := congrFun heq v
    rw [flipConfiguration_at_start,
      flipConfiguration_of_not_mem (regular_piece_no_root h hcb _ hu), h.Y_root] at hv
    exact hcb hv
  rw [regularRootPartial_rightResidual h hca hcb _ _ hu hw,
    regular_root_common_rightResidual h hcb, if_neg hne, if_pos rfl]
  ring

theorem selectedRootPlan_rows_sum [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (∑ U ∈ regularMoveRows FX X v b c,
      (selectedRootPlan h choice c).leftResidual U * ham X U) =
    (∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * componentResidual FY Y v c (choice.right c) S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [regularMoveRows_eq_incidenceLeft h]
  have hz := selectedRootPlan_root_leftResidual h choice hca hcb hN
  by_cases hm : flipConfiguration X (flipSet FX.graph X v c) (X v) c ∈
      Finset.univ.image (regularIncidenceLeft FX X Y v c)
  · rw [Finset.insert_eq_of_mem hm]
    simpa only [mul_comm] using regularIncidenceLeft_weightedResidual_sum h choice hca hcb
  · rw [Finset.sum_insert hm, hz, zero_mul, zero_add]
    simpa only [mul_comm] using regularIncidenceLeft_weightedResidual_sum h choice hca hcb

theorem selectedRootPlan_cols_sum [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (∑ Z ∈ regularMoveRows FY Y v a c,
      (selectedRootPlan h choice c).rightResidual Z * ham Y Z) =
    (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * componentResidual FX X v c (choice.left c) S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [regularMoveRows_eq_incidenceRight h hca hcb]
  have hz := selectedRootPlan_root_rightResidual h choice hca hcb hN
  by_cases hm : flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c ∈
      Finset.univ.image (regularIncidenceRight FX FY X Y v c)
  · rw [Finset.insert_eq_of_mem hm]
    simpa only [mul_comm] using regularIncidenceRight_weightedResidual_sum h choice hca hcb
  · rw [Finset.sum_insert hm, hz, zero_mul, zero_add]
    simpa only [mul_comm] using regularIncidenceRight_weightedResidual_sum h choice hca hcb

/-- The selected root plan's charge increment plus its affected baseline
is exactly the scalar root charges and remaining piece-size charges. -/
theorem selectedRootPlan_local_charge [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    hamCompletionCharge (selectedRootPlan h choice c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) =
      (rootCharge FX X v c (choice.left c) + rootCharge FY Y v c (choice.right c) +
        (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * componentResidual FX X v c (choice.left c) S.val) +
        ∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * componentResidual FY Y v c (choice.right c) S.val) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := choice.left_mem c hN
  have hw := choice.right_mem c hNY
  have heq := PartialCoupling.charge_localize
    (hardCommonOffRootPartial FX FY X Y v) (selectedRootPlan h choice c)
    (regularMoveRows FX X v b c) (regularMoveRows FY Y v a c) hamDrift (ham X) (ham Y)
    (fun U hU => by
      unfold PartialCoupling.leftResidual
      simp_rw [regularRootPartial_eq_common_off_rows h hca hcb _ _ hu hw U _ hU])
    (fun Z hZ => by
      unfold PartialCoupling.rightResidual
      simp_rw [regularRootPartial_eq_common_off_cols h hca hcb _ _ hu hw _ Z hZ])
  unfold hamCompletionCharge
  rw [heq, hardCommon_cost_hamDrift h, sub_zero, selectedRootPlan_cost h choice hca hcb hN,
    selectedRootPlan_rows_sum h choice hca hcb hN, selectedRootPlan_cols_sum h choice hca hcb hN]
  ring

/-- The complete nonempty regular group has at most the paper's exact
per-colour charge, with no supplied capacity or drift hypothesis. -/
theorem regularColour_local_charge_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    hamCompletionCharge (selectedRegularPartial h choice c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) ≤
      canonicalColourCharge h hca hcb (choice.left c) (choice.right c) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hb := selectedRootPlan_local_charge h choice hca hcb hN
  have hs := regularColour_incidence_charge_le h choice hca hcb
  rw [selectedRegularPartial, if_pos hN]
  simp only [canonicalColourCharge, if_pos hN, canonicalOffRootCharge, add_div, sub_div]
  simp only [add_div] at hb
  linarith

/-- A colour absent at the neighbours gives the exact negative singleton
charge after its two separate root-move charges are cancelled. -/
theorem singletonColour_local_charge [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : rootNeighbours FX X v c = ∅) :
    hamCompletionCharge (selectedRegularPartial h choice c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) =
      canonicalColourCharge h hca hcb (choice.left c) (choice.right c) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hNY : rootNeighbours FY Y v c = ∅ := (h.rootNeighbours_eq hca hcb).symm.trans hN
  have hL : ham X (flipConfiguration X (flipSet FX.graph X v c) (X v) c) = 1 := by
    rw [ham_comm, ham_flip_eq_card (by rwa [h.X_root]),
      root_flipSet_singleton_of_no_neighbours FX X v c (by rwa [h.X_root]) hN]
    simp
  have hR : ham Y (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) = 1 := by
    rw [ham_comm, ham_flip_eq_card (by rwa [h.Y_root]),
      root_flipSet_singleton_of_no_neighbours FY Y v c (by rwa [h.Y_root]) hNY]
    simp
  have hd : hamDrift (flipConfiguration X (flipSet FX.graph X v c) (X v) c)
      (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) = -1 := by
    rw [hamDrift, singleton_regular_coalesces h hca hcb hN, ham_self]
    norm_num
  have hc := PartialCoupling.charge_eq_add_point
    (hardCommonOffRootPartial FX FY X Y v) (selectedRegularPartial h choice c)
    _ _ _ (singletonRegularPartial_full h choice hca hcb hN) hamDrift (ham X) (ham Y)
  rw [hd, hL, hR] at hc
  have hm := singleton_regular_mass h hca hcb hN
  simp only [regularMoveRows, hN, hNY, Finset.image_empty, Finset.insert_empty,
    Finset.sum_singleton, regular_root_common_leftResidual h hca,
    regular_root_common_rightResidual h hcb, hL, hR, hm.1, hm.2, mul_one]
  unfold hamCompletionCharge
  rw [hc]
  simp only [canonicalColourCharge, hN, Finset.not_nonempty_empty, if_false, neg_div]
  ring

/-- Every actual selected regular-colour plan satisfies the scalar charge
bound, including colours with no incident neighbour. -/
theorem selectedRegular_local_charge_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b) :
    hamCompletionCharge (selectedRegularPartial h choice c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) ≤
      canonicalColourCharge h hca hcb (choice.left c) (choice.right c) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  by_cases hN : (rootNeighbours FX X v c).Nonempty
  · exact regularColour_local_charge_le h choice hca hcb hN
  · exact (singletonColour_local_charge h choice hca hcb (Finset.not_nonempty_iff_eq_empty.mp hN)).le

theorem selectedRegular_charge_baseline_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b) :
    hamCompletionCharge (selectedRegularPartial h choice c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      regularBaseline FX FY X Y v c ≤
      canonicalColourCharge h hca hcb (choice.left c) (choice.right c) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  simpa only [regularBaseline, h.X_root, h.Y_root] using
    selectedRegular_local_charge_le h choice hca hcb


end
end CI2ZF.Appendix.CV
