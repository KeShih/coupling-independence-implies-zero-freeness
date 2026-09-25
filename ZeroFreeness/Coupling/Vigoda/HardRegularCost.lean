import ZeroFreeness.Coupling.Vigoda.HardGlobalCost
import ZeroFreeness.Coupling.Vigoda.HardIncidenceRates
import ZeroFreeness.Coupling.Vigoda.HardPieceSums
import ZeroFreeness.Coupling.Vigoda.HardSingletonRegular
import ZeroFreeness.Coupling.Vigoda.HardBaselineData

/-! Exact root-match costs and actual incidence savings for regular colours. -/
namespace ZeroFreeness

open PottsCI PottsCI.FinDist PottsCI.Vigoda RootComponentGeometry RegularColourCharge
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C]
local instance hardRegularCostConfigDecEq : DecidableEq (V → C) := Classical.decEq _
set_option linter.unusedSectionVars false

lemma ham_replaceRoot_eq_one (U : V → C) (v : V) (b : C) (h : U v ≠ b) :
    ham U (replaceRoot U v b) = 1 := by
  have heq : (Finset.univ.filter fun w => U w ≠ replaceRoot U v b w) = {v} := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [h]
    · simp [replaceRoot_off_root U v b w hw, hw]
  simp [ham, hamCard, heq]

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

/-- The exact signed drift of the first actual regular root/piece match. -/
theorem regular_root_match_drift
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    hamDrift
      (flipConfiguration X (flipSet FX.graph X v c) (X v) c)
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) =
      ((flipSet FX.graph X v c).card : ℝ) -
        (offRootComponent FX X v a c u).card - 1 := by
  have hYu : Y u = c := (h.agree_off_root u (rootNeighbour_ne_root hu)).symm.trans
    (mem_rootNeighbours.mp hu).2
  have hswap : flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a =
      flipConfiguration Y (flipSet FY.graph Y u a) a c := by
    rw [hYu]
    apply flipConfiguration_swap_colours hca
    intro w hw
    simpa only [hYu] using colour_eq_of_mem_flipSet hw
  have hsub : flipSet FY.graph Y u a ⊆ flipSet FX.graph X v c := by
    rw [← h.offRootComponent_eq_opposite_flipSet hcb hu]
    apply root_piece_subset_root (by rwa [h.X_root])
    rw [← h.X_root]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have hham := root_offRoot_match_ham h.X_root h.Y_root hca.symm hcb.symm
    h.agree_off_root (self_mem_flipSet (G := FX.graph) (X := X) (u := v) (c := c))
    (regular_piece_no_root h hcb u hu) hsub
    (fun w hw => by simpa only [h.X_root] using colour_eq_of_mem_flipSet hw)
  unfold hamDrift
  rw [hswap, h.X_root, hham, ← h.offRootComponent_eq_opposite_flipSet hcb hu]

/-- Every actual incidence match saves at least one against separate moves. -/
theorem regularIncidence_defect_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    hamDefect X Y (regularIncidenceLeft FX X Y v c i)
      (regularIncidenceRight FX FY X Y v c i) ≤ -1 := by
  have hXu : X i.val = c := (mem_rootNeighbours.mp i.property).2
  have hYu : Y i.val = c := (h.agree_off_root i.val (rootNeighbour_ne_root i.property)).symm.trans hXu
  have hL : ham X (regularIncidenceLeft FX X Y v c i) =
      ((flipSet FX.graph X i.val (Y v)).card : ℝ) := by
    rw [ham_comm]
    exact ham_flip_eq_card (by rw [h.Y_root, hXu]; exact hcb.symm)
  have hR : ham Y (regularIncidenceRight FX FY X Y v c i) =
      ((flipSet FY.graph Y i.val (X v)).card : ℝ) := by
    rw [ham_comm]
    exact ham_flip_eq_card (by rw [h.X_root, hYu]; exact hca.symm)
  have hb := regularIncidence_ham_drift_le h i
  unfold hamDefect
  rw [hL, hR]
  linarith

/-- All incidence savings in the scalar certificate survive in the true
state-level partial plan, with the exact proposal normalization. -/
theorem regularColour_incidence_charge_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    hamCompletionCharge (regularColourPartial FX FY X Y v c
      (selectedRepresentative FX X v c) (selectedRepresentative FY Y v c)) X Y ≤
    hamCompletionCharge (selectedRootPlan FX FY X Y v c) X Y -
      (∑ i, IncidenceMatching.atIncidence (componentOf FX X v c) (oppositeComponentOf h hca hcb)
        (fun S => residual FX X v c S.val) (fun S => residual FY Y v c S.val) i) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hcharge := PartialCoupling.charge_matchResidualIncidences
    (selectedRootPlan FX FY X Y v c) (regularIncidenceLeft FX X Y v c)
    (regularIncidenceRight FX FY X Y v c) hamDrift (ham X) (ham Y)
  change hamCompletionCharge ((selectedRootPlan FX FY X Y v c).matchResidualIncidences
    (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)) X Y ≤ _
  unfold hamCompletionCharge
  rw [hcharge]
  have hsum : (∑ i, IncidenceMatching.atIncidence
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan FX FY X Y v c).leftResidual (selectedRootPlan FX FY X Y v c).rightResidual i *
      hamDefect X Y (regularIncidenceLeft FX X Y v c i) (regularIncidenceRight FX FY X Y v c i)) ≤
    - (∑ i, IncidenceMatching.atIncidence
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan FX FY X Y v c).leftResidual (selectedRootPlan FX FY X Y v c).rightResidual i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hn := IncidenceMatching.atIncidence_nonneg
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan FX FY X Y v c).leftResidual (selectedRootPlan FX FY X Y v c).rightResidual
      (PartialCoupling.leftResidual_nonneg _) (PartialCoupling.rightResidual_nonneg _) i
    simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left
      (regularIncidence_defect_le h hca hcb i) hn
  simp_rw [regularIncidence_atIncidence h hca hcb] at hsum
  rw [← Finset.sum_div] at hsum
  change _ + (∑ i, _ * hamDefect X Y _ _) ≤ _
  simp_rw [regularIncidence_atIncidence h hca hcb]
  linarith

/-- The two selected root/piece matches realize precisely the two scalar
root charges, including their true proposal normalization. -/
theorem selectedRootPlan_cost [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (selectedRootPlan FX FY X Y v c).cost hamDrift =
      (rootCharge FX X v c + rootCharge FY Y v c) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := selectedRepresentative_mem FX X v c hN
  have hw := selectedRepresentative_mem FY Y v c hNY
  have hcost := PartialCoupling.cost_eq_add_of_w_eq
    (hardCommonOffRootPartial FX FY X Y v) (selectedRootPlan FX FY X Y v c)
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
  simp only [rootCharge, largestPiece, h.X_root, h.Y_root]
  ring

lemma regularMoveRows_eq_incidenceLeft
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) :
    regularMoveRows FX X v b c = insert
      (flipConfiguration X (flipSet FX.graph X v c) (X v) c)
      (Finset.univ.image (regularIncidenceLeft FX X Y v c)) := by
  ext U
  simp only [regularMoveRows, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and, regularIncidenceLeft, h.Y_root]
  constructor
  · rintro (hU | ⟨u, hu, heq⟩)
    · exact Or.inl hU
    · exact Or.inr ⟨⟨u, hu⟩, heq⟩
  · rintro (hU | ⟨i, heq⟩)
    · exact Or.inl hU
    · exact Or.inr ⟨i.val, i.property, heq⟩

lemma regularMoveRows_eq_incidenceRight
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    regularMoveRows FY Y v a c = insert
      (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c)
      (Finset.univ.image (regularIncidenceRight FX FY X Y v c)) := by
  ext Z
  simp only [regularMoveRows, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and, regularIncidenceRight, h.X_root]
  constructor
  · rintro (hZ | ⟨u, hu, heq⟩)
    · exact Or.inl hZ
    · exact Or.inr ⟨⟨u, (h.rootNeighbours_eq hca hcb).symm ▸ hu⟩, heq⟩
  · rintro (hZ | ⟨i, heq⟩)
    · exact Or.inl hZ
    · exact Or.inr ⟨i.val, (h.rootNeighbours_eq hca hcb) ▸ i.property, heq⟩

lemma selectedRootPlan_root_leftResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (selectedRootPlan FX FY X Y v c).leftResidual
      (flipConfiguration X (flipSet FX.graph X v c) (X v) c) = 0 := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := selectedRepresentative_mem FX X v c hN
  have hw := selectedRepresentative_mem FY Y v c hNY
  have hne : flipConfiguration X (flipSet FX.graph X v c) (X v) c ≠
      flipConfiguration X (flipSet FX.graph X (selectedRepresentative FY Y v c) b)
        (X (selectedRepresentative FY Y v c)) b := by
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
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (selectedRootPlan FX FY X Y v c).rightResidual
      (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) = 0 := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := selectedRepresentative_mem FX X v c hN
  have hw := selectedRepresentative_mem FY Y v c hNY
  have hne : flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c ≠
      flipConfiguration Y (flipSet FY.graph Y (selectedRepresentative FX X v c) a)
        (Y (selectedRepresentative FX X v c)) a := by
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
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (∑ U ∈ regularMoveRows FX X v b c,
      (selectedRootPlan FX FY X Y v c).leftResidual U * ham X U) =
    (∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * residual FY Y v c S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [regularMoveRows_eq_incidenceLeft h]
  have hz := selectedRootPlan_root_leftResidual h hca hcb hN
  by_cases hm : flipConfiguration X (flipSet FX.graph X v c) (X v) c ∈
      Finset.univ.image (regularIncidenceLeft FX X Y v c)
  · rw [Finset.insert_eq_of_mem hm]
    simpa only [mul_comm] using regularIncidenceLeft_weightedResidual_sum h hca hcb
  · rw [Finset.sum_insert hm, hz, zero_mul, zero_add]
    simpa only [mul_comm] using regularIncidenceLeft_weightedResidual_sum h hca hcb

theorem selectedRootPlan_cols_sum [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    (∑ Z ∈ regularMoveRows FY Y v a c,
      (selectedRootPlan FX FY X Y v c).rightResidual Z * ham Y Z) =
    (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * residual FX X v c S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [regularMoveRows_eq_incidenceRight h hca hcb]
  have hz := selectedRootPlan_root_rightResidual h hca hcb hN
  by_cases hm : flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c ∈
      Finset.univ.image (regularIncidenceRight FX FY X Y v c)
  · rw [Finset.insert_eq_of_mem hm]
    simpa only [mul_comm] using regularIncidenceRight_weightedResidual_sum h hca hcb
  · rw [Finset.sum_insert hm, hz, zero_mul, zero_add]
    simpa only [mul_comm] using regularIncidenceRight_weightedResidual_sum h hca hcb

/-- The selected root plan's charge increment plus its affected baseline
is exactly the scalar root charges and remaining piece-size charges. -/
theorem selectedRootPlan_local_charge [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    hamCompletionCharge (selectedRootPlan FX FY X Y v c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) =
      (rootCharge FX X v c + rootCharge FY Y v c +
        (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * residual FX X v c S.val) +
        ∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * residual FY Y v c S.val) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have hu := selectedRepresentative_mem FX X v c hN
  have hw := selectedRepresentative_mem FY Y v c hNY
  have heq := PartialCoupling.charge_localize
    (hardCommonOffRootPartial FX FY X Y v) (selectedRootPlan FX FY X Y v c)
    (regularMoveRows FX X v b c) (regularMoveRows FY Y v a c) hamDrift (ham X) (ham Y)
    (fun U hU => by
      unfold PartialCoupling.leftResidual
      simp_rw [regularRootPartial_eq_common_off_rows h hca hcb _ _ hu hw U _ hU])
    (fun Z hZ => by
      unfold PartialCoupling.rightResidual
      simp_rw [regularRootPartial_eq_common_off_cols h hca hcb _ _ hu hw _ Z hZ])
  unfold hamCompletionCharge
  rw [heq, hardCommon_cost_hamDrift h, sub_zero, selectedRootPlan_cost h hca hcb hN,
    selectedRootPlan_rows_sum h hca hcb hN, selectedRootPlan_cols_sum h hca hcb hN]
  ring

/-- The complete nonempty regular group has at most the paper's exact
per-colour charge, with no supplied capacity or drift hypothesis. -/
theorem regularColour_local_charge_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : (rootNeighbours FX X v c).Nonempty) :
    hamCompletionCharge (selectedRegularPartial FX FY X Y v c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) ≤
      perColourCharge h hca hcb / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hb := selectedRootPlan_local_charge h hca hcb hN
  have hs := regularColour_incidence_charge_le h hca hcb
  rw [selectedRegularPartial, if_pos hN]
  simp only [perColourCharge, if_pos hN, offRootCharge, add_div, sub_div]
  simp only [add_div] at hb
  linarith

/-- A colour absent at the neighbours gives the exact negative singleton
charge after its two separate root-move charges are cancelled. -/
theorem singletonColour_local_charge [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : rootNeighbours FX X v c = ∅) :
    hamCompletionCharge (selectedRegularPartial FX FY X Y v c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) =
      perColourCharge h hca hcb / ((Fintype.card V : ℝ) * Fintype.card C) := by
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
    (hardCommonOffRootPartial FX FY X Y v) (selectedRegularPartial FX FY X Y v c)
    _ _ _ (singletonRegularPartial_full h hca hcb hN) hamDrift (ham X) (ham Y)
  rw [hd, hL, hR] at hc
  have hm := singleton_regular_mass h hca hcb hN
  simp only [regularMoveRows, hN, hNY, Finset.image_empty, Finset.insert_empty,
    Finset.sum_singleton, regular_root_common_leftResidual h hca,
    regular_root_common_rightResidual h hcb, hL, hR, hm.1, hm.2, mul_one]
  unfold hamCompletionCharge
  rw [hc]
  simp only [perColourCharge, hN, Finset.not_nonempty_empty, if_false, neg_div]
  ring

/-- Every actual selected regular-colour plan satisfies the scalar charge
bound, including colours with no incident neighbour. -/
theorem selectedRegular_local_charge_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    hamCompletionCharge (selectedRegularPartial FX FY X Y v c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ((∑ U ∈ regularMoveRows FX X v b c,
        (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
      ∑ Z ∈ regularMoveRows FY Y v a c,
        (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z) ≤
      perColourCharge h hca hcb / ((Fintype.card V : ℝ) * Fintype.card C) := by
  by_cases hN : (rootNeighbours FX X v c).Nonempty
  · exact regularColour_local_charge_le h hca hcb hN
  · exact (singletonColour_local_charge h hca hcb (Finset.not_nonempty_iff_eq_empty.mp hN)).le

theorem selectedRegular_charge_baseline_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    hamCompletionCharge (selectedRegularPartial FX FY X Y v c) X Y -
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      regularBaseline FX FY X Y v c ≤
      perColourCharge h hca hcb / ((Fintype.card V : ℝ) * Fintype.card C) := by
  simpa only [regularBaseline, h.X_root, h.Y_root] using
    selectedRegular_local_charge_le h hca hcb

end
end ZeroFreeness
