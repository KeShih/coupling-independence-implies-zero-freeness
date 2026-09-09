import CI2ZF.Appendix.CV.CanonicalCoupling
import CI2ZF.HardRegularRates

/-! Exact CV rates for actual component moves and residuals. The selected
representatives are explicit parameters, so a later joint maximum choice can
enforce the common-maximum tie rule without changing the transition kernel. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvRatesColouringDecEq : DecidableEq (V → C) := Classical.decEq _

def pieceRate (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) : ℝ :=
  if flipAllowed F S (flipConfiguration X S (X v) c) then mass S.card else 0

def rootRate (F : HardListInstance V C) (X : V → C) (v : V) (c : C) : ℝ :=
  if flipAllowed F (flipSet F.graph X v c)
    (flipConfiguration X (flipSet F.graph X v c) (X v) c)
  then mass (flipSet F.graph X v c).card else 0

def componentResidual (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (u : V) (S : Finset V) : ℝ :=
  pieceRate F X v c S -
    if S = offRootComponent F X v (X v) c u then rootRate F X v c else 0

def rootCharge (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (u : V) : ℝ :=
  ((flipSet F.graph X v c).card - (offRootComponent F X v (X v) c u).card - 1 : ℝ) *
    rootRate F X v c

lemma pieceRate_nonneg (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) :
    0 ≤ pieceRate F X v c S := by
  unfold pieceRate
  split_ifs <;> simp_all [mass_nonneg]

lemma pieceRate_le_mass (F : HardListInstance V C) (X : V → C) (v : V) (c : C) (S : Finset V) :
    pieceRate F X v c S ≤ mass S.card := by
  unfold pieceRate
  split_ifs
  · exact le_rfl
  · exact mass_nonneg _

lemma rootRate_nonneg (F : HardListInstance V C) (X : V → C) (v : V) (c : C) :
    0 ≤ rootRate F X v c := by
  unfold rootRate
  split_ifs
  · exact mass_nonneg _
  · exact le_rfl

lemma rootRate_le_pieceRate (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (S : Finset V) (hS : S ∈ rootFamily F X v c) :
    rootRate F X v c ≤ pieceRate F X v c S := by
  unfold rootRate
  split_ifs with hroot
  · have hp := ((root_flipAllowed_iff F X v c hc).mp hroot).2 S hS
    rw [pieceRate, if_pos hp]
    exact mass_antitone (Finset.card_pos.mpr (rootFamily_nonempty_component hS))
      (Finset.card_le_card (root_piece_subset_root hc hS))
  · exact pieceRate_nonneg F X v c S

lemma componentResidual_nonneg (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (S : RootPiece F X v c) :
    0 ≤ componentResidual F X v c u S := by
  unfold componentResidual
  split_ifs
  · exact sub_nonneg.mpr (rootRate_le_pieceRate F X v c hc S S.property)
  · simpa using pieceRate_nonneg F X v c S

lemma componentResidual_le_mass (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (u : V) (S : Finset V) : componentResidual F X v c u S ≤ mass S.card := by
  have hr := rootRate_nonneg F X v c
  have hp := pieceRate_le_mass F X v c S
  unfold componentResidual
  split_ifs <;> linarith

lemma rootRate_zero_of_unavailable (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ∉ F.list v) : rootRate F X v c = 0 := by
  unfold rootRate
  rw [if_neg]
  intro hallowed
  apply hc
  simpa using hallowed v self_mem_flipSet

lemma hardStep_rootRate [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (hX : F.IsProper X) (v : V) (c : C)
    (hc : c ≠ X v) :
    (hardStep F X).w (flipConfiguration X (flipSet F.graph X v c) (X v) c) =
      rootRate F X v c / ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold rootRate
  split_ifs with ha
  · exact hardStep_component_mass F X v c hc ha
  · rw [hardStep_blocked_component_mass F X hX v c ha, zero_div]

lemma hardStep_opposite_pieceRate [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) =
      pieceRate FX X v c (offRootComponent FX X v a c u) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hYu : Y u = c := (h.agree_off_root u (rootNeighbour_ne_root hu)).symm.trans
    (mem_rootNeighbours.mp hu).2
  unfold pieceRate
  rw [h.X_root]
  split_ifs with ha
  · have hay := (h.offRoot_flipAllowed_iff hca hcb hu).mp ha
    rw [hardStep_component_mass FY Y u a (by rw [hYu]; exact hca.symm) hay,
      h.offRootComponent_eq_opposite_flipSet hcb hu]
  · have hay : ¬ flipAllowed FY (flipSet FY.graph Y u a)
        (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) :=
      fun hh => ha ((h.offRoot_flipAllowed_iff hca hcb hu).mpr hh)
    rw [hardStep_blocked_component_mass FY Y h.properY u a hay, zero_div]

theorem rootPartial_rightResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (uStar wStar : V) (huStar : uStar ∈ rootNeighbours FX X v c)
    (hwStar : wStar ∈ rootNeighbours FY Y v c)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    (regularRootPartial FX FY X Y v c uStar wStar).rightResidual
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) =
    componentResidual FX X v c uStar (offRootComponent FX X v a c u) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [regularRootPartial_rightResidual h hca hcb _ _ huStar hwStar,
    regular_piece_common_rightResidual h u hu]
  have hnotroot : flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a ≠
      flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c := by
    intro heq
    have hc := congrFun heq v
    rw [flipConfiguration_of_not_mem (regular_piece_no_root h hcb u hu),
      flipConfiguration_at_start, h.Y_root] at hc
    exact hcb hc.symm
  rw [if_neg hnotroot, sub_zero]
  have heq := opposite_output_eq_iff_piece_eq h hca hcb u uStar hu huStar
  simp only [heq]
  rw [hardStep_opposite_pieceRate h hca hcb u hu,
    hardStep_rootRate FX X h.properX v c (by rwa [h.X_root])]
  unfold componentResidual
  rw [h.X_root]
  split_ifs <;> simp [sub_div]

theorem rootPartial_leftResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (uStar wStar : V) (huStar : uStar ∈ rootNeighbours FX X v c)
    (hwStar : wStar ∈ rootNeighbours FY Y v c)
    (u : V) (hu : u ∈ rootNeighbours FY Y v c) :
    (regularRootPartial FX FY X Y v c uStar wStar).leftResidual
      (flipConfiguration X (flipSet FX.graph X u b) (X u) b) =
    componentResidual FY Y v c wStar (offRootComponent FY Y v b c u) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [regularRootPartial_leftResidual h hca hcb _ _ huStar hwStar,
    regular_piece_common_leftResidual h u hu]
  have hnotroot : flipConfiguration X (flipSet FX.graph X u b) (X u) b ≠
      flipConfiguration X (flipSet FX.graph X v c) (X v) c := by
    intro heq
    have hc := congrFun heq v
    rw [flipConfiguration_of_not_mem (regular_piece_no_root h.symm hca u hu),
      flipConfiguration_at_start, h.X_root] at hc
    exact hca hc.symm
  rw [if_neg hnotroot, sub_zero]
  have heq := opposite_output_eq_iff_piece_eq h.symm hcb hca u wStar hu hwStar
  simp only [heq]
  rw [hardStep_opposite_pieceRate h.symm hcb hca u hu,
    hardStep_rootRate FY Y h.properY v c (by rwa [h.Y_root])]
  unfold componentResidual
  rw [h.Y_root]
  split_ifs <;> simp [sub_div]

end
end CI2ZF.Appendix.CV
