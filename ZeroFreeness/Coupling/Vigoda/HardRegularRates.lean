import ZeroFreeness.Coupling.Vigoda.HardRootAllocation
import ZeroFreeness.Coupling.Vigoda.RegularColourCharge

/-! The rates in the scalar colour charges are the probabilities of the
actual root and opposite-side component moves, after scaling by |V||C|. -/
namespace ZeroFreeness
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open RootComponentGeometry RegularColourCharge
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance regularRatesFunctionDecEq : DecidableEq (V → C) := Classical.decEq _

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

/-- Actual off-root outputs coincide exactly when their off-root pieces do.
This identifies incidence multiplicities with their state-level capacities. -/
lemma opposite_output_eq_iff_piece_eq
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FX X v c) :
    flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a =
      flipConfiguration Y (flipSet FY.graph Y w a) (Y w) a ↔
    offRootComponent FX X v a c u = offRootComponent FX X v a c w := by
  have huc : Y u = c := (h.agree_off_root u (rootNeighbour_ne_root hu)).symm.trans
    (mem_rootNeighbours.mp hu).2
  have hwc : Y w = c := (h.agree_off_root w (rootNeighbour_ne_root hw)).symm.trans
    (mem_rootNeighbours.mp hw).2
  rw [h.offRootComponent_eq_opposite_flipSet hcb hu,
    h.offRootComponent_eq_opposite_flipSet hcb hw]
  constructor
  · intro heq
    ext z
    rw [← flipConfiguration_ne_iff (by rw [huc]; exact hca.symm),
      ← flipConfiguration_ne_iff (by rw [hwc]; exact hca.symm), heq]
  · intro hset
    rw [hset, huc, hwc]

/-- The actual remaining column probability after root matching equals the
paper's off-root residual rate divided by the proposal normalization. -/
theorem selectedRootPartial_rightResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    (regularRootPartial FX FY X Y v c
      (selectedRepresentative FX X v c) (selectedRepresentative FY Y v c)).rightResidual
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) =
    residual FX X v c (offRootComponent FX X v a c u) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hN : (rootNeighbours FX X v c).Nonempty := ⟨u, hu⟩
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have huStar := selectedRepresentative_mem FX X v c hN
  have hwStar := selectedRepresentative_mem FY Y v c hNY
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
  have hstarset : offRootComponent FX X v a c (selectedRepresentative FX X v c) =
      largestPiece FX X v c := by
    simp only [largestPiece, h.X_root]
  have heq := opposite_output_eq_iff_piece_eq h hca hcb u
    (selectedRepresentative FX X v c) hu huStar
  rw [hstarset] at heq
  simp only [heq]
  rw [hardStep_opposite_pieceRate h hca hcb u hu,
    hardStep_rootRate FX X h.properX v c (by rwa [h.X_root])]
  unfold RegularColourCharge.residual
  by_cases hsame : offRootComponent FX X v a c u = largestPiece FX X v c
  · rw [if_pos hsame, if_pos hsame, sub_div]
  · rw [if_neg hsame, if_neg hsame, sub_zero, sub_zero]

/-- The symmetric true row residual is the other family's scalar residual. -/
theorem selectedRootPartial_leftResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u : V) (hu : u ∈ rootNeighbours FY Y v c) :
    (regularRootPartial FX FY X Y v c
      (selectedRepresentative FX X v c) (selectedRepresentative FY Y v c)).leftResidual
      (flipConfiguration X (flipSet FX.graph X u b) (X u) b) =
    residual FY Y v c (offRootComponent FY Y v b c u) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hNY : (rootNeighbours FY Y v c).Nonempty := ⟨u, hu⟩
  have hN : (rootNeighbours FX X v c).Nonempty := (h.rootNeighbours_eq hca hcb).symm ▸ hNY
  have huStar := selectedRepresentative_mem FX X v c hN
  have hwStar := selectedRepresentative_mem FY Y v c hNY
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
  have hstarset : offRootComponent FY Y v b c (selectedRepresentative FY Y v c) =
      largestPiece FY Y v c := by
    simp only [largestPiece, h.Y_root]
  have heq := opposite_output_eq_iff_piece_eq h.symm hcb hca u
    (selectedRepresentative FY Y v c) hu hwStar
  rw [hstarset] at heq
  simp only [heq]
  rw [hardStep_opposite_pieceRate h.symm hcb hca u hu,
    hardStep_rootRate FY Y h.properY v c (by rwa [h.Y_root])]
  unfold RegularColourCharge.residual
  by_cases hsame : offRootComponent FY Y v b c u = largestPiece FY Y v c
  · rw [if_pos hsame, if_pos hsame, sub_div]
  · rw [if_neg hsame, if_neg hsame, sub_zero, sub_zero]

end
end ZeroFreeness
