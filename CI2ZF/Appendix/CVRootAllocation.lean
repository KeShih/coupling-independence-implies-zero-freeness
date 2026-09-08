import CI2ZF.Appendix.CVCoupling
import CI2ZF.RootComponentGeometry

/-! Full root-to-component CV matches, with capacities proved from actual
component geometry and the CV profile's monotonicity. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance rootAllocationFunctionDecEq : DecidableEq (V → C) := Classical.decEq _
private lemma profile_antitone (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) : mass s ≤ mass r :=
  mass_antitone hr hrs

lemma hardStep_blocked_component_mass [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (hX : F.IsProper X) (u : V) (c : C)
    (ha : ¬ flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)) :
    (hardStep F X).w (flipConfiguration X (flipSet F.graph X u c) (X u) c) = 0 := by
  apply hardStep_support hX
  intro hproper
  exact ha (fun w _ => hproper.2 w)

/-- Every opposite-side component has enough true row mass to receive the
entire feasible root-component move. Blocked root moves contribute zero. -/
theorem regular_root_mass_le_piece_mass [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X v c) (X v) c) ≤
      (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) := by
  by_cases ha : flipAllowed FX (flipSet FX.graph X v c)
      (flipConfiguration X (flipSet FX.graph X v c) (X v) c)
  · have hb := ((h.root_flipAllowed_iff_opposite hca hcb).mp ha).2 u hu
    have hYu : Y u = c := (h.agree_off_root u (rootNeighbour_ne_root hu)).symm.trans
      (mem_rootNeighbours.mp hu).2
    rw [hardStep_component_mass FX X v c (by rwa [h.X_root]) ha,
      hardStep_component_mass FY Y u a (by rw [hYu]; exact hca.symm) hb]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply profile_antitone _ _ (by
      exact flipSet_card_pos (G := FY.graph) (X := Y) (u := u) (c := a))
    apply Finset.card_le_card
    rw [← h.offRootComponent_eq_opposite_flipSet hcb hu]
    apply root_piece_subset_root (by rwa [h.X_root])
    rw [← h.X_root]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · rw [hardStep_blocked_component_mass FX X h.properX v c ha]
    exact (hardStep FY Y).nonneg _

/-- The opposite off-root move recolours an actual root neighbour to the
original root colour. Restoring that root creates a monochromatic edge. -/
theorem regular_piece_inverse_improper
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    ¬ FX.IsProper (replaceRoot
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) v (X v)) := by
  intro hp
  apply hp.1 v u (mem_rootNeighbours.mp hu).1
  rw [replaceRoot_at_root,
    replaceRoot_off_root _ _ _ _ (rootNeighbour_ne_root hu), flipConfiguration_at_start,
    h.X_root]

lemma regular_root_common_leftResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) :
    (hardCommonOffRootPartial FX FY X Y v).leftResidual
      (flipConfiguration X (flipSet FX.graph X v c) (X v) c) =
    (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X v c) (X v) c) := by
  unfold PartialCoupling.leftResidual
  have hroot : (flipConfiguration X (flipSet FX.graph X v c) (X v) c) v ≠ X v := by
    rwa [flipConfiguration_at_start, h.X_root]
  simp only [hardCommonOffRootPartial,
    commonOffRootPartial_changed_root_row _ _ _ _ _ _ _ hroot,
    Finset.sum_const_zero, sub_zero]

lemma regular_piece_common_rightResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    (hardCommonOffRootPartial FX FY X Y v).rightResidual
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) =
    (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) := by
  unfold PartialCoupling.rightResidual
  simp only [hardCommonOffRoot_col_zero_of_improper FX FY X Y v h.properX _
    (regular_piece_inverse_improper h u hu), Finset.sum_const_zero, sub_zero]

/-- The first regular root-to-piece allocation uses the full true root
probability; no capacity or desired-drift hypothesis is supplied. -/
theorem regular_first_match_full [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) (U Z : V → C) :
    let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
    let CY := flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a
    let mu := hardStep FX X
    ((hardCommonOffRootPartial FX FY X Y v).matchPointAtMost RX CY (mu.w RX)
      (mu.nonneg RX)).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z +
        if U = RX ∧ Z = CY then mu.w RX else 0 := by
  dsimp only
  apply PartialCoupling.matchPointAtMost_full
  · rw [regular_root_common_leftResidual h hca]
  · rw [regular_piece_common_rightResidual h u hu]
    exact regular_root_mass_le_piece_mass h hca hcb u hu

lemma regular_piece_no_root
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hcb : c ≠ b)
    (u : V) (hu : u ∈ rootNeighbours FX X v c) :
    v ∉ flipSet FY.graph Y u a := by
  rw [← h.offRootComponent_eq_opposite_flipSet hcb hu]
  intro hv
  exact ne_root_of_mem_offRootComponent (rootNeighbour_ne_root hu) hv rfl

lemma regular_root_common_rightResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hcb : c ≠ b) :
    (hardCommonOffRootPartial FX FY X Y v).rightResidual
      (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) =
    (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) := by
  unfold PartialCoupling.rightResidual
  have hroot : (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) v ≠ Y v := by
    rwa [flipConfiguration_at_start, h.Y_root]
  simp only [hardCommonOffRootPartial,
    commonOffRootPartial_changed_root_col _ _ _ _ _ _ _ hroot,
    Finset.sum_const_zero, sub_zero]

lemma regular_piece_common_leftResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b)
    (w : V) (hw : w ∈ rootNeighbours FY Y v c) :
    (hardCommonOffRootPartial FX FY X Y v).leftResidual
      (flipConfiguration X (flipSet FX.graph X w b) (X w) b) =
    (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X w b) (X w) b) := by
  unfold PartialCoupling.leftResidual
  simp only [hardCommonOffRoot_row_zero_of_improper FX FY X Y v h.properY _
    (regular_piece_inverse_improper h.symm w hw), Finset.sum_const_zero, sub_zero]

/-- Both root allocations fit in full and occupy distinct actual rows and
columns. This is the exact two-point part of the regular-colour plan. -/
theorem regularRootPartial_full [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U Z : V → C) :
    let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
    let SY := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
    let CY := flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a
    let DX := flipConfiguration X (flipSet FX.graph X w b) (X w) b
    (regularRootPartial FX FY X Y v c u w).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z +
        (if U = RX ∧ Z = CY then (hardStep FX X).w RX else 0) +
        (if U = DX ∧ Z = SY then (hardStep FY Y).w SY else 0) := by
  dsimp only
  let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
  let SY := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
  let CY := flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a
  let DX := flipConfiguration X (flipSet FX.graph X w b) (X w) b
  let kappa := hardCommonOffRootPartial FX FY X Y v
  let first := kappa.matchPointAtMost RX CY ((hardStep FX X).w RX) ((hardStep FX X).nonneg RX)
  have hDX : DX v = X v := flipConfiguration_of_not_mem (regular_piece_no_root h.symm hca w hw)
  have hCY : CY v = Y v := flipConfiguration_of_not_mem (regular_piece_no_root h hcb u hu)
  have hRX : RX v = c := flipConfiguration_at_start
  have hSY : SY v = c := flipConfiguration_at_start
  have hrow : DX ≠ RX := by
    intro hh
    have hc := congrFun hh v
    rw [hDX, hRX, h.X_root] at hc
    exact hca hc.symm
  have hcol : SY ≠ CY := by
    intro hh
    have hc := congrFun hh v
    rw [hSY, hCY, h.Y_root] at hc
    exact hcb hc
  have hleft : (hardStep FY Y).w SY ≤ first.leftResidual DX := by
    rw [PartialCoupling.matchPointAtMost_leftResidual_of_ne _ _ _ _ _ _ hrow]
    rw [regular_piece_common_leftResidual h w hw]
    exact regular_root_mass_le_piece_mass h.symm hcb hca w hw
  have hright : (hardStep FY Y).w SY ≤ first.rightResidual SY := by
    rw [PartialCoupling.matchPointAtMost_rightResidual_of_ne _ _ _ _ _ _ hcol]
    rw [regular_root_common_rightResidual h hcb]
  have hsecond := PartialCoupling.matchPointAtMost_full first DX SY ((hardStep FY Y).w SY)
    ((hardStep FY Y).nonneg SY) hleft hright U Z
  have hfirst := regular_first_match_full h hca hcb u hu U Z
  have hCYdef : flipConfiguration Y (flipSet FY.graph Y u (X v)) (Y u) (X v) = CY := by
    dsimp only [CY]
    rw [h.X_root]
  have hDXdef : flipConfiguration X (flipSet FX.graph X w (Y v)) (X w) (Y v) = DX := by
    dsimp only [DX]
    rw [h.Y_root]
  have hplan : regularRootPartial FX FY X Y v c u w =
      first.matchPointAtMost DX SY ((hardStep FY Y).w SY) ((hardStep FY Y).nonneg SY) := by
    unfold regularRootPartial
    dsimp only
    rw [hCYdef, hDXdef]
  rw [hplan, hsecond, hfirst]

/-- Exact column residuals after both regular root allocations. -/
theorem regularRootPartial_rightResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (Z : V → C) :
    let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
    let SY := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
    let CY := flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a
    (regularRootPartial FX FY X Y v c u w).rightResidual Z =
      (hardCommonOffRootPartial FX FY X Y v).rightResidual Z -
        (if Z = CY then (hardStep FX X).w RX else 0) -
        (if Z = SY then (hardStep FY Y).w SY else 0) := by
  dsimp only
  unfold PartialCoupling.rightResidual
  simp_rw [regularRootPartial_full h hca hcb u w hu hw]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Exact row residuals after both regular root allocations. -/
theorem regularRootPartial_leftResidual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U : V → C) :
    let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
    let SY := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
    let DX := flipConfiguration X (flipSet FX.graph X w b) (X w) b
    (regularRootPartial FX FY X Y v c u w).leftResidual U =
      (hardCommonOffRootPartial FX FY X Y v).leftResidual U -
        (if U = RX then (hardStep FX X).w RX else 0) -
        (if U = DX then (hardStep FY Y).w SY else 0) := by
  dsimp only
  unfold PartialCoupling.leftResidual
  simp_rw [regularRootPartial_full h hca hcb u w hu hw]
  have hsum (R T : V → C) (p : ℝ) : (∑ Z, if U = R ∧ Z = T then p else 0) =
      if U = R then p else 0 := by
    by_cases hu : U = R <;> simp [hu]
  simp only [Finset.sum_add_distrib, hsum]
  ring

end
end CI2ZF.Appendix.CV
