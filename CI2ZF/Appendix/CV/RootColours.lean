import CI2ZF.Appendix.CV.RootAllocation
import CI2ZF.HardRootColours

/-! Both root-colour allocations with their actual CV transition masses. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvRootColoursColouringDecEq : DecidableEq (V → C) := Classical.decEq _

lemma hardStep_move_mass_le_inv_nq [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (hX : F.IsProper X)
    (u : V) (c : C) (hc : c ≠ X u) :
    (hardStep F X).w (flipConfiguration X (flipSet F.graph X u c) (X u) c) ≤
      1 / ((Fintype.card V : ℝ) * Fintype.card C) := by
  by_cases ha : flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)
  · rw [hardStep_component_mass F X u c hc ha]
    exact div_le_div_of_nonneg_right (mass_le_one _) (by positivity)
  · rw [hardStep_blocked_component_mass F X hX u c ha]
    positivity

/-- The reserved holding probability pays for a whole root-colour move. -/
theorem root_colour_holding_capacity [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) ≤
      (hardStep FX X).w X := by
  apply (hardStep_move_mass_le_inv_nq FY Y h.properY v a
    (by simpa only [h.Y_root] using h.colours_ne)).trans
  apply le_trans _ (hardStep_holding_mass FX X)
  apply one_div_le_one_div_of_le (by positivity)
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  nlinarith [show 0 ≤ (Fintype.card C : ℝ) by positivity]

def rootColourHoldPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
  (hardCommonOffRootPartial FX FY X Y v).matchPointAtMost X SY
    ((hardStep FY Y).w SY) ((hardStep FY Y).nonneg SY)

/-- A root-to-holding allocation uses the entire true root-move mass,
with no residual-capacity hypothesis. -/
theorem rootColourHoldPartial_full [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C) :
    let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
    (rootColourHoldPartial FX FY X Y v).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z +
        if U = X ∧ Z = SY then (hardStep FY Y).w SY else 0 := by
  dsimp only [rootColourHoldPartial]
  apply PartialCoupling.matchPointAtMost_full
  · have hr : (hardCommonOffRootPartial FX FY X Y v).leftResidual X =
        (hardStep FX X).w X := by
      simp [PartialCoupling.leftResidual, hardCommonOffRootPartial]
    rw [hr, h.X_root]
    exact root_colour_holding_capacity h
  · rw [h.X_root, regular_root_common_rightResidual h h.colours_ne]

/-- The one-neighbour root/piece allocation has enough genuine component
mass on the opposite side. -/
theorem root_colour_single_capacity [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hneigh : rootNeighbours FY Y v a = {u})
    (hv : v ∉ flipSet FX.graph X u b) :
    (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) ≤
      (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X u b) (X u) b) := by
  have hu : u ∈ rootNeighbours FY Y v a := by rw [hneigh]; simp
  have hXu : X u = a := (h.agree_off_root u (rootNeighbour_ne_root hu)).trans
    (mem_rootNeighbours.mp hu).2
  by_cases ha : flipAllowed FY (flipSet FY.graph Y v a)
      (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a)
  · have hb := ((root_colour_single_allowed_iff h hneigh hv).mp ha).2
    rw [hardStep_component_mass FY Y v a (by simpa only [h.Y_root] using h.colours_ne) ha,
      hardStep_component_mass FX X u b (by simpa only [hXu] using h.colours_ne.symm) hb]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mass_antitone flipSet_card_pos
    rw [root_colour_single_piece h hneigh hv]
    exact Finset.card_le_card (Finset.subset_insert _ _)
  · rw [hardStep_blocked_component_mass FY Y h.properY v a ha]
    exact (hardStep FX X).nonneg _

def rootColourPiecePartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v u : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
  let CX := flipConfiguration X (flipSet FX.graph X u (Y v)) (X u) (Y v)
  (hardCommonOffRootPartial FX FY X Y v).matchPointAtMost CX SY
    ((hardStep FY Y).w SY) ((hardStep FY Y).nonneg SY)

theorem rootColourPiecePartial_full [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hneigh : rootNeighbours FY Y v a = {u})
    (hv : v ∉ flipSet FX.graph X u b) (U Z : V → C) :
    let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
    let CX := flipConfiguration X (flipSet FX.graph X u (Y v)) (X u) (Y v)
    (rootColourPiecePartial FX FY X Y v u).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z +
        if U = CX ∧ Z = SY then (hardStep FY Y).w SY else 0 := by
  dsimp only [rootColourPiecePartial]
  apply PartialCoupling.matchPointAtMost_full
  · rw [h.Y_root, h.X_root, regular_piece_common_leftResidual h u
      (by rw [hneigh]; simp)]
    simpa only [h.Y_root] using root_colour_single_capacity h hneigh hv
  · rw [h.X_root, regular_root_common_rightResidual h h.colours_ne]

def rootColourPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
  (hardCommonOffRootPartial FX FY X Y v).matchPointAtMost
    (rootColourPartner FX FY X Y v) SY ((hardStep FY Y).w SY) ((hardStep FY Y).nonneg SY)

/-- The actual prescribed root-colour rule chooses coalescence in the
one-neighbour off-root case and holding in every other case. -/
theorem rootColourPartial_full [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C) :
    let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
    (rootColourPartial FX FY X Y v).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z +
        if U = rootColourPartner FX FY X Y v ∧ Z = SY
          then (hardStep FY Y).w SY else 0 := by
  by_cases hp : rootColourCanPair FX FY X Y v
  · have hs := hp.choose_spec
    have hn : rootNeighbours FY Y v a = {hp.choose} := by
      simpa only [h.X_root] using hs.1
    have hv : v ∉ flipSet FX.graph X hp.choose b := by
      simpa only [h.Y_root] using hs.2
    simpa only [rootColourPartial, rootColourPartner, dif_pos hp, rootColourPiecePartial]
      using rootColourPiecePartial_full h hn hv U Z
  · simpa only [rootColourPartial, rootColourPartner, dif_neg hp, rootColourHoldPartial]
      using rootColourHoldPartial_full h U Z


end
end CI2ZF.Appendix.CV
