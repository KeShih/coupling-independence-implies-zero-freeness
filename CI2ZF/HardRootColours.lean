import CI2ZF.HardMoveClassification
import CI2ZF.HardMatchCost

/-! Actual allocations for the two root-colour groups. -/
namespace CI2ZF
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]
local instance hardRootColoursColouringDecEq : DecidableEq (V → C) := Classical.decEq _

lemma hardStep_move_mass_le_inv_nq [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (hX : F.IsProper X)
    (u : V) (c : C) (hc : c ≠ X u) :
    (hardStep F X).w (flipConfiguration X (flipSet F.graph X u c) (X u) c) ≤
      1 / ((Fintype.card V : ℝ) * Fintype.card C) := by
  by_cases ha : flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)
  · rw [hardStep_component_mass F X u c hc ha]
    exact div_le_div_of_nonneg_right (vigodaMass_le_one _) (by positivity)
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

/-- Exact Hamming drift for a root-colour move paired with holding. -/
theorem root_colour_holding_ham
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    ham X (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) - 1 =
      ((flipSet FY.graph Y v a).card : ℝ) - 2 := by
  rw [ham_comm X, h.Y_root,
    root_holding_match_ham h.Y_root h.X_root h.colours_ne.symm
      (fun w hw => (h.agree_off_root w hw).symm) self_mem_flipSet
      (fun w hw => by simpa only [h.Y_root] using colour_eq_of_mem_flipSet hw)]
  ring

/-- With one active root neighbour, an opposite component that stays
off-root is exactly the root component with the root removed. -/
theorem root_colour_single_piece
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hneigh : rootNeighbours FY Y v a = {u})
    (hv : v ∉ flipSet FX.graph X u b) :
    flipSet FY.graph Y v a = insert v (flipSet FX.graph X u b) := by
  have hu : u ∈ rootNeighbours FY Y v a := by rw [hneigh]; simp
  have hXu : X u = a := (h.agree_off_root u (rootNeighbour_ne_root hu)).trans
    (mem_rootNeighbours.mp hu).2
  rw [root_flipSet_eq FY Y v a (by simpa only [h.Y_root] using h.colours_ne)]
  have hfamily : rootFamily FY Y v a = {offRootComponent FY Y v (Y v) a u} := by
    simp [rootFamily, hneigh]
  rw [hfamily]
  congr 1
  rw [flipSet_eq_offRootComponent_of_not_mem FX X v u b hv,
    h.offRootComponent_eq, hXu, h.Y_root]
  simpa using offRootComponent_swap_colours FY Y v u b a

/-- The special one-neighbour root/piece match really coalesces. -/
theorem root_colour_single_coalesces
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hneigh : rootNeighbours FY Y v a = {u})
    (hv : v ∉ flipSet FX.graph X u b) :
    flipConfiguration X (flipSet FX.graph X u b) (X u) b =
      flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a := by
  have hu : u ∈ rootNeighbours FY Y v a := by rw [hneigh]; simp
  have hXu : X u = a := (h.agree_off_root u (rootNeighbour_ne_root hu)).trans
    (mem_rootNeighbours.mp hu).2
  rw [root_colour_single_piece h hneigh hv, hXu, h.Y_root]
  rw [root_offRoot_match_coalesces h.Y_root h.X_root
    (fun w hw => (h.agree_off_root w hw).symm) hv]
  exact flipConfiguration_swap_colours h.colours_ne
    (fun w hw => by simpa only [hXu] using colour_eq_of_mem_flipSet hw)

theorem root_colour_single_allowed_iff
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hneigh : rootNeighbours FY Y v a = {u})
    (hv : v ∉ flipSet FX.graph X u b) :
    flipAllowed FY (flipSet FY.graph Y v a)
      (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) ↔
    a ∈ FY.list v ∧ flipAllowed FX (flipSet FX.graph X u b)
      (flipConfiguration X (flipSet FX.graph X u b) (X u) b) := by
  have hroot : flipConfiguration X (flipSet FX.graph X u b) (X u) b v = a := by
    rw [flipConfiguration_of_not_mem hv, h.X_root]
  rw [← root_colour_single_coalesces h hneigh hv, root_colour_single_piece h hneigh hv]
  constructor
  · intro ha
    refine ⟨by simpa only [hroot] using ha v (Finset.mem_insert_self _ _), ?_⟩
    intro w hw
    have hwv : w ≠ v := fun heq => hv (heq ▸ hw)
    rw [h.offRoot_list_eq w hwv]
    exact ha w (Finset.mem_insert_of_mem hw)
  · rintro ⟨hr, hs⟩ w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rwa [hroot]
    · have hwv : w ≠ v := fun heq => hv (heq ▸ hw)
      rw [← h.offRoot_list_eq w hwv]
      exact hs w hw

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
    apply VigodaArithmetic.profile_antitone _ _ flipSet_card_pos
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

def rootColourCanPair (FX FY : HardListInstance V C) (X Y : V → C) (v : V) : Prop :=
  ∃ u, rootNeighbours FY Y v (X v) = {u} ∧ v ∉ flipSet FX.graph X u (Y v)

def rootColourPartner (FX FY : HardListInstance V C) (X Y : V → C) (v : V) : V → C :=
  if hp : rootColourCanPair FX FY X Y v then
    let u := hp.choose
    flipConfiguration X (flipSet FX.graph X u (Y v)) (X u) (Y v)
  else X

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

omit [Fintype C] in
lemma rootColourPartner_of_single
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hn : rootNeighbours FY Y v a = {u}) (hv : v ∉ flipSet FX.graph X u b) :
    rootColourPartner FX FY X Y v =
      flipConfiguration X (flipSet FX.graph X u b) (X u) b := by
  have hp : rootColourCanPair FX FY X Y v :=
    ⟨u, by simpa only [h.X_root] using hn, by simpa only [h.Y_root] using hv⟩
  have hu : hp.choose = u := by
    have hc : rootNeighbours FY Y v a = {hp.choose} := by
      simpa only [h.X_root] using hp.choose_spec.1
    exact Finset.singleton_inj.mp (hc.symm.trans hn)
  unfold rootColourPartner
  rw [dif_pos hp]
  change flipConfiguration X (flipSet FX.graph X hp.choose (Y v)) (X hp.choose) (Y v) = _
  rw [hu, h.Y_root]

lemma rootColourPartner_root
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} :
    rootColourPartner FX FY X Y v v = X v := by
  unfold rootColourPartner
  split_ifs with hp
  · exact flipConfiguration_of_not_mem hp.choose_spec.2
  · rfl

end
end CI2ZF
