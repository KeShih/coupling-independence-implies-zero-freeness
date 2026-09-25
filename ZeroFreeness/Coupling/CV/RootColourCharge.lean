import ZeroFreeness.Coupling.CV.RootColours
import ZeroFreeness.Coupling.Vigoda.RootColourCharge

/-! Root-colour charges and profile bounds for the actual CV transitions. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]
local instance cvRootColourChargeDecEq : DecidableEq (V → C) := Classical.decEq _

def scaledMoveMass (F : HardListInstance V C) (X : V → C) (u : V) (c : C) : ℝ :=
  ((Fintype.card V : ℝ) * Fintype.card C) *
    (hardStep F X).w (flipConfiguration X (flipSet F.graph X u c) (X u) c)

lemma scaledMoveMass_of_allowed (F : HardListInstance V C) (X : V → C)
    (u : V) (c : C) (hc : c ≠ X u)
    (ha : flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)) :
    scaledMoveMass F X u c = mass (flipSet F.graph X u c).card := by
  unfold scaledMoveMass
  rw [hardStep_component_mass F X u c hc ha]
  field_simp

lemma scaledMoveMass_of_blocked (F : HardListInstance V C) (X : V → C)
    (hX : F.IsProper X) (u : V) (c : C)
    (ha : ¬ flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)) :
    scaledMoveMass F X u c = 0 := by
  simp only [scaledMoveMass, hardStep_blocked_component_mass F X hX u c ha, mul_zero]

lemma scaledMoveMass_size_bound (F : HardListInstance V C) (X : V → C)
    (hX : F.IsProper X) (u : V) (c : C) (hc : c ≠ X u) :
    ((flipSet F.graph X u c).card : ℝ) * scaledMoveMass F X u c ≤ 1 := by
  by_cases ha : flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)
  · rw [scaledMoveMass_of_allowed F X u c hc ha]
    exact size_mass_le_one _
  · rw [scaledMoveMass_of_blocked F X hX u c ha]
    norm_num

lemma root_colour_holding_charge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (ham X (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) - 1) *
      scaledMoveMass FY Y v a ≤ 22 / 125 := by
  rw [root_colour_holding_ham h]
  by_cases ha : flipAllowed FY (flipSet FY.graph Y v a)
      (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a)
  · rw [scaledMoveMass_of_allowed FY Y v a
      (by simpa only [h.Y_root] using h.colours_ne) ha]
    exact sub_two_size_mass_le _
  · rw [scaledMoveMass_of_blocked FY Y h.properY v a ha]
    norm_num

/-- Exact-profile charge for the special coalescing root/piece match.
Both feasibility bits are obtained from the real list tests. -/
theorem root_colour_single_charge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hn : rootNeighbours FY Y v a = {u}) (hv : v ∉ flipSet FX.graph X u b)
    (hl : a ∈ FY.list v) :
    ((flipSet FX.graph X u b).card : ℝ) * scaledMoveMass FX X u b -
      (((flipSet FX.graph X u b).card : ℝ) + 1) * scaledMoveMass FY Y v a ≤ 44 / 125 := by
  have hu : u ∈ rootNeighbours FY Y v a := by rw [hn]; simp
  have hXu : X u = a := (h.agree_off_root u (rootNeighbour_ne_root hu)).trans
    (mem_rootNeighbours.mp hu).2
  have hcard : (flipSet FY.graph Y v a).card = (flipSet FX.graph X u b).card + 1 := by
    rw [root_colour_single_piece h hn hv, Finset.card_insert_of_notMem hv]
  by_cases ha : flipAllowed FX (flipSet FX.graph X u b)
      (flipConfiguration X (flipSet FX.graph X u b) (X u) b)
  · have hb := (root_colour_single_allowed_iff h hn hv).mpr ⟨hl, ha⟩
    rw [scaledMoveMass_of_allowed FX X u b (by simpa only [hXu] using h.colours_ne.symm) ha,
      scaledMoveMass_of_allowed FY Y v a (by simpa only [h.Y_root] using h.colours_ne) hb,
      hcard]
    simpa only [Nat.cast_add, Nat.cast_one] using
      root_colour_one_neighbour (flipSet FX.graph X u b).card
  · have hb : ¬ flipAllowed FY (flipSet FY.graph Y v a)
        (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) :=
      fun hh => ha ((root_colour_single_allowed_iff h hn hv).mp hh).2
    rw [scaledMoveMass_of_blocked FX X h.properX u b ha,
      scaledMoveMass_of_blocked FY Y h.properY v a hb]
    norm_num

def rootColourOffCharge (FX FY : HardListInstance V C) (X Y : V → C) (v : V) : ℝ :=
  ∑ U ∈ rootColourOffRows FX FY X Y v,
    ham X U * (((Fintype.card V : ℝ) * Fintype.card C) * (hardStep FX X).w U)

/-- Size charges on the unmatched off-root moves, plus the actual root
match drift, minus the consumed partner's size charge. -/
def rootColourCharge (FX FY : HardListInstance V C) (X Y : V → C) (v : V) : ℝ :=
  let SY := flipConfiguration Y (flipSet FY.graph Y v (X v)) (Y v) (X v)
  let P := rootColourPartner FX FY X Y v
  rootColourOffCharge FX FY X Y v +
    (ham P SY - 1 - ham X P) * scaledMoveMass FY Y v (X v)

lemma rootColourOffCharge_le_degree
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    rootColourOffCharge FX FY X Y v ≤ (rootNeighbours FY Y v a).card := by
  have hterm (U : V → C) (hU : U ∈ rootColourOffRows FX FY X Y v) :
      ham X U * (((Fintype.card V : ℝ) * Fintype.card C) * (hardStep FX X).w U) ≤ 1 := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hU).1
    have huv : u ≠ v := rootNeighbour_ne_root hu
    have hXu : X u = a := (h.agree_off_root u huv).trans
      ((mem_rootNeighbours.mp hu).2.trans h.X_root)
    have hc : Y v ≠ X u := by rw [h.Y_root, hXu]; exact h.colours_ne.symm
    rw [ham_comm X, ham_flip_eq_card hc]
    exact scaledMoveMass_size_bound FX X h.properX u (Y v) hc
  calc
    rootColourOffCharge FX FY X Y v ≤ ∑ _U ∈ rootColourOffRows FX FY X Y v, (1 : ℝ) :=
      Finset.sum_le_sum (fun U hU => hterm U hU)
    _ = (rootColourOffRows FX FY X Y v).card := by simp
    _ ≤ (rootNeighbours FY Y v a).card := by
      apply Nat.cast_le.mpr
      exact (Finset.card_filter_le _ _).trans (by
        simpa only [h.X_root] using Finset.card_image_le
          (s := rootNeighbours FY Y v (X v))
          (f := fun u => flipConfiguration X (flipSet FX.graph X u (Y v)) (X u) (Y v)))

lemma rootColourCharge_single_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hn : rootNeighbours FY Y v a = {u}) (hv : v ∉ flipSet FX.graph X u b)
    (hl : a ∈ FY.list v) : rootColourCharge FX FY X Y v ≤ 44 / 125 := by
  have hu : u ∈ rootNeighbours FY Y v a := by rw [hn]; simp
  have hXu : X u = a := (h.agree_off_root u (rootNeighbour_ne_root hu)).trans
    (mem_rootNeighbours.mp hu).2
  have hc : b ≠ X u := by rw [hXu]; exact h.colours_ne.symm
  simp only [rootColourCharge, rootColourOffCharge, rootColourOffRows_single h hn hv,
    Finset.sum_singleton, rootColourPartner_of_single h hn hv, h.X_root]
  rw [← root_colour_single_coalesces h hn hv, ham_self, ham_comm X, ham_flip_eq_card hc]
  change (↑(flipSet FX.graph X u b).card) * scaledMoveMass FX X u b +
      (0 - 1 - ↑(flipSet FX.graph X u b).card) * scaledMoveMass FY Y v a ≤ _
  have hb := root_colour_single_charge_le h hn hv hl
  linarith

lemma rootColourCharge_single_shared_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hn : rootNeighbours FY Y v a = {u}) (hv : v ∈ flipSet FX.graph X u b) :
    rootColourCharge FX FY X Y v ≤ 22 / 125 := by
  simpa only [rootColourCharge, rootColourOffCharge, rootColourOffRows_single_shared h hn hv,
    Finset.sum_empty, rootColourPartner_single_shared h hn hv, h.X_root, ham_self,
    sub_zero, zero_add] using root_colour_holding_charge_le h

lemma rootColourCharge_zero_neighbours
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hn : rootNeighbours FY Y v a = ∅) (hl : a ∈ FY.list v) :
    rootColourCharge FX FY X Y v = -1 := by
  have hset : flipSet FY.graph Y v a = {v} := by
    rw [root_flipSet_eq FY Y v a (by simpa only [h.Y_root] using h.colours_ne)]
    simp only [rootFamily, hn, Finset.image_empty, Finset.biUnion_empty, Finset.insert_empty]
  have hout : flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a = X := by
    funext w
    by_cases hw : w = v
    · subst w
      rw [flipConfiguration_at_start, h.X_root]
    · have hnw : w ∉ flipSet FY.graph Y v a := by simpa only [hset, Finset.mem_singleton] using hw
      rw [flipConfiguration_of_not_mem hnw]
      exact (h.agree_off_root w hw).symm
  have ha : flipAllowed FY (flipSet FY.graph Y v a)
      (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) := by
    intro w hw
    have hwv : w = v := by simpa only [hset, Finset.mem_singleton] using hw
    subst w
    rwa [flipConfiguration_at_start]
  have hrate : scaledMoveMass FY Y v a = 1 := by
    rw [scaledMoveMass_of_allowed FY Y v a
      (by simpa only [h.Y_root] using h.colours_ne) ha, hset, Finset.card_singleton]
    rfl
  have hpart : rootColourPartner FX FY X Y v = X :=
    rootColourPartner_of_card_ne_one FX FY X Y v (by simp only [h.X_root, hn, Finset.card_empty]; omega)
  simp only [rootColourCharge, rootColourOffCharge, rootColourOffRows, h.X_root, hn,
    Finset.image_empty, Finset.filter_empty, Finset.sum_empty, hpart, hout, hrate, ham_self]
  norm_num

theorem rootColourCharge_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    rootColourCharge FX FY X Y v ≤
      bulk * (rootNeighbours FY Y v a).card - (if a ∈ FY.list v then 1 else 0) := by
  unfold bulk
  by_cases hl : a ∈ FY.list v
  · rw [if_pos hl]
    by_cases hzero : (rootNeighbours FY Y v a).card = 0
    · have hn := Finset.card_eq_zero.mp hzero
      rw [rootColourCharge_zero_neighbours h hn hl, hzero]
      norm_num
    · by_cases hone : (rootNeighbours FY Y v a).card = 1
      · obtain ⟨u, hn⟩ := Finset.card_eq_one.mp hone
        rw [hone]
        by_cases hv : v ∈ flipSet FX.graph X u b
        · have hb := rootColourCharge_single_shared_le h hn hv
          norm_num
          linarith
        · have hb := rootColourCharge_single_le h hn hv hl
          norm_num
          linarith
      · have hpart : rootColourPartner FX FY X Y v = X :=
          rootColourPartner_of_card_ne_one FX FY X Y v (by simpa only [h.X_root] using hone)
        have hb := root_colour_holding_charge_le h
        have hoff := rootColourOffCharge_le_degree h
        have hn : (2 : ℝ) ≤ (rootNeighbours FY Y v a).card := by exact_mod_cast (show 2 ≤ (rootNeighbours FY Y v a).card by omega)
        simp only [rootColourCharge, hpart, ham_self, sub_zero, h.X_root]
        linarith
  · rw [if_neg hl, sub_zero]
    have ha : ¬ flipAllowed FY (flipSet FY.graph Y v a)
        (flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) := by
      intro ha
      have hv := ha v self_mem_flipSet
      rw [flipConfiguration_at_start] at hv
      exact hl hv
    simp only [rootColourCharge, h.X_root,
      scaledMoveMass_of_blocked FY Y h.properY v a ha, mul_zero, add_zero]
    have hoff := rootColourOffCharge_le_degree h
    have hn : 0 ≤ ((rootNeighbours FY Y v a).card : ℝ) := by positivity
    linarith


end
end ZeroFreeness.Appendix.CV
