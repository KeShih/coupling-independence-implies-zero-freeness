import CI2ZF.Appendix.CV.DiscountFresh
import CI2ZF.Appendix.CV.IncidenceRates

/-! The actual canonical matching retains enough singleton mass to pay
for ordered-incidence output discounts. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvDiscountSingletonColouringDecEq : DecidableEq (V → C) := Classical.decEq _

lemma rootRate_le_mass_two_of_neighbour (F : HardListInstance V C) (X : V → C)
    (v u : V) (c : C) (hc : c ≠ X v) (hu : u ∈ rootNeighbours F X v c) :
    rootRate F X v c ≤ 81 / 250 := by
  classical
  have huv := rootNeighbour_ne_root hu
  have hum : u ∈ flipSet F.graph X v c := (mem_root_flipSet_iff hc).mpr
    (Or.inr ⟨u, hu, self_mem_offRootComponent F X v u (X v) c⟩)
  have hs : ({v, u} : Finset V) ⊆ flipSet F.graph X v c := by
    intro s hs
    rcases (show s = v ∨ s = u by simpa only [Finset.mem_insert, Finset.mem_singleton] using hs) with rfl | rfl
    · exact self_mem_flipSet
    · exact hum
  have hcard : 2 ≤ (flipSet F.graph X v c).card := by
    have hh := Finset.card_le_card hs
    simpa [huv.symm] using hh
  unfold rootRate
  split
  · exact (mass_antitone (by norm_num : 1 ≤ 2) hcard).trans_eq (by norm_num [mass])
  · norm_num

lemma singleton_componentResidual_lower
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hu : u ∈ rootNeighbours FX X v c) (uStar : V)
    (hsize : flipSet FY.graph Y u a = {u})
    (ha : flipAllowed FY (flipSet FY.graph Y u a)
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a)) :
    1 - 81 / 250 ≤ componentResidual FX X v c uStar (offRootComponent FX X v a c u) := by
  have hpiece := (h.offRoot_flipAllowed_iff hca hcb hu).mpr ha
  have hset := (h.offRootComponent_eq_opposite_flipSet hcb hu).trans hsize
  have hr := rootRate_le_mass_two_of_neighbour FX X v u c (by rwa [h.X_root]) hu
  have hp : pieceRate FX X v c (offRootComponent FX X v a c u) = 1 := by
    unfold pieceRate
    rw [h.X_root, if_pos hpiece, hset]
    simp [mass]
  unfold componentResidual
  rw [hp]
  split <;> linarith

lemma regularIncidenceLeft_first_singleton
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) (hi : flipSet FX.graph X i.val b = {i.val}) :
    CanonicalMatching.IsFirst (regularIncidenceLeft FX X Y v c) i := by
  intro j hj
  have houtput : regularIncidenceLeft FX X Y v c i = Function.update X i.val b := by
    simp only [regularIncidenceLeft, h.Y_root, hi, flipConfiguration_singleton]
  have heq : j = i := by
    apply Subtype.ext
    by_contra hn
    have hjAt : regularIncidenceLeft FX X Y v c j j.val = b := by
      simp only [regularIncidenceLeft, flipConfiguration_at_start, h.Y_root]
    rw [hj, houtput, Function.update_of_ne hn] at hjAt
    exact hcb ((mem_rootNeighbours.mp j.property).2.symm.trans hjAt)
  subst j
  rfl

lemma regularIncidenceRight_first_singleton
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a)
    (i : RootIncidence FX X v c) (hi : flipSet FY.graph Y i.val a = {i.val}) :
    CanonicalMatching.IsFirst (regularIncidenceRight FX FY X Y v c) i := by
  intro j hj
  have houtput : regularIncidenceRight FX FY X Y v c i = Function.update Y i.val a := by
    simp only [regularIncidenceRight, h.X_root, hi, flipConfiguration_singleton]
  have heq : j = i := by
    apply Subtype.ext
    by_contra hn
    have hjAt : regularIncidenceRight FX FY X Y v c j j.val = a := by
      simp only [regularIncidenceRight, flipConfiguration_at_start, h.X_root]
    rw [hj, houtput, Function.update_of_ne hn] at hjAt
    have hYj : Y j.val = c := (h.agree_off_root j.val (rootNeighbour_ne_root j.property)).symm.trans
      (mem_rootNeighbours.mp j.property).2
    exact hca (hYj.symm.trans hjAt)
  subst j
  rfl

/-- After all root and common allocations, the singleton cross pair is
present with mass at least `(1-P₂)/(nq)` in the final coupling. -/
theorem fullHardCoupling_singleton_cross_lower [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hu : u ∈ rootNeighbours FX X v c)
    (hsizeX : flipSet FX.graph X u b = {u})
    (hsizeY : flipSet FY.graph Y u a = {u})
    (haX : flipAllowed FX (flipSet FX.graph X u b)
      (flipConfiguration X (flipSet FX.graph X u b) (X u) b))
    (haY : flipAllowed FY (flipSet FY.graph Y u a)
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a)) :
    (1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) ≤
      (fullHardCoupling h choice).w (Function.update X u b) (Function.update Y u a) := by
  let i : RootIncidence FX X v c := ⟨u, hu⟩
  let κ := regularRootPartial FX FY X Y v c (choice.left c) (choice.right c)
  let f := regularIncidenceLeft FX X Y v c
  let g := regularIncidenceRight FX FY X Y v c
  have hN : (rootNeighbours FX X v c).Nonempty := ⟨u, hu⟩
  have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
  have huY : u ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ hu
  have hf : f i = Function.update X u b := by
    simp only [f, regularIncidenceLeft, i, h.Y_root, hsizeX, flipConfiguration_singleton]
  have hg : g i = Function.update Y u a := by
    simp only [g, regularIncidenceRight, i, h.X_root, hsizeY, flipConfiguration_singleton]
  have hl : (1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) ≤ κ.leftResidual (f i) := by
    have hh := rootPartial_leftResidual h hca hcb (choice.left c) (choice.right c)
      (choice.left_mem c hN) (choice.right_mem c hNY) u huY
    change _ ≤ (regularRootPartial FX FY X Y v c (choice.left c) (choice.right c)).leftResidual _
    simp only [f, regularIncidenceLeft, i, h.Y_root]
    rw [hh]
    exact div_le_div_of_nonneg_right
      (singleton_componentResidual_lower h.symm hcb hca huY _ hsizeX haX) (by positivity)
  have hr : (1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) ≤ κ.rightResidual (g i) := by
    have hh := rootPartial_rightResidual h hca hcb (choice.left c) (choice.right c)
      (choice.left_mem c hN) (choice.right_mem c hNY) u hu
    change _ ≤ (regularRootPartial FX FY X Y v c (choice.left c) (choice.right c)).rightResidual _
    simp only [g, regularIncidenceRight, i, h.X_root]
    rw [hh]
    exact div_le_div_of_nonneg_right
      (singleton_componentResidual_lower h hca hcb hu _ hsizeY haY) (by positivity)
  have hfirstL := regularIncidenceLeft_first_singleton h hcb i hsizeX
  have hfirstR := regularIncidenceRight_first_singleton h hca i hsizeY
  have hmin : (1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) ≤
      CanonicalMatching.atIncidence f g κ.leftResidual κ.rightResidual i := by
    unfold CanonicalMatching.atIncidence CanonicalMatching.share
    rw [if_pos hfirstL, if_pos hfirstR]
    exact le_min hl hr
  have hm : CanonicalMatching.atIncidence f g κ.leftResidual κ.rightResidual i ≤
      CanonicalMatching.matrix f g κ.leftResidual κ.rightResidual (f i) (g i) := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if f j = f i ∧ g j = g i then
        CanonicalMatching.atIncidence f g κ.leftResidual κ.rightResidual j else 0)
      (fun j _ => by
        split_ifs
        · exact CanonicalMatching.atIncidence_nonneg f g _ _
            κ.leftResidual_nonneg κ.rightResidual_nonneg j
        · rfl) (Finset.mem_univ i)
    simpa only [CanonicalMatching.matrix, and_self, if_true] using hh
  have hmatrix : CanonicalMatching.matrix f g κ.leftResidual κ.rightResidual (f i) (g i) ≤
      (canonicalRegularPartial FX FY X Y v c (choice.left c) (choice.right c)).w (f i) (g i) := by
    change _ ≤ κ.w (f i) (g i) + _
    exact le_add_of_nonneg_left (κ.nonneg (f i) (g i))
  have hall := fullHardCoupling_dominate_canonical h choice ⟨c, hca, hcb⟩ hN (f i) (g i)
  simpa only [hf, hg] using hmin.trans (hm.trans (hmatrix.trans hall))

end
end CI2ZF.Appendix.CV
