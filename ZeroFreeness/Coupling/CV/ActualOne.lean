import ZeroFreeness.Coupling.CV.BranchEncoding

/-! The low-multiplicity certificate applied to actual one-neighbour graph
records, with the safety counts read directly from component sizes and lists. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def componentSafe11 (FX FY : HardListInstance V C) (X Y : V → C) (v u : V) (c : C) : ℕ :=
  if (offRootComponent FX X v (X v) c u).card = 1 ∧
    (offRootComponent FY Y v (Y v) c u).card = 1 ∧
    X v ∈ FX.list u ∧ Y v ∈ FY.list u then 1 else 0

def componentSafe12 (FX FY : HardListInstance V C) (X Y : V → C) (v u : V) (c : C) : ℕ :=
  if (((offRootComponent FX X v (X v) c u).card = 1 ∧
      (offRootComponent FY Y v (Y v) c u).card = 2) ∨
    ((offRootComponent FX X v (X v) c u).card = 2 ∧
      (offRootComponent FY Y v (Y v) c u).card = 1)) ∧
    X v ∈ FX.list u ∧ Y v ∈ FY.list u then 1 else 0

lemma componentBranch_safe11 (FX FY : HardListInstance V C) (X Y : V → C) (v u : V) (c : C)
    (hcX : c ≠ X v) (hcY : c ≠ Y v)
    (huX : u ∈ rootNeighbours FX X v c) (huY : u ∈ rootNeighbours FY Y v c) :
    safe11 (componentBranch FX X v c hcX u huX) (componentBranch FY Y v c hcY u huY) =
      componentSafe11 FX FY X Y v u c := by
  have hcap (r : ℕ) : min r 7 = 1 ↔ r = 1 := by omega
  obtain ⟨hsX, haX, _⟩ := componentBranch_spec FX X v c hcX u huX
  obtain ⟨hsY, haY, _⟩ := componentBranch_spec FY Y v c hcY u huY
  simp [safe11, componentSafe11, hsX, hsY, haX, haY, hcap, and_assoc]

lemma componentBranch_safe12 (FX FY : HardListInstance V C) (X Y : V → C) (v u : V) (c : C)
    (hcX : c ≠ X v) (hcY : c ≠ Y v)
    (huX : u ∈ rootNeighbours FX X v c) (huY : u ∈ rootNeighbours FY Y v c) :
    safe12 (componentBranch FX X v c hcX u huX) (componentBranch FY Y v c hcY u huY) =
      componentSafe12 FX FY X Y v u c := by
  have hcap1 (r : ℕ) : min r 7 = 1 ↔ r = 1 := by omega
  have hcap2 (r : ℕ) : min r 7 = 2 ↔ r = 2 := by omega
  obtain ⟨hsX, haX, _⟩ := componentBranch_spec FX X v c hcX u huX
  obtain ⟨hsY, haY, _⟩ := componentBranch_spec FY Y v c hcY u huY
  simp [safe12, componentSafe12, hsX, hsY, haX, haY, hcap1, hcap2, and_assoc]

lemma rootCharge_zero_single_neighbour (F : HardListInstance V C) (X : V → C)
    (v u : V) (c : C) (hc : c ≠ X v) (hN : rootNeighbours F X v c = {u}) :
    rootCharge F X v c u = 0 := by
  unfold rootCharge
  rw [root_flipSet_card_single_neighbour F X v u c hc hN]
  push_cast
  ring

lemma canonicalOffRootCharge_single_neighbour {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (u : V) (hN : rootNeighbours FX X v c = {u}) :
    canonicalOffRootCharge h hca hcb u u =
      (offRootComponent FX X v (X v) c u).card *
        componentResidual FX X v c u (offRootComponent FX X v (X v) c u) +
      (offRootComponent FY Y v (Y v) c u).card *
        componentResidual FY Y v c u (offRootComponent FY Y v (Y v) c u) -
      min (componentResidual FX X v c u (offRootComponent FX X v (X v) c u))
        (componentResidual FY Y v c u (offRootComponent FY Y v (Y v) c u)) := by
  let iu : RootIncidence FX X v c := ⟨u, by simp [hN]⟩
  have hall (i : RootIncidence FX X v c) : i = iu := by
    exact Subtype.ext (show i.val = u from by simpa [hN] using i.property)
  have hfirstX : CanonicalMatching.IsFirst (componentOf FX X v c) iu := by
    intro j _
    rw [hall j]
  have hfirstY : CanonicalMatching.IsFirst (oppositeComponentOf h hca hcb) iu := by
    intro j _
    rw [hall j]
  unfold canonicalOffRootCharge
  rw [CanonicalMatching.charge_as_incidence_sum _ _ (componentOf_surjective FX X v c)
    (oppositeComponentOf_surjective h hca hcb)]
  rw [Finset.sum_eq_single iu]
  · simp only [CanonicalMatching.atIncidence, CanonicalMatching.share,
      if_pos hfirstX, if_pos hfirstY]
    rfl
  · intro i _ hi
    exact (hi (hall i)).elim
  · simp

theorem canonicalColourCharge_eq_recordOne {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v) (u : V)
    (hNX : rootNeighbours FX X v c = {u}) :
    canonicalColourCharge h hca hcb u u =
      recordOne (componentBranch FX X v c (by rwa [h.X_root]) u (by simp [hNX]))
        (componentBranch FY Y v c (by rwa [h.Y_root]) u
          (by rw [← h.rootNeighbours_eq hca hcb, hNX]; simp)) := by
  have hNY : rootNeighbours FY Y v c = {u} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hcX : c ≠ X v := by rwa [h.X_root]
  have hcY : c ≠ Y v := by rwa [h.Y_root]
  have havY := (h.root_list_regular_iff c hca hcb).mp hav
  rw [canonicalColourCharge, if_pos (by rw [hNX]; exact Finset.singleton_nonempty _),
    rootCharge_zero_single_neighbour FX X v u c hcX hNX,
    rootCharge_zero_single_neighbour FY Y v u c hcY hNY, zero_add, zero_add,
    canonicalOffRootCharge_single_neighbour h hca hcb u hNX]
  unfold recordOne
  rw [componentBranch_oneResidual_cost FX X v c hcX hav u hNX,
    componentBranch_oneResidual_cost FY Y v c hcY havY u hNY,
    componentBranch_oneResidual FX X v c hcX hav u hNX,
    componentBranch_oneResidual FY Y v c hcY havY u hNY]

/-- The finite certificate now bounds the actual canonical graph charge for
one active root neighbour, with no abstract record or charge hypothesis. -/
theorem canonicalColourCharge_one_corrected {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v) (u : V)
    (hNX : rootNeighbours FX X v c = {u}) (gain loss : ℝ) :
    canonicalColourCharge h hca hcb u u + loss * componentSafe11 FX FY X Y v u c -
      gain * componentSafe12 FX FY X Y v u c ≤ -1 + low gain loss := by
  have hcX : c ≠ X v := by rwa [h.X_root]
  have hcY : c ≠ Y v := by rwa [h.Y_root]
  have huX : u ∈ rootNeighbours FX X v c := by simp [hNX]
  have huY : u ∈ rootNeighbours FY Y v c := by rw [← h.rootNeighbours_eq hca hcb]; exact huX
  have hb := recordOne_corrected (componentBranch FX X v c hcX u huX)
    (componentBranch FY Y v c hcY u huY) (componentBranch_pos FX X v c hcX u huX)
    (componentBranch_pos FY Y v c hcY u huY) gain loss
  rw [componentBranch_safe11, componentBranch_safe12] at hb
  rw [canonicalColourCharge_eq_recordOne h hca hcb hav u hNX]
  exact hb

end
end ZeroFreeness.Appendix.CV
