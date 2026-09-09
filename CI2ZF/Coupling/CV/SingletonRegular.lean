import CI2ZF.Coupling.CV.GlobalRegular
import CI2ZF.Coupling.CV.Rates
import CI2ZF.Coupling.Vigoda.HardSingletonRegular

/-! Actual full CV singleton matches for colours absent at the root neighbours. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvSingletonRegularDecEq : DecidableEq (V → C) := Classical.decEq _

lemma rootRate_of_no_neighbours (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (hN : rootNeighbours F X v c = ∅) :
    rootRate F X v c = if c ∈ F.list v then 1 else 0 := by
  have hallowed := root_flipAllowed_iff F X v c hc
  simp [rootFamily, hN] at hallowed
  unfold rootRate
  simp only [hallowed]
  rw [root_flipSet_singleton_of_no_neighbours F X v c hc hN, Finset.card_singleton]
  rfl

/-- The two actual singleton root moves have identical true transition rates. -/
lemma singleton_regular_mass [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : rootNeighbours FX X v c = ∅) :
    (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X v c) (X v) c) =
      (if c ∈ FX.list v then 1 else 0) / ((Fintype.card V : ℝ) * Fintype.card C) ∧
    (hardStep FY Y).w (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) =
      (if c ∈ FX.list v then 1 else 0) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hNY : rootNeighbours FY Y v c = ∅ := (h.rootNeighbours_eq hca hcb).symm.trans hN
  constructor
  · rw [hardStep_rootRate FX X h.properX v c (by rwa [h.X_root]),
      rootRate_of_no_neighbours FX X v c (by rwa [h.X_root]) hN]
  · rw [hardStep_rootRate FY Y h.properY v c (by rwa [h.Y_root]),
      rootRate_of_no_neighbours FY Y v c (by rwa [h.Y_root]) hNY]
    congr 1
    exact if_congr (h.root_list_regular_iff c hca hcb).symm rfl rfl

/-- The selected plan for a zero-neighbour regular colour matches the full
singleton mass; it does not leave a capacity inequality as an input. -/
theorem singletonRegularPartial_full [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (hN : rootNeighbours FX X v c = ∅) (U Z : V → C) :
    let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
    let SY := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
    (selectedRegularPartial h choice c).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z +
        if U = RX ∧ Z = SY then
          (if c ∈ FX.list v then 1 else 0) / ((Fintype.card V : ℝ) * Fintype.card C) else 0 := by
  dsimp only
  unfold selectedRegularPartial
  rw [if_neg (by simp [hN])]
  have hm := singleton_regular_mass h hca hcb hN
  have hfull := PartialCoupling.matchPointAtMost_full
    (hardCommonOffRootPartial FX FY X Y v)
    (flipConfiguration X (flipSet FX.graph X v c) (X v) c)
    (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c)
    ((hardStep FX X).w (flipConfiguration X (flipSet FX.graph X v c) (X v) c))
    ((hardStep FX X).nonneg _)
    (by rw [regular_root_common_leftResidual h hca])
    (by rw [regular_root_common_rightResidual h hcb, hm.1, hm.2]) U Z
  change (singletonRegularPartial FX FY X Y v c).w U Z = _
  change (singletonRegularPartial FX FY X Y v c).w U Z = _ at hfull
  rw [hfull, hm.1]


end
end CI2ZF.Appendix.CV
