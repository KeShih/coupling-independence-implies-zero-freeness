import ZeroFreeness.Coupling.Vigoda.HardRegularAllocation
import ZeroFreeness.Coupling.Foundations.PartialCombining
import ZeroFreeness.Coupling.Vigoda.RegularColourCharge

/-! A single global partial coupling containing all regular-colour plans.
Disjointness is proved for actual output rows and columns, so the finite sum
of increments respects both hard-kernel marginals.
-/
namespace ZeroFreeness
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open RootComponentGeometry RegularColourCharge
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance globalRegularFunctionDecEq : DecidableEq (V → C) := Classical.decEq _

abbrev RegularColour (a b : C) := {c : C // c ≠ a ∧ c ≠ b}

/-- The empty-neighbour colour group matches the two true root recolourings. -/
def singletonRegularPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
  let SY := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
  (hardCommonOffRootPartial FX FY X Y v).matchPointAtMost RX SY
    ((hardStep FX X).w RX) ((hardStep FX X).nonneg RX)

/-- The prescribed plan for one actual regular colour, using largest
components selected from the two actual root-neighbour families. -/
def selectedRegularPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  if (rootNeighbours FX X v c).Nonempty then
    regularColourPartial FX FY X Y v c
      (selectedRepresentative FX X v c) (selectedRepresentative FY Y v c)
  else singletonRegularPartial FX FY X Y v c

lemma selectedRegularPartial_ge_common [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤
      (selectedRegularPartial FX FY X Y v c).w U Z := by
  unfold selectedRegularPartial
  split_ifs
  · exact regularColourPartial_ge_common _ _ _ _ _ _ _ _ _ _
  · change _ ≤ _ + if _ then _ else _
    apply le_add_of_nonneg_right
    split_ifs
    · exact le_min ((hardStep FX X).nonneg _)
        (le_min (PartialCoupling.leftResidual_nonneg _ _) (PartialCoupling.rightResidual_nonneg _ _))
    · exact le_rfl

lemma selectedRegularPartial_eq_common_off_rows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (U Z : V → C) (hU : U ∉ regularMoveRows FX X v b c) :
    (selectedRegularPartial FX FY X Y v c).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  unfold selectedRegularPartial
  split_ifs with hN
  · have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
    exact regularColourPartial_eq_common_off_rows h hca hcb _ _
      (selectedRepresentative_mem _ _ _ _ hN) (selectedRepresentative_mem _ _ _ _ hNY) U Z hU
  · have hne : U ≠ flipConfiguration X (flipSet FX.graph X v c) (X v) c := by
      intro heq
      exact hU ((mem_regularMoveRows FX X v b c U).mpr (Or.inl heq))
    simp [singletonRegularPartial, PartialCoupling.matchPointAtMost, PartialCoupling.addPoint, hne]

lemma selectedRegularPartial_eq_common_off_cols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (U Z : V → C) (hZ : Z ∉ regularMoveRows FY Y v a c) :
    (selectedRegularPartial FX FY X Y v c).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  unfold selectedRegularPartial
  split_ifs with hN
  · have hNY : (rootNeighbours FY Y v c).Nonempty := (h.rootNeighbours_eq hca hcb) ▸ hN
    exact regularColourPartial_eq_common_off_cols h hca hcb _ _
      (selectedRepresentative_mem _ _ _ _ hN) (selectedRepresentative_mem _ _ _ _ hNY) U Z hZ
  · have hne : Z ≠ flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c := by
      intro heq
      exact hZ ((mem_regularMoveRows FY Y v a c Z).mpr (Or.inl heq))
    simp [singletonRegularPartial, PartialCoupling.matchPointAtMost, PartialCoupling.addPoint, hne]

/-- Simultaneously combine every regular-colour plan with the common move
matching. All capacities follow from actual row/column disjointness. -/
def globalRegularPartial [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  PartialCoupling.combineDisjoint (hardCommonOffRootPartial FX FY X Y v)
    (fun c : RegularColour a b => selectedRegularPartial FX FY X Y v c.val)
    (fun c : RegularColour a b => regularMoveRows FX X v b c.val)
    (fun c : RegularColour a b => regularMoveRows FY Y v a c.val)
    (fun c => selectedRegularPartial_ge_common FX FY X Y v c.val)
    (fun c => selectedRegularPartial_eq_common_off_rows h c.property.1 c.property.2)
    (fun c => selectedRegularPartial_eq_common_off_cols h c.property.1 c.property.2)
    (fun c d hcd => regularMoveRows_disjoint h c.property.1 c.property.2
      d.property.1 d.property.2 (fun heq => hcd (Subtype.ext heq)))
    (fun c d hcd => regularMoveRows_disjoint h.symm c.property.2 c.property.1
      d.property.2 d.property.1 (fun heq => hcd (Subtype.ext heq)))

lemma globalRegularPartial_w [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C) :
    (globalRegularPartial h).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z +
      ∑ c : RegularColour a b,
        ((selectedRegularPartial FX FY X Y v c.val).w U Z -
          (hardCommonOffRootPartial FX FY X Y v).w U Z) := rfl

lemma globalRegularPartial_eq_common_off_rows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C)
    (hU : ∀ c : RegularColour a b, U ∉ regularMoveRows FX X v b c.val) :
    (globalRegularPartial h).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  rw [globalRegularPartial_w]
  have hz (c : RegularColour a b) :
      (selectedRegularPartial FX FY X Y v c.val).w U Z -
        (hardCommonOffRootPartial FX FY X Y v).w U Z = 0 := by
    rw [selectedRegularPartial_eq_common_off_rows h c.property.1 c.property.2 U Z (hU c), sub_self]
  simp only [hz, Finset.sum_const_zero, add_zero]

lemma globalRegularPartial_eq_common_off_cols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U Z : V → C)
    (hZ : ∀ c : RegularColour a b, Z ∉ regularMoveRows FY Y v a c.val) :
    (globalRegularPartial h).w U Z = (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  rw [globalRegularPartial_w]
  have hz (c : RegularColour a b) :
      (selectedRegularPartial FX FY X Y v c.val).w U Z -
        (hardCommonOffRootPartial FX FY X Y v).w U Z = 0 := by
    rw [selectedRegularPartial_eq_common_off_cols h c.property.1 c.property.2 U Z (hZ c), sub_self]
  simp only [hz, Finset.sum_const_zero, add_zero]

lemma globalRegularPartial_eq_selected_on_rows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (c : RegularColour a b) (U Z : V → C)
    (hU : U ∈ regularMoveRows FX X v b c.val) :
    (globalRegularPartial h).w U Z = (selectedRegularPartial FX FY X Y v c.val).w U Z := by
  rw [globalRegularPartial_w, Finset.sum_eq_single c]
  · ring
  · intro d _ hdc
    have hne : c.val ≠ d.val := fun hc => hdc (Subtype.ext hc.symm)
    have hUd : U ∉ regularMoveRows FX X v b d.val := fun hd =>
      (Finset.disjoint_left.mp (regularMoveRows_disjoint h c.property.1 c.property.2
        d.property.1 d.property.2 hne)) hU hd
    rw [selectedRegularPartial_eq_common_off_rows h d.property.1 d.property.2 U Z hUd, sub_self]
  · simp

lemma globalRegularPartial_eq_selected_on_cols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (c : RegularColour a b) (U Z : V → C)
    (hZ : Z ∈ regularMoveRows FY Y v a c.val) :
    (globalRegularPartial h).w U Z = (selectedRegularPartial FX FY X Y v c.val).w U Z := by
  rw [globalRegularPartial_w, Finset.sum_eq_single c]
  · ring
  · intro d _ hdc
    have hne : c.val ≠ d.val := fun hc => hdc (Subtype.ext hc.symm)
    have hZd : Z ∉ regularMoveRows FY Y v a d.val := fun hd =>
      (Finset.disjoint_left.mp (regularMoveRows_disjoint h.symm c.property.2 c.property.1
        d.property.2 d.property.1 hne)) hZ hd
    rw [selectedRegularPartial_eq_common_off_cols h d.property.1 d.property.2 U Z hZd, sub_self]
  · simp

/-- Proportional residual completion produces a genuine coupling of the
actual hard rows. Root-colour refinements may be inserted before completion. -/
def globalRegularCoupling [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) : Coupling (hardStep FX X) (hardStep FY Y) :=
  (globalRegularPartial h).complete

end
end ZeroFreeness
