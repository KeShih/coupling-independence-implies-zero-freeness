import CI2ZF.Coupling.Vigoda.HardMoveSeparation
import CI2ZF.Coupling.Vigoda.HardMatchCost

/-! Concrete regular-colour plans: full root matches followed by incidence
matching on the exact residual transition capacities. -/
namespace CI2ZF
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance regularAllocationFunctionDecEq : DecidableEq (V → C) := Classical.decEq _

def regularIncidenceLeft (FX : HardListInstance V C) (X Y : V → C) (v : V) (c : C)
    (i : RootIncidence FX X v c) : V → C :=
  flipConfiguration X (flipSet FX.graph X i.val (Y v)) (X i.val) (Y v)

def regularIncidenceRight (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C)
    (i : RootIncidence FX X v c) : V → C :=
  flipConfiguration Y (flipSet FY.graph Y i.val (X v)) (Y i.val) (X v)

/-- This is a concrete partial coupling of the original hard rows; the
incidence matrix acts on actual output colourings and exact residuals. -/
def regularColourPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) (u w : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  (regularRootPartial FX FY X Y v c u w).matchResidualIncidences
    (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)

lemma regularIncidenceLeft_mem {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (i : RootIncidence FX X v c) :
    regularIncidenceLeft FX X Y v c i ∈ regularMoveRows FX X v b c := by
  apply (mem_regularMoveRows FX X v b c _).mpr
  right
  refine ⟨i.val, i.property, ?_⟩
  simp only [regularIncidenceLeft, h.Y_root]

lemma regularIncidenceRight_mem {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (i : RootIncidence FX X v c) :
    regularIncidenceRight FX FY X Y v c i ∈ regularMoveRows FY Y v a c := by
  apply (mem_regularMoveRows FY Y v a c _).mpr
  right
  refine ⟨i.val, (h.rootNeighbours_eq hca hcb) ▸ i.property, ?_⟩
  simp only [regularIncidenceRight, h.X_root]

/-- The actual two incidence moves share the physical neighbour, and
therefore save at least one over the two separate component-size charges. -/
theorem regularIncidence_ham_drift_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (i : RootIncidence FX X v c) :
    ham (regularIncidenceLeft FX X Y v c i) (regularIncidenceRight FX FY X Y v c i) - 1 ≤
      ((flipSet FX.graph X i.val (Y v)).card : ℝ) +
        (flipSet FY.graph Y i.val (X v)).card - 1 := by
  apply intersecting_moves_ham_drift_le h.agree_off_root
    (fun w hw => flipConfiguration_of_not_mem hw)
    (fun w hw => flipConfiguration_of_not_mem hw)
  exact ⟨i.val, Finset.mem_inter.mpr ⟨self_mem_flipSet, self_mem_flipSet⟩⟩

lemma regularColourPartial_ge_common [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) (u w : V)
    (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤
      (regularColourPartial FX FY X Y v c u w).w U Z := by
  have hpoint {mu nu : FinDist (V → C)} (k : PartialCoupling mu nu)
      (R S : V → C) (cap : ℝ) (hcap : 0 ≤ cap) :
      k.w U Z ≤ (k.matchPointAtMost R S cap hcap).w U Z := by
    change k.w U Z ≤ k.w U Z + if U = R ∧ Z = S then
      min cap (min (k.leftResidual R) (k.rightResidual S)) else 0
    apply le_add_of_nonneg_right
    split_ifs
    · exact le_min hcap (le_min (k.leftResidual_nonneg R) (k.rightResidual_nonneg S))
    · exact le_rfl
  apply (le_trans (hpoint _ _ _ _ _) (hpoint _ _ _ _ _)).trans
  change (regularRootPartial FX FY X Y v c u w).w U Z ≤
    (regularRootPartial FX FY X Y v c u w).w U Z + _
  apply le_add_of_nonneg_right
  exact IncidenceMatching.matrix_nonneg _ _ _ _
    (PartialCoupling.leftResidual_nonneg _) (PartialCoupling.rightResidual_nonneg _) U Z
  exact (hardStep FY Y).nonneg _

lemma regularRootPartial_eq_common_off_rows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U Z : V → C) (hU : U ∉ regularMoveRows FX X v b c) :
    (regularRootPartial FX FY X Y v c u w).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  have hr : U ≠ flipConfiguration X (flipSet FX.graph X v c) (X v) c := by
    intro hUeq
    exact hU ((mem_regularMoveRows FX X v b c U).mpr (Or.inl hUeq))
  have hd : U ≠ flipConfiguration X (flipSet FX.graph X w b) (X w) b := by
    intro hUeq
    have hwX : w ∈ rootNeighbours FX X v c := (h.rootNeighbours_eq hca hcb).symm ▸ hw
    exact hU ((mem_regularMoveRows FX X v b c U).mpr (Or.inr ⟨w, hwX, hUeq⟩))
  have heq := regularRootPartial_full h hca hcb u w hu hw U Z
  simpa only [hr, hd, false_and, if_false, add_zero] using heq

lemma regularRootPartial_eq_common_off_cols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U Z : V → C) (hZ : Z ∉ regularMoveRows FY Y v a c) :
    (regularRootPartial FX FY X Y v c u w).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  have hr : Z ≠ flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c := by
    intro hZeq
    exact hZ ((mem_regularMoveRows FY Y v a c Z).mpr (Or.inl hZeq))
  have hc : Z ≠ flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a := by
    intro hZeq
    have huY : u ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ hu
    exact hZ ((mem_regularMoveRows FY Y v a c Z).mpr (Or.inr ⟨u, huY, hZeq⟩))
  have heq := regularRootPartial_full h hca hcb u w hu hw U Z
  simpa only [hr, hc, and_false, if_false, add_zero] using heq

lemma regularColourPartial_eq_common_off_rows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U Z : V → C) (hU : U ∉ regularMoveRows FX X v b c) :
    (regularColourPartial FX FY X Y v c u w).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  change (regularRootPartial FX FY X Y v c u w).w U Z + _ = _
  rw [regularRootPartial_eq_common_off_rows h hca hcb u w hu hw U Z hU]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro i _
  apply if_neg
  rintro ⟨heq, _⟩
  exact hU (heq ▸ regularIncidenceLeft_mem h i)

lemma regularColourPartial_eq_common_off_cols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U Z : V → C) (hZ : Z ∉ regularMoveRows FY Y v a c) :
    (regularColourPartial FX FY X Y v c u w).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  change (regularRootPartial FX FY X Y v c u w).w U Z + _ = _
  rw [regularRootPartial_eq_common_off_cols h hca hcb u w hu hw U Z hZ]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro i _
  apply if_neg
  rintro ⟨_, heq⟩
  exact hZ (heq ▸ regularIncidenceRight_mem h hca hcb i)

end
end CI2ZF
