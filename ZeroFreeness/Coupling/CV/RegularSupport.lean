import ZeroFreeness.Coupling.CV.GlobalChoice

/-! Actual row/column support of canonical CV colour plans. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvRegularSupportDecEq : DecidableEq (V → C) := Classical.decEq _

lemma canonicalRegularPartial_ge_common [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) (u w : V)
    (U Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z ≤
      (canonicalRegularPartial FX FY X Y v c u w).w U Z := by
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
  exact CanonicalMatching.matrix_nonneg _ _ _ _
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

lemma canonicalRegularPartial_eq_common_off_rows [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U Z : V → C) (hU : U ∉ regularMoveRows FX X v b c) :
    (canonicalRegularPartial FX FY X Y v c u w).w U Z =
      (hardCommonOffRootPartial FX FY X Y v).w U Z := by
  change (regularRootPartial FX FY X Y v c u w).w U Z + _ = _
  rw [regularRootPartial_eq_common_off_rows h hca hcb u w hu hw U Z hU]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro i _
  apply if_neg
  rintro ⟨heq, _⟩
  exact hU (heq ▸ regularIncidenceLeft_mem h i)

lemma canonicalRegularPartial_eq_common_off_cols [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u w : V) (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (U Z : V → C) (hZ : Z ∉ regularMoveRows FY Y v a c) :
    (canonicalRegularPartial FX FY X Y v c u w).w U Z =
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
end ZeroFreeness.Appendix.CV
