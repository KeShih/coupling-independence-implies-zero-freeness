import CI2ZF.HardRegularRates
import CI2ZF.HardRegularAllocation

/-! Exact equality between state-level incidence allocations and the
component-indexed residual masses used in the scalar charge certificate. -/
namespace CI2ZF
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open RootComponentGeometry RegularColourCharge
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance incidenceRatesFunctionDecEq : DecidableEq (V → C) := Classical.decEq _

lemma regularIncidenceRight_count
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    IncidenceMatching.count (regularIncidenceRight FX FY X Y v c)
      (regularIncidenceRight FX FY X Y v c i) =
    IncidenceMatching.count (componentOf FX X v c) (componentOf FX X v c i) := by
  unfold IncidenceMatching.count
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have heq := opposite_output_eq_iff_piece_eq h hca hcb j.val i.val j.property i.property
  simpa [regularIncidenceRight, componentOf, h.X_root] using heq

lemma regularIncidenceLeft_count
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    IncidenceMatching.count (regularIncidenceLeft FX X Y v c)
      (regularIncidenceLeft FX X Y v c i) =
    IncidenceMatching.count (oppositeComponentOf h hca hcb) (oppositeComponentOf h hca hcb i) := by
  unfold IncidenceMatching.count
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hj : j.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ j.property
  have hi : i.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ i.property
  have heq := opposite_output_eq_iff_piece_eq h.symm hcb hca j.val i.val hj hi
  simpa [regularIncidenceLeft, oppositeComponentOf, rootIncidenceEquiv, componentOf, h.Y_root] using heq

abbrev selectedRootPlan [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) :=
  regularRootPartial FX FY X Y v c
    (selectedRepresentative FX X v c) (selectedRepresentative FY Y v c)

lemma regularIncidenceRight_residual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    (selectedRootPlan FX FY X Y v c).rightResidual (regularIncidenceRight FX FY X Y v c i) =
      RegularColourCharge.residual FX X v c (componentOf FX X v c i).val /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hr := selectedRootPartial_rightResidual h hca hcb i.val i.property
  simpa only [regularIncidenceRight, componentOf, h.X_root] using hr

lemma regularIncidenceLeft_residual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    (selectedRootPlan FX FY X Y v c).leftResidual (regularIncidenceLeft FX X Y v c i) =
      RegularColourCharge.residual FY Y v c (oppositeComponentOf h hca hcb i).val /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hi : i.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ i.property
  have hr := selectedRootPartial_leftResidual h hca hcb i.val hi
  simpa only [regularIncidenceLeft, oppositeComponentOf, rootIncidenceEquiv,
    componentOf, Equiv.subtypeEquivRight_apply_coe, h.Y_root] using hr

lemma regularIncidenceRight_share [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    IncidenceMatching.share (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan FX FY X Y v c).rightResidual i =
    IncidenceMatching.share (componentOf FX X v c)
      (fun S => RegularColourCharge.residual FX X v c S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold IncidenceMatching.share
  rw [regularIncidenceRight_residual h hca hcb i, regularIncidenceRight_count h hca hcb i]
  simp only [div_eq_mul_inv]
  ring

lemma regularIncidenceLeft_share [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    IncidenceMatching.share (regularIncidenceLeft FX X Y v c)
      (selectedRootPlan FX FY X Y v c).leftResidual i =
    IncidenceMatching.share (oppositeComponentOf h hca hcb)
      (fun S => RegularColourCharge.residual FY Y v c S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold IncidenceMatching.share
  rw [regularIncidenceLeft_residual h hca hcb i, regularIncidenceLeft_count h hca hcb i]
  simp only [div_eq_mul_inv]
  ring

/-- The exact actual matching mass at each physical incidence agrees with
the scalar allocation, including multiplicities and blocked components. -/
theorem regularIncidence_atIncidence [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    IncidenceMatching.atIncidence
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan FX FY X Y v c).leftResidual
      (selectedRootPlan FX FY X Y v c).rightResidual i =
    IncidenceMatching.atIncidence (componentOf FX X v c) (oppositeComponentOf h hca hcb)
      (fun S => RegularColourCharge.residual FX X v c S.val)
      (fun S => RegularColourCharge.residual FY Y v c S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold IncidenceMatching.atIncidence
  rw [regularIncidenceLeft_share h hca hcb i, regularIncidenceRight_share h hca hcb i,
    min_div_div_right (by positivity), min_comm]

end
end CI2ZF
