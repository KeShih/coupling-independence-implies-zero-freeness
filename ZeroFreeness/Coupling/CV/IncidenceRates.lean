import ZeroFreeness.Coupling.CV.Rates

/-! Exact scaling of canonical incidence allocations from actual CV kernel
rows to component residuals. The first-incidence predicates agree because
actual off-root outputs identify precisely the same component fibres. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvIncidenceRatesColouringDecEq : DecidableEq (V → C) := Classical.decEq _

lemma regularIncidenceRight_first
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.IsFirst (regularIncidenceRight FX FY X Y v c) i ↔
      CanonicalMatching.IsFirst (componentOf FX X v c) i := by
  unfold CanonicalMatching.IsFirst
  apply forall_congr'
  intro j
  have heq := opposite_output_eq_iff_piece_eq h hca hcb j.val i.val j.property i.property
  have heq' : regularIncidenceRight FX FY X Y v c j = regularIncidenceRight FX FY X Y v c i ↔
      componentOf FX X v c j = componentOf FX X v c i := by
    simpa [regularIncidenceRight, componentOf, h.X_root] using heq
  rw [heq']

lemma regularIncidenceLeft_first
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.IsFirst (regularIncidenceLeft FX X Y v c) i ↔
      CanonicalMatching.IsFirst (oppositeComponentOf h hca hcb) i := by
  unfold CanonicalMatching.IsFirst
  apply forall_congr'
  intro j
  have hj : j.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ j.property
  have hi : i.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ i.property
  have heq := opposite_output_eq_iff_piece_eq h.symm hcb hca j.val i.val hj hi
  have heq' : regularIncidenceLeft FX X Y v c j = regularIncidenceLeft FX X Y v c i ↔
      oppositeComponentOf h hca hcb j = oppositeComponentOf h hca hcb i := by
    simpa [regularIncidenceLeft, oppositeComponentOf, rootIncidenceEquiv, componentOf,
      h.Y_root] using heq
  rw [heq']

lemma regularIncidenceRight_residual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (uStar wStar : V) (huStar : uStar ∈ rootNeighbours FX X v c)
    (hwStar : wStar ∈ rootNeighbours FY Y v c)
    (i : RootIncidence FX X v c) :
    (regularRootPartial FX FY X Y v c uStar wStar).rightResidual
      (regularIncidenceRight FX FY X Y v c i) =
      componentResidual FX X v c uStar (componentOf FX X v c i).val /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hr := rootPartial_rightResidual h hca hcb uStar wStar huStar hwStar i.val i.property
  simpa only [regularIncidenceRight, componentOf, h.X_root] using hr

lemma regularIncidenceLeft_residual [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (uStar wStar : V) (huStar : uStar ∈ rootNeighbours FX X v c)
    (hwStar : wStar ∈ rootNeighbours FY Y v c)
    (i : RootIncidence FX X v c) :
    (regularRootPartial FX FY X Y v c uStar wStar).leftResidual
      (regularIncidenceLeft FX X Y v c i) =
      componentResidual FY Y v c wStar (oppositeComponentOf h hca hcb i).val /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hi : i.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ i.property
  have hr := rootPartial_leftResidual h hca hcb uStar wStar huStar hwStar i.val hi
  simpa only [regularIncidenceLeft, oppositeComponentOf, rootIncidenceEquiv,
    componentOf, Equiv.subtypeEquivRight_apply_coe, h.Y_root] using hr

lemma regularIncidenceRight_share [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (uStar wStar : V) (huStar : uStar ∈ rootNeighbours FX X v c)
    (hwStar : wStar ∈ rootNeighbours FY Y v c)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.share (regularIncidenceRight FX FY X Y v c)
      (regularRootPartial FX FY X Y v c uStar wStar).rightResidual i =
    CanonicalMatching.share (componentOf FX X v c)
      (fun S => componentResidual FX X v c uStar S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold CanonicalMatching.share
  rw [regularIncidenceRight_first h hca hcb i,
    regularIncidenceRight_residual h hca hcb uStar wStar huStar hwStar i]
  split_ifs <;> simp

lemma regularIncidenceLeft_share [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (uStar wStar : V) (huStar : uStar ∈ rootNeighbours FX X v c)
    (hwStar : wStar ∈ rootNeighbours FY Y v c)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.share (regularIncidenceLeft FX X Y v c)
      (regularRootPartial FX FY X Y v c uStar wStar).leftResidual i =
    CanonicalMatching.share (oppositeComponentOf h hca hcb)
      (fun S => componentResidual FY Y v c wStar S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold CanonicalMatching.share
  rw [regularIncidenceLeft_first h hca hcb i,
    regularIncidenceLeft_residual h hca hcb uStar wStar huStar hwStar i]
  split_ifs <;> simp

/-- The matching probability at every physical incidence is exactly the
canonical scalar residual minimum, with the proposal normalization. -/
theorem regularIncidence_atIncidence [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (uStar wStar : V) (huStar : uStar ∈ rootNeighbours FX X v c)
    (hwStar : wStar ∈ rootNeighbours FY Y v c)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.atIncidence
      (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (regularRootPartial FX FY X Y v c uStar wStar).leftResidual
      (regularRootPartial FX FY X Y v c uStar wStar).rightResidual i =
    CanonicalMatching.atIncidence (componentOf FX X v c) (oppositeComponentOf h hca hcb)
      (fun S => componentResidual FX X v c uStar S.val)
      (fun S => componentResidual FY Y v c wStar S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold CanonicalMatching.atIncidence
  rw [regularIncidenceLeft_share h hca hcb uStar wStar huStar hwStar i,
    regularIncidenceRight_share h hca hcb uStar wStar huStar hwStar i,
    min_div_div_right (by positivity), min_comm]

end
end ZeroFreeness.Appendix.CV
