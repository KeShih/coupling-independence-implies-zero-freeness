import ZeroFreeness.Coupling.CV.IncidenceRates
import ZeroFreeness.Coupling.CV.GlobalChoice
import ZeroFreeness.Coupling.Vigoda.HardPieceSums

/-! Exact canonical weighted residual sums on distinct actual output moves. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvPieceSumsDecEq : DecidableEq (V → C) := Classical.decEq _

lemma sum_weighted_share_image {J S : Type*} [Fintype J] [Fintype S]
    (f : J → S) (r a : S → ℝ) :
    (∑ i, a (f i) * CanonicalMatching.share f r i) =
      ∑ s ∈ Finset.univ.image f, a s * r s := by
  have hterm (i : J) : a (f i) * CanonicalMatching.share f r i =
      ∑ s ∈ Finset.univ.image f,
        if f i = s then a s * CanonicalMatching.share f r i else 0 := by
    rw [Finset.sum_eq_single (f i)]
    · simp
    · intro s _ hs
      rw [if_neg (Ne.symm hs)]
    · intro hi
      exact (hi (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).elim
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hfactor (i : J) :
      (if f i = s then a s * CanonicalMatching.share f r i else 0) =
      a s * (if f i = s then CanonicalMatching.share f r i else 0) := by
    split_ifs <;> simp
  simp_rw [hfactor]
  rw [← Finset.mul_sum, CanonicalMatching.sum_share_fibre]
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hs
  rw [if_pos ⟨i, hi⟩]

abbrev selectedRootPlan [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (c : C) :=
  regularRootPartial FX FY X Y v c (choice.left c) (choice.right c)

lemma selectedIncidenceRight_share [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.share (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan h choice c).rightResidual i =
    CanonicalMatching.share (componentOf FX X v c)
      (fun S => componentResidual FX X v c (choice.left c) S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) :=
  regularIncidenceRight_share h hca hcb (choice.left c) (choice.right c)
    (choice.left_mem c ⟨i.val, i.property⟩)
    (choice.right_mem c ((h.rootNeighbours_eq hca hcb) ▸ ⟨i.val, i.property⟩)) i

lemma selectedIncidenceLeft_share [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.share (regularIncidenceLeft FX X Y v c)
      (selectedRootPlan h choice c).leftResidual i =
    CanonicalMatching.share (oppositeComponentOf h hca hcb)
      (fun S => componentResidual FY Y v c (choice.right c) S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) :=
  regularIncidenceLeft_share h hca hcb (choice.left c) (choice.right c)
    (choice.left_mem c ⟨i.val, i.property⟩)
    (choice.right_mem c ((h.rootNeighbours_eq hca hcb) ▸ ⟨i.val, i.property⟩)) i

lemma selectedIncidence_atIncidence [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    CanonicalMatching.atIncidence (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)
      (selectedRootPlan h choice c).leftResidual (selectedRootPlan h choice c).rightResidual i =
    CanonicalMatching.atIncidence (componentOf FX X v c) (oppositeComponentOf h hca hcb)
      (fun S => componentResidual FX X v c (choice.left c) S.val)
      (fun S => componentResidual FY Y v c (choice.right c) S.val) i /
        ((Fintype.card V : ℝ) * Fintype.card C) :=
  regularIncidence_atIncidence h hca hcb (choice.left c) (choice.right c)
    (choice.left_mem c ⟨i.val, i.property⟩)
    (choice.right_mem c ((h.rootNeighbours_eq hca hcb) ▸ ⟨i.val, i.property⟩)) i

/-- Distinct actual Y outputs recover the scalar root-piece size sum. -/
theorem regularIncidenceRight_weightedResidual_sum [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b) :
    (∑ Z ∈ Finset.univ.image (regularIncidenceRight FX FY X Y v c),
      ham Y Z * (selectedRootPlan h choice c).rightResidual Z) =
    (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * componentResidual FX X v c (choice.left c) S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [← sum_weighted_share_image]
  simp_rw [regularIncidenceRight_ham h hca hcb, selectedIncidenceRight_share h choice hca hcb,
    ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  exact CanonicalMatching.sum_weighted_share (componentOf FX X v c)
    (componentOf_surjective FX X v c) (fun S => componentResidual FX X v c (choice.left c) S.val)
    (fun S => (S.val.card : ℝ))

/-- The analogous distinct-state sum for X-side off-root outputs. -/
theorem regularIncidenceLeft_weightedResidual_sum [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (hca : c ≠ a) (hcb : c ≠ b) :
    (∑ U ∈ Finset.univ.image (regularIncidenceLeft FX X Y v c),
      ham X U * (selectedRootPlan h choice c).leftResidual U) =
    (∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * componentResidual FY Y v c (choice.right c) S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [← sum_weighted_share_image]
  simp_rw [regularIncidenceLeft_ham h hca hcb, selectedIncidenceLeft_share h choice hca hcb,
    ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  exact CanonicalMatching.sum_weighted_share (oppositeComponentOf h hca hcb)
    (oppositeComponentOf_surjective h hca hcb) (fun S => componentResidual FY Y v c (choice.right c) S.val)
    (fun S => (S.val.card : ℝ))


end
end ZeroFreeness.Appendix.CV
