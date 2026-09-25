import ZeroFreeness.Coupling.Vigoda.HardIncidenceRates

/-! Exact weighted sums on the actual image of incidence moves, without
counting a component twice when it meets several root neighbours. -/
namespace ZeroFreeness
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open RootComponentGeometry RegularColourCharge
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance pieceSumsFunctionDecEq : DecidableEq (V → C) := Classical.decEq _

lemma sum_weighted_share_image {J S : Type*} [Fintype J] [Fintype S]
    (f : J → S) (r a : S → ℝ) :
    (∑ i, a (f i) * IncidenceMatching.share f r i) =
      ∑ s ∈ Finset.univ.image f, a s * r s := by
  have hterm (i : J) : a (f i) * IncidenceMatching.share f r i =
      ∑ s ∈ Finset.univ.image f,
        if f i = s then a s * IncidenceMatching.share f r i else 0 := by
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
      (if f i = s then a s * IncidenceMatching.share f r i else 0) =
      a s * (if f i = s then IncidenceMatching.share f r i else 0) := by
    split_ifs <;> simp
  simp_rw [hfactor]
  rw [← Finset.mul_sum, IncidenceMatching.sum_share_fibre]
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hs
  have hn : (IncidenceMatching.count f s : ℝ) ≠ 0 := by
    rw [← hi]
    exact_mod_cast (IncidenceMatching.count_pos f i).ne'
  field_simp

lemma regularIncidenceRight_ham
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    ham Y (regularIncidenceRight FX FY X Y v c i) =
      ((componentOf FX X v c i).val.card : ℝ) := by
  have hic : Y i.val = c := (h.agree_off_root i.val (rootNeighbour_ne_root i.property)).symm.trans
    (mem_rootNeighbours.mp i.property).2
  unfold regularIncidenceRight
  rw [h.X_root, ham_comm, ham_flip_eq_card (by rw [hic]; exact hca.symm)]
  have hs := h.offRootComponent_eq_opposite_flipSet hcb i.property
  simpa only [componentOf, h.X_root] using congrArg (fun S : Finset V => (S.card : ℝ)) hs.symm

lemma regularIncidenceLeft_ham
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (i : RootIncidence FX X v c) :
    ham X (regularIncidenceLeft FX X Y v c i) =
      ((oppositeComponentOf h hca hcb i).val.card : ℝ) := by
  have hi : i.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ i.property
  have hic : X i.val = c := (mem_rootNeighbours.mp i.property).2
  unfold regularIncidenceLeft
  rw [h.Y_root, ham_comm, ham_flip_eq_card (by rw [hic]; exact hcb.symm)]
  have hs := h.symm.offRootComponent_eq_opposite_flipSet hca hi
  simpa only [oppositeComponentOf, rootIncidenceEquiv, componentOf,
    Equiv.subtypeEquivRight_apply_coe, h.Y_root] using congrArg (fun S : Finset V => (S.card : ℝ)) hs.symm

/-- Distinct actual Y outputs recover the scalar root-piece size sum. -/
theorem regularIncidenceRight_weightedResidual_sum [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    (∑ Z ∈ Finset.univ.image (regularIncidenceRight FX FY X Y v c),
      ham Y Z * (selectedRootPlan FX FY X Y v c).rightResidual Z) =
    (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * RegularColourCharge.residual FX X v c S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [← sum_weighted_share_image]
  simp_rw [regularIncidenceRight_ham h hca hcb, regularIncidenceRight_share h hca hcb,
    ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  exact IncidenceMatching.sum_weighted_share (componentOf FX X v c)
    (componentOf_surjective FX X v c) (fun S => RegularColourCharge.residual FX X v c S.val)
    (fun S => (S.val.card : ℝ))

/-- The analogous distinct-state sum for X-side off-root outputs. -/
theorem regularIncidenceLeft_weightedResidual_sum [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    (∑ U ∈ Finset.univ.image (regularIncidenceLeft FX X Y v c),
      ham X U * (selectedRootPlan FX FY X Y v c).leftResidual U) =
    (∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * RegularColourCharge.residual FY Y v c S.val) /
      ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [← sum_weighted_share_image]
  simp_rw [regularIncidenceLeft_ham h hca hcb, regularIncidenceLeft_share h hca hcb,
    ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  exact IncidenceMatching.sum_weighted_share (oppositeComponentOf h hca hcb)
    (oppositeComponentOf_surjective h hca hcb) (fun S => RegularColourCharge.residual FY Y v c S.val)
    (fun S => (S.val.card : ℝ))

end
end ZeroFreeness
