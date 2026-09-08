import CI2ZF.Appendix.CVCanonical
import CI2ZF.Appendix.CVRootAllocation
import CI2ZF.HardGlobalCost

/-! Canonical residual matching on the actual CV root-matched rows. Each
repeated component contributes its full residual at its first incidence;
completion preserves the resulting Hamming savings. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

namespace CanonicalMatching
variable {I S T : Type*} [Fintype I] [Fintype S] [Fintype T]
variable {mu : FinDist S} {nu : FinDist T}

/-- Add canonical matches in the exact unused capacities of an existing plan. -/
def extend (κ : PartialCoupling mu nu) (f : I → S) (g : I → T) : PartialCoupling mu nu where
  w x y := κ.w x y + matrix f g κ.leftResidual κ.rightResidual x y
  nonneg x y := add_nonneg (κ.nonneg x y)
    (matrix_nonneg f g _ _ κ.leftResidual_nonneg κ.rightResidual_nonneg x y)
  row_le x := by
    rw [Finset.sum_add_distrib]
    have h := matrix_row_le f g κ.leftResidual κ.rightResidual κ.leftResidual_nonneg x
    change (∑ y, matrix f g κ.leftResidual κ.rightResidual x y) ≤ mu.w x - ∑ y, κ.w x y at h
    linarith
  col_le y := by
    rw [Finset.sum_add_distrib]
    have h := matrix_col_le f g κ.leftResidual κ.rightResidual κ.rightResidual_nonneg y
    change (∑ x, matrix f g κ.leftResidual κ.rightResidual x y) ≤ nu.w y - ∑ x, κ.w x y at h
    linarith

lemma extend_ge (κ : PartialCoupling mu nu) (f : I → S) (g : I → T) (x : S) (y : T) :
    κ.w x y ≤ (extend κ f g).w x y := by
  apply le_add_of_nonneg_right
  exact matrix_nonneg f g _ _ κ.leftResidual_nonneg κ.rightResidual_nonneg x y

lemma extend_cost (κ : PartialCoupling mu nu) (f : I → S) (g : I → T) (d : S → T → ℝ) :
    (extend κ f g).cost d = κ.cost d +
      ∑ i, atIncidence f g κ.leftResidual κ.rightResidual i * d (f i) (g i) := by
  simp only [PartialCoupling.cost, extend, add_mul, Finset.sum_add_distrib]
  rw [matrix_weighted_sum]

lemma separable_account (κ : PartialCoupling mu nu) (a : S → ℝ) (b : T → ℝ) :
    κ.cost (fun x y => a x + b y) + (∑ x, κ.leftResidual x * a x) +
      (∑ y, κ.rightResidual y * b y) = (∑ x, mu.w x * a x) + (∑ y, nu.w y * b y) := by
  have hleft : (∑ x, ∑ y, κ.w x y * a x) = ∑ x, (∑ y, κ.w x y) * a x := by
    simp_rw [Finset.sum_mul]
  have hright : (∑ x, ∑ y, κ.w x y * b y) = ∑ y, (∑ x, κ.w x y) * b y := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  simp only [PartialCoupling.cost, mul_add, Finset.sum_add_distrib,
    PartialCoupling.leftResidual, PartialCoupling.rightResidual, sub_mul, Finset.sum_sub_distrib]
  rw [hleft, hright]
  ring

/-- The base plan's already earned savings and every canonical same-incidence
saving survive the actual product completion. -/
theorem extend_complete_cost_le (κ : PartialCoupling mu nu) (f : I → S) (g : I → T)
    (d : S → T → ℝ) (a : S → ℝ) (b : T → ℝ) (saving : I → ℝ)
    (hd : ∀ x y, d x y ≤ a x + b y)
    (hmatch : ∀ i, d (f i) (g i) ≤ a (f i) + b (g i) - saving i) :
    (extend κ f g).complete.cost d ≤ κ.cost d +
      (∑ x, κ.leftResidual x * a x) + (∑ y, κ.rightResidual y * b y) -
      ∑ i, atIncidence f g κ.leftResidual κ.rightResidual i * saving i := by
  have hcost : (extend κ f g).cost d - κ.cost d ≤
      (extend κ f g).cost (fun x y => a x + b y) - κ.cost (fun x y => a x + b y) -
      ∑ i, atIncidence f g κ.leftResidual κ.rightResidual i * saving i := by
    rw [extend_cost, extend_cost]
    simp only [add_sub_cancel_left, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_sub] using mul_le_mul_of_nonneg_left (hmatch i)
      (atIncidence_nonneg f g _ _ κ.leftResidual_nonneg κ.rightResidual_nonneg i)
  have hcomplete := (extend κ f g).complete_cost_le_separable d a b hd
  have ha := separable_account κ a b
  have hb := separable_account (extend κ f g) a b
  linarith

end CanonicalMatching

variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvCanonicalColouringDecidableEq : DecidableEq (V → C) := Classical.decEq _

/-- The CV residual rule following the two full regular root matches. -/
def canonicalRegularPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) (u w : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  CanonicalMatching.extend (regularRootPartial FX FY X Y v c u w)
    (regularIncidenceLeft FX X Y v c) (regularIncidenceRight FX FY X Y v c)

/-- A genuine coupling of the actual CV transition rows. -/
def canonicalRegularCoupling [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) (u w : V) :
    Coupling (hardStep FX X) (hardStep FY Y) :=
  (canonicalRegularPartial FX FY X Y v c u w).complete

lemma canonical_incidence_cost {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (i : RootIncidence FX X v c) :
    hamDrift (regularIncidenceLeft FX X Y v c i) (regularIncidenceRight FX FY X Y v c i) ≤
      ham X (regularIncidenceLeft FX X Y v c i) +
      ham Y (regularIncidenceRight FX FY X Y v c i) - 1 := by
  have hxi : X i.val = c := (mem_rootNeighbours.mp i.property).2
  have hyi : Y i.val = c := (h.agree_off_root i.val (rootNeighbour_ne_root i.property)).symm.trans hxi
  unfold regularIncidenceLeft regularIncidenceRight hamDrift
  rw [ham_comm X, ham_comm Y, ham_flip_eq_card (by rw [h.Y_root, hxi]; exact hcb.symm),
    ham_flip_eq_card (by rw [h.X_root, hyi]; exact hca.symm)]
  apply intersecting_moves_ham_drift_le h.agree_off_root
  · intro z hz; exact flipConfiguration_of_not_mem hz
  · intro z hz; exact flipConfiguration_of_not_mem hz
  · exact ⟨i.val, Finset.mem_inter.mpr ⟨self_mem_flipSet, self_mem_flipSet⟩⟩

/-- Graph-level Hamming cost for canonical matching, before the remaining
colour groups are assembled. The saving is derived from actual intersecting
flip sets rather than supplied as a cost assumption. -/
theorem canonicalRegularCoupling_cost [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) (u w : V) :
    (canonicalRegularCoupling FX FY X Y v c u w).cost ham - 1 ≤
      (regularRootPartial FX FY X Y v c u w).cost hamDrift +
      (∑ U, (regularRootPartial FX FY X Y v c u w).leftResidual U * ham X U) +
      (∑ Z, (regularRootPartial FX FY X Y v c u w).rightResidual Z * ham Y Z) -
      ∑ i : RootIncidence FX X v c,
        CanonicalMatching.atIncidence (regularIncidenceLeft FX X Y v c)
          (regularIncidenceRight FX FY X Y v c)
          (regularRootPartial FX FY X Y v c u w).leftResidual
          (regularRootPartial FX FY X Y v c u w).rightResidual i := by
  rw [← coupling_hamDrift_cost]
  apply (CanonicalMatching.extend_complete_cost_le _ _ _ hamDrift (ham X) (ham Y) (fun _ => 1)
    (hamDrift_le_moves (rootLocal_ham_one h)) (canonical_incidence_cost h hca hcb)).trans_eq
  simp

end
end CI2ZF.Appendix.CV
