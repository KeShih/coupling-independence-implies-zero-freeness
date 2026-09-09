import CI2ZF.Coupling.Vigoda.HardGlobalRegular
import CI2ZF.Coupling.Vigoda.HardFlipBoundary

/-!
# Global cost accounting for the actual hard coupling

The completion charge includes the exact cost of the matched mass and
separate move-size charges on the two unmatched marginals. This charge is
affine in the partial matching matrix, so all local savings survive a
simultaneous global assembly and residual completion.
-/

namespace CI2ZF

open PottsCI PottsCI.FinDist PottsCI.Vigoda
open RootComponentGeometry RegularColourCharge
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section

namespace PartialCoupling

variable {S T K : Type*} [Fintype S] [Fintype T]
variable {μ : FinDist S} {ν : FinDist T}

/-- Marginal move charges plus the correction for mass already matched. -/
def completionCharge (κ : PartialCoupling μ ν) (d : S → T → ℝ)
    (a : S → ℝ) (b : T → ℝ) : ℝ :=
  (∑ x, μ.w x * a x) + (∑ y, ν.w y * b y) +
    κ.cost (fun x y => d x y - a x - b y)

/-- The charge is exactly matched cost plus the two residual-size sums. -/
theorem completionCharge_eq (κ : PartialCoupling μ ν) (d : S → T → ℝ)
    (a : S → ℝ) (b : T → ℝ) :
    κ.completionCharge d a b = κ.cost d +
      (∑ x, κ.leftResidual x * a x) + (∑ y, κ.rightResidual y * b y) := by
  have hleft : (∑ x, ∑ y, κ.w x y * a x) = ∑ x, (∑ y, κ.w x y) * a x := by
    simp_rw [Finset.sum_mul]
  have hright : (∑ x, ∑ y, κ.w x y * b y) = ∑ y, (∑ x, κ.w x y) * b y := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  unfold completionCharge cost leftResidual rightResidual
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [hleft, hright]
  ring

/-- Product completion preserves every saving recorded in the charge. -/
theorem complete_cost_le_completionCharge (κ : PartialCoupling μ ν)
    (d : S → T → ℝ) (a : S → ℝ) (b : T → ℝ)
    (hd : ∀ x y, d x y ≤ a x + b y) :
    κ.complete.cost d ≤ κ.completionCharge d a b := by
  rw [completionCharge_eq]
  exact κ.complete_cost_le_separable d a b hd

/-- Cost is affine under any specified matrix increment. -/
theorem cost_eq_add_of_w_eq (κ κ' : PartialCoupling μ ν) (M : S → T → ℝ)
    (hw : ∀ x y, κ'.w x y = κ.w x y + M x y) (d : S → T → ℝ) :
    κ'.cost d = κ.cost d + ∑ x, ∑ y, M x y * d x y := by
  simp only [cost, hw, add_mul, Finset.sum_add_distrib]

/-- Adding one point has the exact signed gain dictated by that pair. -/
theorem charge_eq_add_point (κ κ' : PartialCoupling μ ν) (x : S) (y : T) (p : ℝ)
    (hw : ∀ u v, κ'.w u v = κ.w u v + if u = x ∧ v = y then p else 0)
    (d : S → T → ℝ) (a : S → ℝ) (b : T → ℝ) :
    κ'.completionCharge d a b = κ.completionCharge d a b + p * (d x y - a x - b y) := by
  unfold completionCharge
  rw [cost_eq_add_of_w_eq κ κ' _ hw]
  simp only [ite_mul, zero_mul, ite_and]
  simp
  ring

/-- The true incidence matrix contributes the sum of the gains of its
incidences even when several incidences share one pair of output states. -/
theorem charge_matchResidualIncidences [Fintype K]
    (κ : PartialCoupling μ ν) (f : K → S) (g : K → T)
    (d : S → T → ℝ) (a : S → ℝ) (b : T → ℝ) :
    (κ.matchResidualIncidences f g).completionCharge d a b =
      κ.completionCharge d a b + ∑ i,
        IncidenceMatching.atIncidence f g κ.leftResidual κ.rightResidual i *
          (d (f i) (g i) - a (f i) - b (g i)) := by
  unfold completionCharge
  rw [cost_eq_add_of_w_eq κ (κ.matchResidualIncidences f g) _ (fun _ _ => rfl),
    IncidenceMatching.matrix_weighted_sum]
  ring

/-- Any finite assembly of increments has exactly the sum of the local
charge increments. The existence and capacities of the assembled plan are
already part of its `PartialCoupling` type. -/
theorem charge_sum_increments [Fintype K]
    (base total : PartialCoupling μ ν) (plans : K → PartialCoupling μ ν)
    (hw : ∀ x y, total.w x y = base.w x y + ∑ k, ((plans k).w x y - base.w x y))
    (d : S → T → ℝ) (a : S → ℝ) (b : T → ℝ) :
    total.completionCharge d a b = base.completionCharge d a b +
      ∑ k, ((plans k).completionCharge d a b - base.completionCharge d a b) := by
  have hcost : total.cost (fun x y => d x y - a x - b y) =
      base.cost (fun x y => d x y - a x - b y) +
      ∑ k, ((plans k).cost (fun x y => d x y - a x - b y) -
        base.cost (fun x y => d x y - a x - b y)) := by
    rw [cost_eq_add_of_w_eq base total _ hw]
    congr 1
    simp only [Finset.sum_mul]
    conv_lhs =>
      arg 2
      ext x
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [sub_mul, Finset.sum_sub_distrib, cost]
  unfold completionCharge
  rw [hcost, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A local matrix change can be accounted for using only its affected
rows and columns. Unchanged residuals outside these sets cancel exactly. -/
theorem charge_localize (base κ : PartialCoupling μ ν)
    (rows : Finset S) (cols : Finset T) (d : S → T → ℝ)
    (a : S → ℝ) (b : T → ℝ)
    (hl : ∀ x, x ∉ rows → κ.leftResidual x = base.leftResidual x)
    (hr : ∀ y, y ∉ cols → κ.rightResidual y = base.rightResidual y) :
    κ.completionCharge d a b - base.completionCharge d a b +
      ((∑ x ∈ rows, base.leftResidual x * a x) +
        ∑ y ∈ cols, base.rightResidual y * b y) =
      κ.cost d - base.cost d + (∑ x ∈ rows, κ.leftResidual x * a x) +
        ∑ y ∈ cols, κ.rightResidual y * b y := by
  have hleft : (∑ x, κ.leftResidual x * a x) - (∑ x, base.leftResidual x * a x) =
      (∑ x ∈ rows, κ.leftResidual x * a x) - ∑ x ∈ rows, base.leftResidual x * a x := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.subset_univ rows)
    intro x _ hx
    rw [hl x hx, sub_self]
  have hright : (∑ y, κ.rightResidual y * b y) - (∑ y, base.rightResidual y * b y) =
      (∑ y ∈ cols, κ.rightResidual y * b y) - ∑ y ∈ cols, base.rightResidual y * b y := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.subset_univ cols)
    intro y _ hy
    rw [hr y hy, sub_self]
  rw [completionCharge_eq, completionCharge_eq]
  linarith

end PartialCoupling

section Hamming

variable {V C : Type*} [Fintype V] [Fintype C]
local instance hardGlobalCostConfigDecEq : DecidableEq (V → C) := Classical.decEq _

/-- Signed one-step drift cost. -/
def hamDrift (U Z : V → C) : ℝ := ham U Z - 1

/-- The exact correction to separate move-size charges. -/
def hamDefect (X Y U Z : V → C) : ℝ := ham U Z - 1 - ham X U - ham Y Z

/-- The global completion charge of a partial matching of two hard rows. -/
def hamCompletionCharge {μ ν : FinDist (V → C)} (κ : PartialCoupling μ ν)
    (X Y : V → C) : ℝ :=
  κ.completionCharge hamDrift (ham X) (ham Y)

omit [Fintype C] in
/-- A root-local pair starts at Hamming distance exactly one. -/
theorem rootLocal_ham_one {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (h : RootLocalPair FX FY X Y v a b) : ham X Y = 1 := by
  have heq : (Finset.univ.filter fun w => X w ≠ Y w) = {v} := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [h.X_root, h.Y_root, h.colours_ne]
    · simp [hw, h.agree_off_root w hw]
  simp [ham, hamCard, heq]

omit [Fintype C] in
/-- Separate actual move sizes dominate every possible pair's Hamming drift. -/
theorem hamDrift_le_moves {X Y : V → C} (hXY : ham X Y = 1) (U Z : V → C) :
    hamDrift U Z ≤ ham X U + ham Y Z := by
  have h1 := ham_triangle U X Z
  have h2 := ham_triangle X Y Z
  rw [ham_comm U X] at h1
  rw [hXY] at h2
  unfold hamDrift
  linarith

/-- Averaging signed drift agrees exactly with subtracting one from cost. -/
theorem coupling_hamDrift_cost {μ ν : FinDist (V → C)} (γ : Coupling μ ν) :
    γ.cost hamDrift = γ.cost ham - 1 := by
  unfold Coupling.cost hamDrift
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, γ.sum_row, μ.sum_one]

/-- Every constructed global completion controls the actual Wasserstein drift. -/
theorem W_ham_sub_one_le_charge {μ ν : FinDist (V → C)}
    (κ : PartialCoupling μ ν) {X Y : V → C} (hXY : ham X Y = 1) :
    W ham μ ν - 1 ≤ hamCompletionCharge κ X Y := by
  have hW := W_le_cost ham_nonneg κ.complete
  have hC := κ.complete_cost_le_completionCharge hamDrift (ham X) (ham Y)
    (hamDrift_le_moves hXY)
  rw [coupling_hamDrift_cost] at hC
  exact (sub_le_sub_right hW 1).trans hC

/-- Cost accounting for the assembled actual regular-colour plan. -/
theorem globalRegular_charge_eq [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    hamCompletionCharge (globalRegularPartial h) X Y =
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ∑ c : RegularColour a b,
        (hamCompletionCharge (selectedRegularPartial FX FY X Y v c.val) X Y -
          hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y) := by
  apply PartialCoupling.charge_sum_increments
  intro U Z
  rfl

/-- The local charge increments of all regular colors survive the global
completion as a bound on the actual hard-row Wasserstein drift. -/
theorem globalRegular_W_drift_le [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    W ham (hardStep FX X) (hardStep FY Y) - 1 ≤
      hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y +
      ∑ c : RegularColour a b,
        (hamCompletionCharge (selectedRegularPartial FX FY X Y v c.val) X Y -
          hamCompletionCharge (hardCommonOffRootPartial FX FY X Y v) X Y) := by
  exact (W_ham_sub_one_le_charge (globalRegularPartial h) (rootLocal_ham_one h)).trans_eq
    (globalRegular_charge_eq h)

end Hamming

end

end CI2ZF
