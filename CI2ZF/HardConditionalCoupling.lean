import CI2ZF.HardMoveMass
import CI2ZF.PartialCoupling
import CI2ZF.IncidenceMatching
import PottsCI.Vigoda.ComponentCoupling

/-! Actual partial couplings of the hard component-flip rows.  Common
root-preserving moves are matched through root replacement, with capacities
computed from the two genuine hard transition laws.
-/

namespace CI2ZF
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

/-- Transport an output colouring to the other fixed root-colour fibre. -/
def replaceRoot (U : V → C) (v : V) (b : C) : V → C := Function.update U v b

@[simp] lemma replaceRoot_at_root (U : V → C) (v : V) (b : C) :
    replaceRoot U v b v = b := by simp [replaceRoot]

lemma replaceRoot_off_root (U : V → C) (v : V) (b : C) (w : V) (hw : w ≠ v) :
    replaceRoot U v b w = U w := by simp [replaceRoot, hw]

lemma replaceRoot_inverse (U : V → C) (v : V) (a b : C) (hU : U v = a) :
    replaceRoot (replaceRoot U v b) v a = U := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [hU]
  · simp [replaceRoot, hw]

lemma replaceRoot_injective_fibre (v : V) (a b : C) {U T : V → C}
    (hU : U v = a) (hT : T v = a)
    (h : replaceRoot U v b = replaceRoot T v b) : U = T := by
  have hi := congrArg (fun Z => replaceRoot Z v a) h
  simpa only [replaceRoot_inverse U v a b hU, replaceRoot_inverse T v a b hT] using hi

/-- Match every non-holding output in the original root fibre with the
output having exactly the same off-root colours in the other root fibre.
The minimum of the two actual row probabilities is always available. -/
def commonOffRootPartial (mu nu : FinDist (V → C)) (X Y : V → C) (v : V) :
    PartialCoupling mu nu where
  w U Z := if U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
    then min (mu.w U) (nu.w Z) else 0
  nonneg U Z := by
    split_ifs
    · exact le_min (mu.nonneg U) (nu.nonneg Z)
    · exact le_rfl
  row_le U := by
    by_cases hU : U v = X v ∧ U ≠ X
    · have hterm (Z : V → C) :
          (if U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
            then min (mu.w U) (nu.w Z) else 0) =
          if Z = replaceRoot U v (Y v) then min (mu.w U) (nu.w Z) else 0 := by
        exact if_congr ⟨And.right ∘ And.right, fun hz => ⟨hU.1, hU.2, hz⟩⟩ rfl rfl
      simp_rw [hterm]
      simp
    · have hterm (Z : V → C) :
          ¬ (U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)) :=
        fun hz => hU ⟨hz.1, hz.2.1⟩
      simp only [if_neg (hterm _), Finset.sum_const_zero]
      exact mu.nonneg U
  col_le Z := by
    have hterm (U : V → C) :
        (if U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
          then min (mu.w U) (nu.w Z) else 0) ≤
        if U = replaceRoot Z v (X v) then nu.w Z else 0 := by
      by_cases h : U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
      · rw [if_pos h]
        have hi : U = replaceRoot Z v (X v) := by
          rw [h.2.2, replaceRoot_inverse U v (X v) (Y v) h.1]
        rw [if_pos hi]
        exact min_le_right _ _
      · rw [if_neg h]
        split_ifs
        · exact nu.nonneg Z
        · exact le_rfl
    exact (Finset.sum_le_sum fun U _ => hterm U).trans_eq (by simp)

/-- The common-off-root allocation for the two actual component-flip rows. -/
def hardCommonOffRootPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  commonOffRootPartial (hardStep FX X) (hardStep FY Y) X Y v

@[simp] lemma commonOffRootPartial_holding_row (mu nu : FinDist (V → C))
    (X Y : V → C) (v : V) (Z : V → C) :
    (commonOffRootPartial mu nu X Y v).w X Z = 0 := by
  simp [commonOffRootPartial]

lemma commonOffRootPartial_changed_root_row (mu nu : FinDist (V → C))
    (X Y : V → C) (v : V) (U Z : V → C) (hU : U v ≠ X v) :
    (commonOffRootPartial mu nu X Y v).w U Z = 0 := by
  simp [commonOffRootPartial, hU]

lemma commonOffRootPartial_changed_root_col (mu nu : FinDist (V → C))
    (X Y : V → C) (v : V) (U Z : V → C) (hZ : Z v ≠ Y v) :
    (commonOffRootPartial mu nu X Y v).w U Z = 0 := by
  unfold commonOffRootPartial
  apply if_neg
  rintro ⟨_, _, h⟩
  exact hZ (by rw [h, replaceRoot_at_root])

/-- Equal available common-move rates are matched in full. -/
lemma commonOffRootPartial_full_match (mu nu : FinDist (V → C))
    (X Y : V → C) (v : V) (U : V → C) (hroot : U v = X v) (hmove : U ≠ X)
    (hmass : mu.w U = nu.w (replaceRoot U v (Y v))) :
    (commonOffRootPartial mu nu X Y v).w U (replaceRoot U v (Y v)) = mu.w U := by
  change (if U v = X v ∧ U ≠ X ∧ replaceRoot U v (Y v) = replaceRoot U v (Y v)
    then min (mu.w U) (nu.w (replaceRoot U v (Y v))) else 0) = mu.w U
  rw [if_pos ⟨hroot, hmove, rfl⟩, ← hmass, min_self]

lemma replaceRoot_eq_of_agree_off_root (X Y : V → C) (v : V)
    (hagree : ∀ w, w ≠ v → X w = Y w) : replaceRoot X v (Y v) = Y := by
  funext w
  by_cases hw : w = v
  · subst w
    simp
  · rw [replaceRoot_off_root _ _ _ _ hw]
    exact hagree w hw

lemma commonOffRootPartial_holding_col (mu nu : FinDist (V → C))
    (X Y : V → C) (v : V) (hagree : ∀ w, w ≠ v → X w = Y w) (U : V → C) :
    (commonOffRootPartial mu nu X Y v).w U Y = 0 := by
  unfold commonOffRootPartial
  apply if_neg
  rintro ⟨hr, hn, hm⟩
  apply hn
  apply replaceRoot_injective_fibre v (X v) (Y v) hr rfl
  exact hm.symm.trans (replaceRoot_eq_of_agree_off_root X Y v hagree).symm

lemma common_component_replacement (X Y : V → C) (v : V)
    (hagree : ∀ w, w ≠ v → X w = Y w) (S : Finset V) (a b : C) (hv : v ∉ S) :
    replaceRoot (flipConfiguration X S a b) v (Y v) = flipConfiguration Y S a b := by
  funext w
  by_cases hw : w = v
  · subst w
    rw [replaceRoot_at_root, flipConfiguration_of_not_mem hv]
  · rw [replaceRoot_off_root _ _ _ _ hw]
    unfold flipConfiguration
    rw [hagree w hw]

/-- A feasible component that is off-root in both hard instances receives
its complete true transition mass in the common matching. -/
theorem hardCommonOffRoot_component_match [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (hpair : RootLocalPair FX FY X Y v a b) (u : V) (c : C) (hc : c ≠ X u)
    (hsets : flipSet FX.graph X u c = flipSet FY.graph Y u c)
    (hv : v ∉ flipSet FX.graph X u c)
    (ha : flipAllowed FX (flipSet FX.graph X u c)
      (flipConfiguration X (flipSet FX.graph X u c) (X u) c)) :
    (hardCommonOffRootPartial FX FY X Y v).w
      (flipConfiguration X (flipSet FX.graph X u c) (X u) c)
      (flipConfiguration Y (flipSet FY.graph Y u c) (Y u) c) =
        vigodaMass (flipSet FX.graph X u c).card /
          ((Fintype.card V : ℝ) * Fintype.card C) := by
  have huv : u ≠ v := by
    intro hu
    exact hv (hu ▸ self_mem_flipSet)
  have hxy := hpair.agree_off_root u huv
  have heq := common_component_replacement X Y v hpair.agree_off_root
    (flipSet FX.graph X u c) (X u) c hv
  have heq' : replaceRoot (flipConfiguration X (flipSet FX.graph X u c) (X u) c) v (Y v) =
      flipConfiguration Y (flipSet FY.graph Y u c) (Y u) c := by
    simpa only [hsets, hxy] using heq
  have hay : flipAllowed FY (flipSet FY.graph Y u c)
      (flipConfiguration Y (flipSet FY.graph Y u c) (Y u) c) := by
    intro w hw
    have hwX : w ∈ flipSet FX.graph X u c := hsets.symm ▸ hw
    have hwv : w ≠ v := fun h => hv (h ▸ hwX)
    rw [← hpair.offRoot_list_eq w hwv, ← heq', replaceRoot_off_root _ _ _ _ hwv]
    exact ha w hwX
  have hmx := hardStep_component_mass FX X u c hc ha
  have hmy := hardStep_component_mass FY Y u c (by simpa only [← hxy] using hc) hay
  have hm : (hardStep FX X).w (flipConfiguration X (flipSet FX.graph X u c) (X u) c) =
      (hardStep FY Y).w (replaceRoot
        (flipConfiguration X (flipSet FX.graph X u c) (X u) c) v (Y v)) := by
    rw [heq', hmx, hmy, hsets]
  rw [← hmx, ← heq']
  apply commonOffRootPartial_full_match
  · exact flipConfiguration_of_not_mem hv
  · intro h
    exact ((flipConfiguration_ne_iff hc u).mpr self_mem_flipSet) (congrFun h u)
  · exact hm

/-- A common-match row has zero mass when its root-replaced output is
infeasible for the other actual hard instance. -/
lemma hardCommonOffRoot_row_zero_of_improper [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V)
    (hY : FY.IsProper Y) (U : V → C)
    (hbad : ¬ FY.IsProper (replaceRoot U v (Y v))) (Z : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z = 0 := by
  change (if U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
    then min ((hardStep FX X).w U) ((hardStep FY Y).w Z) else 0) = 0
  by_cases h : U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
  · rw [if_pos h, h.2.2, hardStep_support hY hbad]
    exact min_eq_right ((hardStep FX X).nonneg U)
  · exact if_neg h

/-- The inverse root replacement detects columns which cannot be used by
any common off-root match. -/
lemma hardCommonOffRoot_col_zero_of_improper [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V)
    (hX : FX.IsProper X) (Z : V → C)
    (hbad : ¬ FX.IsProper (replaceRoot Z v (X v))) (U : V → C) :
    (hardCommonOffRootPartial FX FY X Y v).w U Z = 0 := by
  change (if U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
    then min ((hardStep FX X).w U) ((hardStep FY Y).w Z) else 0) = 0
  by_cases h : U v = X v ∧ U ≠ X ∧ Z = replaceRoot U v (Y v)
  · rw [if_pos h]
    have hinv : replaceRoot Z v (X v) = U := by
      rw [h.2.2, replaceRoot_inverse U v (X v) (Y v) h.1]
    have hbadU : ¬ FX.IsProper U := by simpa only [hinv] using hbad
    rw [hardStep_support hX hbadU]
    exact min_eq_left ((hardStep FY Y).nonneg Z)
  · exact if_neg h

namespace PartialCoupling
variable {S T : Type*} [Fintype S] [Fintype T]
variable {mu : FinDist S} {nu : FinDist T}

/-- Add a specified point mass when it fits the actual residual marginals. -/
def addPoint (kappa : PartialCoupling mu nu) (x : S) (y : T) (p : ℝ)
    (hp : 0 ≤ p) (hleft : p ≤ kappa.leftResidual x)
    (hright : p ≤ kappa.rightResidual y) : PartialCoupling mu nu where
  w u v := kappa.w u v + if u = x ∧ v = y then p else 0
  nonneg u v := add_nonneg (kappa.nonneg u v) (by split_ifs <;> positivity)
  row_le u := by
    rw [Finset.sum_add_distrib]
    by_cases hu : u = x
    · subst u
      simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      dsimp only [leftResidual] at hleft
      linarith
    · simp only [hu, false_and, if_false, Finset.sum_const_zero, add_zero]
      exact kappa.row_le u
  col_le v := by
    rw [Finset.sum_add_distrib]
    by_cases hv : v = y
    · subst v
      simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      dsimp only [rightResidual] at hright
      linarith
    · simp only [hv, and_false, if_false, Finset.sum_const_zero, add_zero]
      exact kappa.col_le v

/-- A capacity-safe point allocation, using exact residuals and a requested
upper cap.  It is a genuine partial coupling for every finite instance. -/
def matchPointAtMost (kappa : PartialCoupling mu nu) (x : S) (y : T) (cap : ℝ)
    (hcap : 0 ≤ cap) : PartialCoupling mu nu :=
  kappa.addPoint x y (min cap (min (kappa.leftResidual x) (kappa.rightResidual y)))
    (le_min hcap (le_min (kappa.leftResidual_nonneg x) (kappa.rightResidual_nonneg y)))
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _))

lemma matchPointAtMost_full (kappa : PartialCoupling mu nu) (x : S) (y : T) (cap : ℝ)
    (hcap : 0 ≤ cap) (hleft : cap ≤ kappa.leftResidual x)
    (hright : cap ≤ kappa.rightResidual y) (u : S) (v : T) :
    (kappa.matchPointAtMost x y cap hcap).w u v =
      kappa.w u v + if u = x ∧ v = y then cap else 0 := by
  dsimp only [matchPointAtMost, addPoint]
  rw [min_eq_left (le_min hleft hright)]

lemma matchPointAtMost_leftResidual_of_ne (kappa : PartialCoupling mu nu)
    (x : S) (y : T) (cap : ℝ) (hcap : 0 ≤ cap) (u : S) (hu : u ≠ x) :
    (kappa.matchPointAtMost x y cap hcap).leftResidual u = kappa.leftResidual u := by
  simp [leftResidual, matchPointAtMost, addPoint, hu]

lemma matchPointAtMost_rightResidual_of_ne (kappa : PartialCoupling mu nu)
    (x : S) (y : T) (cap : ℝ) (hcap : 0 ≤ cap) (v : T) (hv : v ≠ y) :
    (kappa.matchPointAtMost x y cap hcap).rightResidual v = kappa.rightResidual v := by
  simp [rightResidual, matchPointAtMost, addPoint, hv]

/-- Add an incidence matching inside the exact residual capacities. -/
def matchResidualIncidences {J : Type*} [Fintype J]
    (kappa : PartialCoupling mu nu) (f : J → S) (g : J → T) : PartialCoupling mu nu where
  w x y := kappa.w x y +
    IncidenceMatching.matrix f g kappa.leftResidual kappa.rightResidual x y
  nonneg x y := add_nonneg (kappa.nonneg x y)
    (IncidenceMatching.matrix_nonneg f g _ _
      kappa.leftResidual_nonneg kappa.rightResidual_nonneg x y)
  row_le x := by
    rw [Finset.sum_add_distrib]
    have hb := IncidenceMatching.matrix_row_le f g kappa.leftResidual kappa.rightResidual
      kappa.leftResidual_nonneg x
    dsimp only [leftResidual] at hb
    linarith [kappa.row_le x]
  col_le y := by
    rw [Finset.sum_add_distrib]
    have hb := IncidenceMatching.matrix_col_le f g kappa.leftResidual kappa.rightResidual
      kappa.rightResidual_nonneg y
    dsimp only [rightResidual] at hb
    linarith [kappa.col_le y]

end PartialCoupling

/-- The two regular root-to-component allocations, taken from the actual
remaining hard-row capacities after matching common off-root moves.
The incidence allocation can subsequently be applied to this partial plan. -/
def regularRootPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) (u w : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  let RX := flipConfiguration X (flipSet FX.graph X v c) (X v) c
  let SY := flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c
  let CY := flipConfiguration Y (flipSet FY.graph Y u (X v)) (Y u) (X v)
  let DX := flipConfiguration X (flipSet FX.graph X w (Y v)) (X w) (Y v)
  let first := (hardCommonOffRootPartial FX FY X Y v).matchPointAtMost RX CY
    ((hardStep FX X).w RX) ((hardStep FX X).nonneg RX)
  first.matchPointAtMost DX SY ((hardStep FY Y).w SY) ((hardStep FY Y).nonneg SY)

end
end CI2ZF
