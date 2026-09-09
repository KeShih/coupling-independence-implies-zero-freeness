import CI2ZF.Coupling.CV.MoveMass
import CI2ZF.Coupling.Vigoda.HardConditionalCoupling

/-! Actual partial CV couplings. Root-preserving component moves are matched
with full aggregate mass, and regular root matches use exact residual capacities. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def hardCommonOffRootPartial [Nonempty V] [Nonempty C]
    (FX FY : HardListInstance V C) (X Y : V → C) (v : V) :
    PartialCoupling (hardStep FX X) (hardStep FY Y) :=
  commonOffRootPartial (hardStep FX X) (hardStep FY Y) X Y v

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
        mass (flipSet FX.graph X u c).card /
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
end CI2ZF.Appendix.CV
