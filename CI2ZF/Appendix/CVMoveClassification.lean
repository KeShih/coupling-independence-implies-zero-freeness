import CI2ZF.Appendix.CVDiscountKernel
import CI2ZF.Appendix.CVRootAllocation
import CI2ZF.HardMoveClassification

/-! Exhaustion of positive actual CV common-plan residuals by the concrete
regular and root-colour move groups. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]

/-- Every positive-mass move either changes the root, is fully common,
or is an off-root move whose counterpart contains the root. -/
theorem hardStep_move_root_trichotomy [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U : V → C)
    (hU : U ≠ X) (hp : 0 < (hardStep FX X).w U) :
    (∃ c, c ≠ a ∧ U = flipConfiguration X (flipSet FX.graph X v c) (X v) c) ∨
    (∃ u c, c ≠ X u ∧
      flipAllowed FX (flipSet FX.graph X u c)
        (flipConfiguration X (flipSet FX.graph X u c) (X u) c) ∧
      U = flipConfiguration X (flipSet FX.graph X u c) (X u) c ∧
      v ∉ flipSet FX.graph X u c ∧
      (flipSet FX.graph X u c = flipSet FY.graph Y u c ∨
        v ∈ flipSet FY.graph Y u c)) := by
  obtain ⟨u, c, hc, ha, hout⟩ := hardStep_positive_move FX X U hU hp
  by_cases hvX : v ∈ flipSet FX.graph X u c
  · left
    obtain ⟨_, heq⟩ := component_move_from_member FX.graph X u c hc v hvX
    refine ⟨U v, ?_, ?_⟩
    · rw [hout, ← h.X_root]
      exact (flipConfiguration_ne_iff hc v).mpr hvX
    · rw [hout]
      exact heq.symm
  · right
    refine ⟨u, c, hc, ha, hout, hvX, ?_⟩
    by_cases hvY : v ∈ flipSet FY.graph Y u c
    · exact Or.inr hvY
    · exact Or.inl (common_component_sets h u c hvX hvY)

/-- After the common allocation, every positive residual non-holding
row belongs to a root move or to an actual affected-neighbour group.
There is no support-exhaustion assumption in this result. -/
theorem hardCommon_residual_exhaustion [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U : V → C) (hU : U ≠ X)
    (hp : 0 < (hardCommonOffRootPartial FX FY X Y v).leftResidual U) :
    (∃ c, c ≠ a ∧ U = flipConfiguration X (flipSet FX.graph X v c) (X v) c) ∨
    (∃ c u, c ≠ b ∧ u ∈ rootNeighbours FY Y v c ∧
      U = flipConfiguration X (flipSet FX.graph X u b) (X u) b ∧
      v ∉ flipSet FX.graph X u b) := by
  let k := hardCommonOffRootPartial FX FY X Y v
  have hpU : 0 < (hardStep FX X).w U := by
    have hn : 0 ≤ ∑ Z, k.w U Z := Finset.sum_nonneg (fun Z _ => k.nonneg U Z)
    change 0 < (hardStep FX X).w U - ∑ Z, k.w U Z at hp
    linarith
  rcases hardStep_move_root_trichotomy h U hU hpU with hroot | ⟨u, c, hc, ha, hout, hv, hm⟩
  · exact Or.inl hroot
  · rcases hm with hcommon | haffected
    · exfalso
      have hfull := hardCommonOffRoot_component_match h u c hc hcommon hv ha
      have hmass := hardStep_component_mass FX X u c hc ha
      rw [← hmass, ← hout] at hfull
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun Z => k.w U Z) (fun Z _ => k.nonneg U Z)
        (Finset.mem_univ (flipConfiguration Y (flipSet FY.graph Y u c) (Y u) c))
      change k.w U _ = (hardStep FX X).w U at hfull
      rw [hfull] at hle
      change 0 < (hardStep FX X).w U - ∑ Z, k.w U Z at hp
      linarith
    · obtain ⟨d, w, hdb, hw, heq, hvw⟩ :=
        affected_component_from_neighbour h u c hc hv haffected
      exact Or.inr ⟨d, w, hdb, hw, hout.trans heq, hvw⟩


end
end CI2ZF.Appendix.CV
