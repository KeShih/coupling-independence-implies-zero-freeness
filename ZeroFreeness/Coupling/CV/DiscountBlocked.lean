import ZeroFreeness.Coupling.CV.DiscountSingleton

/-! A surviving active target blocker improves the target-loss probability
from `2/(nq)` to `(1+P₂)/(nq)`, including a blocker at the disagreement root. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]

def rootFixedBadMass {FX FY : HardListInstance V C} {X Y : V → C}
    (γ : Coupling (hardStep FX X) (hardStep FY Y)) (v u : V) (a b : C) : ℝ :=
  ∑ U, ∑ Z, if U v = X v ∧ Z v = Y v ∧
    ¬ (U u = Z u ∧ U u ≠ a ∧ U u ≠ b) then γ.w U Z else 0

lemma targetProbability_eq_zero_of_not_list (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) (hc : c ≠ X u) (hlist : c ∉ F.list u) :
    targetProbability F X u c = 0 := by
  rw [targetProbability_eq F X u c hc, if_neg]
  intro ha
  apply hlist
  simpa only [flipConfiguration_at_start] using ha u self_mem_flipSet

lemma flipSet_card_ge_two_of_adj (F : HardListInstance V C) (X : V → C)
    (u w : V) (c : C) (huw : F.graph.Adj u w) (hw : X w = c) :
    2 ≤ (flipSet F.graph X u c).card := by
  classical
  have hmem : w ∈ flipSet F.graph X u c := mem_flipSet.mpr
    (Relation.ReflTransGen.single ⟨huw, Or.inl ⟨rfl, hw⟩⟩)
  have hsub : ({u, w} : Finset V) ⊆ flipSet F.graph X u c := by
    intro t ht
    rcases (show t = u ∨ t = w by simpa only [Finset.mem_insert, Finset.mem_singleton] using ht) with rfl | rfl
    · exact self_mem_flipSet
    · exact hmem
  simpa [huw.ne] using Finset.card_le_card hsub

lemma flipSet_eq_singleton_of_card_le_one (F : HardListInstance V C) (X : V → C)
    (u : V) (c : C) (hc : (flipSet F.graph X u c).card ≤ 1) :
    flipSet F.graph X u c = {u} := by
  have heq : (flipSet F.graph X u c).card = 1 :=
    le_antisymm hc (flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c))
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp heq
  have hum : u ∈ flipSet F.graph X u c := self_mem_flipSet
  rw [hw, Finset.mem_singleton] at hum
  simpa only [hum] using hw

/-- An active root edge also improves the loss bound: when both opposite
target moves are singletons their actual intersection supplies the saving. -/
theorem fullHardCoupling_rootNeighbour_badMass_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hu : u ∈ rootNeighbours FX X v c) :
    rootFixedBadMass (fullHardCoupling h choice) v u a b ≤
      (1 + 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have huv := rootNeighbour_ne_root hu
  have hXu := (mem_rootNeighbours.mp hu).2
  have hua : X u ≠ a := by rwa [hXu]
  have hub : X u ≠ b := by rwa [hXu]
  have haY : a ≠ Y u := by rw [← h.agree_off_root u huv]; exact hua.symm
  have hpX := targetProbability_le FX X u b hub.symm
  have hpY := targetProbability_le FY Y u a haY
  have hb := root_fixed_badAt_mass_le h (fullHardCoupling h choice)
    (fullHardCoupling_dominate_common h choice) u huv hua hub
  change rootFixedBadMass _ v u a b ≤ _ at hb
  by_cases hsX : 2 ≤ (flipSet FX.graph X u b).card
  · have hx := targetProbability_le_mass_two FX X u b hub.symm hsX
    exact hb.trans ((add_le_add hx hpY).trans_eq (by ring))
  by_cases hsY : 2 ≤ (flipSet FY.graph Y u a).card
  · have hy := targetProbability_le_mass_two FY Y u a haY hsY
    exact hb.trans ((add_le_add hpX hy).trans_eq (by ring))
  have hsizeX := flipSet_eq_singleton_of_card_le_one FX X u b (by omega)
  have hsizeY := flipSet_eq_singleton_of_card_le_one FY Y u a (by omega)
  by_cases halX : flipAllowed FX (flipSet FX.graph X u b)
      (flipConfiguration X (flipSet FX.graph X u b) (X u) b)
  · by_cases halY : flipAllowed FY (flipSet FY.graph Y u a)
        (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a)
    · have hcredit := fullHardCoupling_singleton_cross_lower h choice hca hcb hu hsizeX hsizeY halX halY
      have hb' := root_fixed_badAt_mass_le_with_cross h (fullHardCoupling h choice)
        (fullHardCoupling_dominate_common h choice) u huv hua hub
        (Function.update X u b) (Function.update Y u a) (by simp) (by simp)
      exact hb'.trans ((sub_le_sub (add_le_add hpX hpY) hcredit).trans_eq (by ring))
    · have hz : targetProbability FY Y u a = 0 := by rw [targetProbability_eq FY Y u a haY, if_neg halY]
      rw [hz, add_zero] at hb
      exact hb.trans (hpX.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)))
  · have hz : targetProbability FX X u b = 0 := by rw [targetProbability_eq FX X u b hub.symm, if_neg halX]
    rw [hz, zero_add] at hb
    exact hb.trans (hpY.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)))

/-- Any active collected target constraint gives the improved rate. The
free-neighbour condition is symmetric in the two hard instances. -/
theorem fullHardCoupling_active_blocker_badMass_le
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (huv : u ≠ v) (hua : X u ≠ a) (hub : X u ≠ b)
    (hblock : a ∉ FY.list u ∨ b ∉ FX.list u ∨
      ∃ w, (FX.graph ⊔ FY.graph).Adj u w ∧ (X w = a ∨ X w = b ∨ Y w = a ∨ Y w = b)) :
    rootFixedBadMass (fullHardCoupling h choice) v u a b ≤
      (1 + 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have haY : a ≠ Y u := by rw [← h.agree_off_root u huv]; exact hua.symm
  have hpX := targetProbability_le FX X u b hub.symm
  have hpY := targetProbability_le FY Y u a haY
  have hb := root_fixed_badAt_mass_le h (fullHardCoupling h choice)
    (fullHardCoupling_dominate_common h choice) u huv hua hub
  change rootFixedBadMass _ v u a b ≤ _ at hb
  rcases hblock with hbad | hbad | ⟨w, hadj, hwt⟩
  · rw [targetProbability_eq_zero_of_not_list FY Y u a haY hbad, add_zero] at hb
    exact hb.trans (hpX.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)))
  · rw [targetProbability_eq_zero_of_not_list FX X u b hub.symm hbad, zero_add] at hb
    exact hb.trans (hpY.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)))
  · by_cases hwv : w = v
    · subst w
      have hed : FX.graph.Adj v u := by
        rcases hadj with hadj | hadj
        · exact hadj.symm
        · exact (h.regular_root_edge_iff u (X u) huv rfl hua hub).mpr hadj.symm
      exact fullHardCoupling_rootNeighbour_badMass_le h choice hua hub (mem_rootNeighbours.mpr ⟨hed, rfl⟩)
    · have hadjX : FX.graph.Adj u w := hadj.elim id ((h.offRoot_edge_iff u w huv hwv).mpr)
      have hadjY : FY.graph.Adj u w := (h.offRoot_edge_iff u w huv hwv).mp hadjX
      have hxy := h.agree_off_root w hwv
      have hcol : X w = a ∨ X w = b := by rw [← hxy] at hwt; tauto
      rcases hcol with hwa | hwb
      · have hy := targetProbability_le_mass_two FY Y u a haY
          (flipSet_card_ge_two_of_adj FY Y u w a hadjY (hxy.symm.trans hwa))
        exact hb.trans ((add_le_add hpX hy).trans_eq (by ring))
      · have hx := targetProbability_le_mass_two FX X u b hub.symm
          (flipSet_card_ge_two_of_adj FX X u w b hadjX hwb)
        exact hb.trans ((add_le_add hx hpY).trans_eq (by ring))

end
end ZeroFreeness.Appendix.CV
