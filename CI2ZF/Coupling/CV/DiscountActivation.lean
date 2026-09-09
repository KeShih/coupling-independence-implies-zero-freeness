import CI2ZF.Coupling.CV.DiscountConstraints
import CI2ZF.Coupling.CV.Coins

/-! Safe physical activation events give the actual feasible singleton
cross moves used by the ordered-incidence discount. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def safeActivation (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool) : Prop :=
  ω (rootFreeConstraint I v u) = true ∧
    ∀ k ∈ (targetConstraints I X Y v u.val).erase (rootFreeConstraint I v u), ω k = false

lemma safeActivation_pattern (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool) :
    safeActivation I X Y v u ω ↔
      coinPattern {rootFreeConstraint I v u}
        ((targetConstraints I X Y v u.val).erase (rootFreeConstraint I v u)) ω := by
  simp [safeActivation, coinPattern]

/-- The safe-event probability is exactly the deterministic geometric score. -/
theorem safeActivation_probability (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => if safeActivation I X Y v u ω then (1 : ℝ) else 0) =
      (1 - x) * x^(blockerCount I X Y v u.val) := by
  simp_rw [safeActivation_pattern]
  have hdis : Disjoint ({rootFreeConstraint I v u} : Finset I.Constraint)
      ((targetConstraints I X Y v u.val).erase (rootFreeConstraint I v u)) := by simp
  have hh := coinPatternProbability_eq_inactive x hx _ _ hdis
  change expectReal _ _ = _ at hh
  simpa only [Finset.card_singleton, pow_one, targetConstraints_erase_root_card] using hh

lemma rootFreeConstraint_edge_ne (I : PinningData V C) (v : V) (u : I.graph.neighborSet v)
    (e : I.FreeEdge) (w : V) (he : e.val = s(u.val, w)) (hwv : w ≠ v) :
    (Sum.inl e : I.Constraint) ≠ rootFreeConstraint I v u := by
  intro hh
  have heq : s(u.val, w) = s(v, u.val) := by
    exact he.symm.trans (congrArg Subtype.val (Sum.inl.inj hh))
  rcases Sym2.eq_iff.mp heq with ⟨huv, _⟩ | ⟨_, hwv'⟩
  · exact u.property.ne huv.symm
  · exact hwv hwv'

lemma safeActivation_no_other_target_edge (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hsafe : safeActivation I X Y v u ω) (w : V) (hwv : w ≠ v)
    (htarget : targetAt X Y v w) :
    ¬ (activeGraph I (activatedSet I X ω)).Adj u.val w ∧
      ¬ (activeGraph I (activatedSet I Y ω)).Adj u.val w := by
  have hno (Q : V → C) : ¬ (activeGraph I (activatedSet I Q ω)).Adj u.val w := by
    rintro ⟨e, heA, he⟩
    have heT : (Sum.inl e : I.Constraint) ∈ targetConstraints I X Y v u.val :=
      (mem_targetConstraints I X Y v u.val _).mpr ⟨w, he, htarget⟩
    have heE := Finset.mem_erase.mpr ⟨rootFreeConstraint_edge_ne I v u e w he hwv, heT⟩
    have hz := hsafe.2 _ heE
    have hp := (mem_activatedSet I Q ω _).mp heA
    rw [hz] at hp
    exact Bool.noConfusion hp.1
  exact ⟨hno X, hno Y⟩

lemma safeActivation_target_list (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hsafe : safeActivation I X Y v u ω) (c : C) (hc : c = X v ∨ c = Y v)
    (Q : V → C) : c ∈ activeList I (activatedSet I Q ω) u.val := by
  rw [Potts.mem_activeList_activated]
  rintro ⟨⟨i, hi⟩, _⟩
  have hm : (Sum.inr ⟨u.val, c, i⟩ : I.Constraint) ∈
      (targetConstraints I X Y v u.val).erase (rootFreeConstraint I v u) := by
    apply Finset.mem_erase.mpr
    exact ⟨by simp [rootFreeConstraint], (mem_targetConstraints I X Y v u.val _).mpr ⟨rfl, hc⟩⟩
  rw [hsafe.2 _ hm] at hi
  exact Bool.noConfusion hi

/-- Safe activations realize the graph/list hypotheses of the singleton
matching theorem; these properties are consequences of the actual bits. -/
theorem safeActivation_singletons (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hroot : X v ≠ Y v) (hu : regularAt X Y v u.val)
    (hagree : ∀ w, w ≠ v → X w = Y w) (hsafe : safeActivation I X Y v u ω) :
    u.val ∈ rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v (X u.val) ∧
    flipSet (activeHardListInstance I (activatedSet I X ω)).graph X u.val (Y v) = {u.val} ∧
    flipSet (activeHardListInstance I (activatedSet I Y ω)).graph Y u.val (X v) = {u.val} ∧
    flipAllowed (activeHardListInstance I (activatedSet I X ω)) {u.val} (Function.update X u.val (Y v)) ∧
    flipAllowed (activeHardListInstance I (activatedSet I Y ω)) {u.val} (Function.update Y u.val (X v)) := by
  have heT := targetConstraints_root_edge_mem I X Y v u
  have heSat := targetConstraints_satisfied I X Y v u.val hu hagree _ heT
  have hneX : Y v ≠ X u.val := hu.2.2.symm
  have hneY : X v ≠ Y u.val := by rw [← hu.1]; exact hu.2.1.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply mem_rootNeighbours.mpr
    refine ⟨?_, rfl⟩
    rw [activeHardListInstance, activeGraph_root_adj_iff]
    exact (mem_activatedSet I X ω _).mpr ⟨hsafe.1, heSat.1⟩
  · apply root_flipSet_singleton_of_no_neighbours (activeHardListInstance I (activatedSet I X ω)) X u.val (Y v) hneX
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hed, hcol⟩ := mem_rootNeighbours.mp hw
    have hwv : w ≠ v := by intro hh; subst w; exact hroot hcol
    exact (safeActivation_no_other_target_edge I X Y v u ω hsafe w hwv (Or.inr (Or.inl hcol))).1 hed
  · apply root_flipSet_singleton_of_no_neighbours (activeHardListInstance I (activatedSet I Y ω)) Y u.val (X v) hneY
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hed, hcol⟩ := mem_rootNeighbours.mp hw
    have hwv : w ≠ v := by intro hh; subst w; exact hroot hcol.symm
    exact (safeActivation_no_other_target_edge I X Y v u ω hsafe w hwv (Or.inr (Or.inr (Or.inl hcol)))).2 hed
  · intro w hw
    have hw := Finset.mem_singleton.mp hw
    subst w
    simpa only [activeHardListInstance, Function.update_self] using
      safeActivation_target_list I X Y v u ω hsafe (Y v) (Or.inr rfl) X
  · intro w hw
    have hw := Finset.mem_singleton.mp hw
    subst w
    simpa only [activeHardListInstance, Function.update_self] using
      safeActivation_target_list I X Y v u ω hsafe (X v) (Or.inl rfl) Y

/-- The output cross-pair mass is certified on the physical safe event. -/
theorem fullHardCoupling_safe_cross_lower [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (u : I.graph.neighborSet v)
    (ω : I.Constraint → Bool) (hroot : X v ≠ Y v)
    (hu : regularAt X Y v u.val) (hagree : ∀ w, w ≠ v → X w = Y w)
    (choice : GlobalChoice (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree))
    (hsafe : safeActivation I X Y v u ω) :
    (1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) ≤
      (fullHardCoupling (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) choice).w
        (Function.update X u.val (Y v)) (Function.update Y u.val (X v)) := by
  obtain ⟨hmem, hx, hy, hax, hay⟩ := safeActivation_singletons I X Y v u ω hroot hu hagree hsafe
  apply fullHardCoupling_singleton_cross_lower _ choice hu.2.1 hu.2.2 hmem hx hy
  · rw [hx, flipConfiguration_singleton]; exact hax
  · rw [hy, flipConfiguration_singleton]; exact hay

end
end CI2ZF.Appendix.CV
