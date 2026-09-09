import CI2ZF.Coupling.CV.DiscountBlocked
import CI2ZF.Coupling.CV.DiscountPointwise
import CI2ZF.Coupling.Vigoda.BoundaryActivation

/-! Physical target-constraint sets. Each free edge occurs once; each pinned
occurrence keeps its label. Distinct regular vertices have disjoint sets. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def targetAt (X Y : V → C) (v w : V) : Prop :=
  X w = X v ∨ X w = Y v ∨ Y w = X v ∨ Y w = Y v

def regularAt (X Y : V → C) (v u : V) : Prop :=
  X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v

lemma regularAt_not_targetAt {X Y : V → C} {v u : V} (hu : regularAt X Y v u) :
    ¬ targetAt X Y v u := by
  rintro (hh | hh | hh | hh)
  · exact hu.2.1 hh
  · exact hu.2.2 hh
  · exact hu.2.1 (hu.1.trans hh)
  · exact hu.2.2 (hu.1.trans hh)

def constraintTargets (I : PinningData V C) (X Y : V → C) (v u : V) : I.Constraint → Prop
  | .inl e => ∃ w, e.val = s(u, w) ∧ targetAt X Y v w
  | .inr i => i.1 = u ∧ (i.2.1 = X v ∨ i.2.1 = Y v)

def targetConstraints (I : PinningData V C) (X Y : V → C) (v u : V) : Finset I.Constraint :=
  Finset.univ.filter (constraintTargets I X Y v u)

@[simp] lemma mem_targetConstraints (I : PinningData V C) (X Y : V → C)
    (v u : V) (k : I.Constraint) : k ∈ targetConstraints I X Y v u ↔ constraintTargets I X Y v u k := by
  simp only [targetConstraints, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Shared edges cannot belong to both target-constraint sets, since both
endpoints are initially outside the target pair. Boundary occurrences have distinct vertices. -/
theorem targetConstraints_disjoint (I : PinningData V C) (X Y : V → C) (v u w : V)
    (huw : u ≠ w) (_hu : regularAt X Y v u) (hw : regularAt X Y v w) :
    Disjoint (targetConstraints I X Y v u) (targetConstraints I X Y v w) := by
  apply Finset.disjoint_left.mpr
  intro k hku hkw
  rw [mem_targetConstraints] at hku hkw
  cases k with
  | inl e =>
    obtain ⟨s, hes, hs⟩ := hku
    obtain ⟨t, het, _⟩ := hkw
    have heq : s(u, s) = s(w, t) := hes.symm.trans het
    rcases Sym2.eq_iff.mp heq with ⟨huw', _⟩ | ⟨_, hsw⟩
    · exact huw huw'
    · exact regularAt_not_targetAt hw (hsw ▸ hs)
  | inr i => exact huw (hku.1.symm.trans hkw.1)

/-- The disjoint index set giving every target occurrence exactly once. -/
abbrev TargetConstraintIndex (I : PinningData V C) (X Y : V → C) (v u : V) :=
  {w : V // I.graph.Adj u w ∧ targetAt X Y v w} ⊕
    {i : I.BoundaryOccurrence // i.1 = u ∧ (i.2.1 = X v ∨ i.2.1 = Y v)}

def targetConstraintIndexMap (I : PinningData V C) (X Y : V → C) (v u : V) :
    TargetConstraintIndex I X Y v u → {k : I.Constraint // k ∈ targetConstraints I X Y v u}
  | .inl w => ⟨.inl ⟨s(u, w.val), by rw [SimpleGraph.mem_edgeFinset]; exact w.property.1⟩,
      (mem_targetConstraints I X Y v u _).mpr ⟨w.val, rfl, w.property.2⟩⟩
  | .inr i => ⟨.inr i.val, (mem_targetConstraints I X Y v u _).mpr i.property⟩

lemma targetConstraintIndexMap_bijective (I : PinningData V C) (X Y : V → C) (v u : V) :
    Function.Bijective (targetConstraintIndexMap I X Y v u) := by
  constructor
  · intro i j heq
    cases i with
    | inl w =>
      cases j with
      | inl t =>
        apply congrArg Sum.inl
        apply Subtype.ext
        have he : s(u, w.val) = s(u, t.val) := by
          exact congrArg Subtype.val (Sum.inl.inj (congrArg Subtype.val heq))
        rcases Sym2.eq_iff.mp he with ⟨_, hh⟩ | ⟨hut, hwu⟩
        · exact hh
        · exact hwu.trans hut
      | inr t => simp [targetConstraintIndexMap] at heq
    | inr i =>
      cases j with
      | inl t => simp [targetConstraintIndexMap] at heq
      | inr j =>
        exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (congrArg Subtype.val heq)))
  · intro k
    obtain ⟨k, hk⟩ := k
    rw [mem_targetConstraints] at hk
    cases k with
    | inl e =>
      obtain ⟨w, he, hw⟩ := hk
      have hadj : I.graph.Adj u w := by
        have hh := e.property
        rw [he, SimpleGraph.mem_edgeFinset] at hh
        exact hh
      refine ⟨.inl ⟨w, hadj, hw⟩, ?_⟩
      apply Subtype.ext
      exact congrArg Sum.inl (Subtype.ext he.symm)
    | inr i => exact ⟨.inr ⟨i, hk⟩, rfl⟩

/-- Exact physical factor count, including target multiplicities on the boundary. -/
theorem targetConstraints_card (I : PinningData V C) (X Y : V → C) (v u : V) :
    (targetConstraints I X Y v u).card =
      ((I.graph.neighborFinset u).filter (targetAt X Y v)).card +
        ∑ c ∈ Finset.univ.filter (fun c => c = X v ∨ c = Y v), I.boundaryCount u c := by
  classical
  have hc := Fintype.card_congr (Equiv.ofBijective _ (targetConstraintIndexMap_bijective I X Y v u))
  rw [Fintype.card_coe] at hc
  change Fintype.card (_ ⊕ _) = _ at hc
  rw [Fintype.card_sum] at hc
  rw [← hc]
  congr 1
  · simp only [Fintype.card_subtype]
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborFinset]
  · rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
    rw [Finset.sum_filter, Fintype.sum_sigma]
    rw [Finset.sum_eq_single u]
    · rw [Fintype.sum_sigma, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c = X v ∨ c = Y v <;> simp [hc]
    · intro w _ hwu
      rw [Fintype.sum_sigma]
      simp [hwu]
    · simp

lemma targetConstraints_root_edge_mem (I : PinningData V C) (X Y : V → C)
    (v : V) (u : I.graph.neighborSet v) :
    rootFreeConstraint I v u ∈ targetConstraints I X Y v u.val := by
  rw [mem_targetConstraints]
  refine ⟨v, Sym2.eq_swap, ?_⟩
  exact Or.inl rfl

/-- Removing the root edge leaves precisely the blocker exponent of the
input incidence; no free edge is duplicated. -/
theorem targetConstraints_erase_root_card (I : PinningData V C) (X Y : V → C)
    (v : V) (u : I.graph.neighborSet v) :
    ((targetConstraints I X Y v u.val).erase (rootFreeConstraint I v u)).card =
      blockerCount I X Y v u.val := by
  classical
  have hm := targetConstraints_root_edge_mem I X Y v u
  rw [Finset.card_erase_of_mem hm, targetConstraints_card]
  let B := (I.graph.neighborFinset u.val).filter (targetAt X Y v)
  have hvB : v ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨by simpa using u.property.symm, Or.inl rfl⟩
  have he : B.erase v = freeBlockers I X Y v u.val := by
    ext w
    simp only [B, freeBlockers, Finset.mem_erase, Finset.mem_filter]
    tauto
  have hc := Finset.card_erase_of_mem hvB
  rw [he] at hc
  have hpos := Finset.card_pos.mpr ⟨v, hvB⟩
  change B.card + _ - 1 = (freeBlockers I X Y v u.val).card + _
  omega

/-- At a regular vertex, every collected target constraint is eligible in
both marginal configurations. -/
lemma targetConstraints_satisfied (I : PinningData V C) (X Y : V → C) (v u : V)
    (hu : regularAt X Y v u) (hagree : ∀ w, w ≠ v → X w = Y w)
    (k : I.Constraint) (hk : k ∈ targetConstraints I X Y v u) :
    I.constraintSatisfied X k ∧ I.constraintSatisfied Y k := by
  rw [mem_targetConstraints] at hk
  cases k with
  | inl e =>
    obtain ⟨w, he, hw⟩ := hk
    have hxw : X w = X v ∨ X w = Y v := by
      by_cases hwv : w = v
      · subst w; exact Or.inl rfl
      · unfold targetAt at hw
        rw [← hagree w hwv] at hw
        tauto
    have hyw : Y w = X v ∨ Y w = Y v := by
      by_cases hwv : w = v
      · subst w; exact Or.inr rfl
      · rw [← hagree w hwv]; exact hxw
    change Sym2.lift _ e.val ∧ Sym2.lift _ e.val
    rw [he]
    change X u ≠ X w ∧ Y u ≠ Y w
    constructor
    · intro hh; exact hxw.elim (fun h => hu.2.1 (hh.trans h)) (fun h => hu.2.2 (hh.trans h))
    · intro hh; exact hyw.elim (fun h => hu.2.1 (hu.1.trans (hh.trans h)))
        (fun h => hu.2.2 (hu.1.trans (hh.trans h)))
  | inr i =>
    obtain ⟨w, c, j⟩ := i
    obtain ⟨rfl, hc⟩ := hk
    change X w ≠ c ∧ Y w ≠ c
    constructor
    · intro hh; exact hc.elim (fun h => hu.2.1 (hh.trans h)) (fun h => hu.2.2 (hh.trans h))
    · intro hh; exact hc.elim (fun h => hu.2.1 (hu.1.trans (hh.trans h)))
        (fun h => hu.2.2 (hu.1.trans (hh.trans h)))

/-- An active bit in the physical collected set is an actual blocker in
one of the two target transitions, or an active edge to the root. -/
theorem active_targetConstraint_is_blocker (I : PinningData V C) (X Y : V → C)
    (ω : I.Constraint → Bool) (v u : V) (hu : regularAt X Y v u)
    (hagree : ∀ w, w ≠ v → X w = Y w)
    (k : I.Constraint) (hk : k ∈ targetConstraints I X Y v u) (hcoin : ω k = true) :
    X v ∉ (activeHardListInstance I (activatedSet I Y ω)).list u ∨
    Y v ∉ (activeHardListInstance I (activatedSet I X ω)).list u ∨
    ∃ w, ((activeHardListInstance I (activatedSet I X ω)).graph ⊔
      (activeHardListInstance I (activatedSet I Y ω)).graph).Adj u w ∧
      (X w = X v ∨ X w = Y v ∨ Y w = X v ∨ Y w = Y v) := by
  have hs := targetConstraints_satisfied I X Y v u hu hagree k hk
  rw [mem_targetConstraints] at hk
  cases k with
  | inl e =>
    obtain ⟨w, he, hw⟩ := hk
    exact Or.inr (Or.inr ⟨w, Or.inl ⟨e, (mem_activatedSet I X ω _).mpr ⟨hcoin, hs.1⟩, he⟩, hw⟩)
  | inr i =>
    obtain ⟨w, c, j⟩ := i
    obtain ⟨rfl, hc⟩ := hk
    have hx : c ∉ (activeHardListInstance I (activatedSet I X ω)).list w := by
      rw [activeHardListInstance, Potts.mem_activeList_activated]
      push Not
      exact ⟨⟨j, hcoin⟩, hs.1⟩
    have hy : c ∉ (activeHardListInstance I (activatedSet I Y ω)).list w := by
      rw [activeHardListInstance, Potts.mem_activeList_activated]
      push Not
      exact ⟨⟨j, hcoin⟩, hs.2⟩
    rcases hc with hc | hc
    · exact Or.inl (hc ▸ hy)
    · exact Or.inr (Or.inl (hc ▸ hx))

end
end CI2ZF.Appendix.CV
