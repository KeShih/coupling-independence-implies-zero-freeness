import CI2ZF.Coupling.Vigoda.HardFlipBoundary
import CI2ZF.Coupling.Vigoda.ActivationLaw
import CI2ZF.Potts.Model.BoundaryData
import Mathlib.Data.Fin.Embedding

/-! Exact labelled-constraint geometry for one added boundary occurrence. -/

namespace CI2ZF.Potts
open PottsCI PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def boundaryIndexEmbedding (I : PinningData V C) (r : V) (a : C) (u : V) (c : C) :
    Fin (I.boundaryCount u c) ↪ Fin ((addBoundary I r a).boundaryCount u c) :=
  Fin.castLEEmb (by simp only [addBoundary_count]; omega)

/-- Old labelled constraints retain their exact identity after adding one
new occurrence, including repeated boundary colours. -/
def boundaryConstraintEmbedding (I : PinningData V C) (r : V) (a : C) :
    I.Constraint ↪ (addBoundary I r a).Constraint :=
  Function.Embedding.sumMap (Function.Embedding.refl _)
    (Function.Embedding.sigmaMap (Function.Embedding.refl V) fun u =>
      Function.Embedding.sigmaMap (Function.Embedding.refl C) fun c =>
        boundaryIndexEmbedding I r a u c)

def freshBoundaryConstraint (I : PinningData V C) (r : V) (a : C) :
    (addBoundary I r a).Constraint :=
  Sum.inr ⟨r, a, ⟨I.boundaryCount r a, by simp [addBoundary_count]⟩⟩

@[simp] lemma boundaryConstraintEmbedding_edge (I : PinningData V C) (r : V) (a : C)
    (e : I.FreeEdge) : boundaryConstraintEmbedding I r a (Sum.inl e) = Sum.inl e := rfl

@[simp] lemma boundaryConstraintEmbedding_boundary (I : PinningData V C) (r : V) (a : C)
    (u : V) (c : C) (i : Fin (I.boundaryCount u c)) :
    boundaryConstraintEmbedding I r a (Sum.inr ⟨u, c, i⟩) =
      Sum.inr ⟨u, c, boundaryIndexEmbedding I r a u c i⟩ := rfl

@[simp] lemma constraintSatisfied_boundaryEmbedding (I : PinningData V C) (r : V) (a : C)
    (X : V → C) (k : I.Constraint) :
    (addBoundary I r a).constraintSatisfied X (boundaryConstraintEmbedding I r a k) ↔
      I.constraintSatisfied X k := by
  cases k <;> rfl

@[simp] lemma constraintSatisfied_freshBoundary (I : PinningData V C) (r : V) (a : C)
    (X : V → C) :
    (addBoundary I r a).constraintSatisfied X (freshBoundaryConstraint I r a) ↔ X r ≠ a :=
  Iff.rfl

/-- Every boundary coin in the enlarged instance is either an old labelled
coin or the unique newly added one. -/
lemma boundaryCoin_exists (I : PinningData V C) (r : V) (a : C)
    (ω : (addBoundary I r a).Constraint → Bool) (u : V) (c : C) :
    (∃ i : Fin ((addBoundary I r a).boundaryCount u c), ω (Sum.inr ⟨u, c, i⟩) = true) ↔
      (∃ i : Fin (I.boundaryCount u c),
        ω (boundaryConstraintEmbedding I r a (Sum.inr ⟨u, c, i⟩)) = true) ∨
      (u = r ∧ c = a ∧ ω (freshBoundaryConstraint I r a) = true) := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases hold : i.val < I.boundaryCount u c
    · left
      refine ⟨⟨i.val, hold⟩, ?_⟩
      convert hi using 1
      rfl
    · right
      have hlt := i.isLt
      change i.val < I.boundaryCount u c + (if u = r ∧ c = a then 1 else 0) at hlt
      have hur : u = r ∧ c = a := by
        by_contra h
        rw [if_neg h] at hlt
        omega
      rcases hur with ⟨rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      have hval : i.val = I.boundaryCount u c := by simp only [and_self, if_true] at hlt; omega
      have heq : i = ⟨I.boundaryCount u c, by simp [addBoundary_count]⟩ := Fin.ext hval
      simpa only [heq, freshBoundaryConstraint] using hi
  · rintro (⟨i, hi⟩ | ⟨rfl, rfl, hi⟩)
    · exact ⟨boundaryIndexEmbedding I r a u c i, hi⟩
    · exact ⟨⟨I.boundaryCount u c, by simp [addBoundary_count]⟩, hi⟩

/-- Adding a boundary occurrence cannot alter the active free graph. -/
lemma activeGraph_addBoundary (I : PinningData V C) (r : V) (a : C)
    (X : V → C) (ω : (addBoundary I r a).Constraint → Bool) :
    activeGraph (addBoundary I r a) (activatedSet (addBoundary I r a) X ω) =
      activeGraph I (activatedSet I X (fun k => ω (boundaryConstraintEmbedding I r a k))) := by
  apply SimpleGraph.ext
  funext u v
  simp only [activeGraph, mem_activatedSet]
  rfl

lemma mem_activeList_activated (I : PinningData V C) (X : V → C)
    (ω : I.Constraint → Bool) (u : V) (c : C) :
    c ∈ activeList I (activatedSet I X ω) u ↔
      ¬ ((∃ i : Fin (I.boundaryCount u c), ω (Sum.inr ⟨u, c, i⟩) = true) ∧ X u ≠ c) := by
  simp only [activeList, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_activatedSet, PinningData.constraintSatisfied, exists_and_right]

/-- The new labelled occurrence either does nothing, or deletes exactly
its colour from exactly its vertex's active list. -/
lemma activeList_addBoundary (I : PinningData V C) (r : V) (a : C)
    (X : V → C) (ω : (addBoundary I r a).Constraint → Bool) (u : V) :
    activeList (addBoundary I r a) (activatedSet (addBoundary I r a) X ω) u =
      if ω (freshBoundaryConstraint I r a) = true ∧ X r ≠ a ∧ u = r then
        (activeList I (activatedSet I X
          (fun k => ω (boundaryConstraintEmbedding I r a k))) u).erase a
      else activeList I (activatedSet I X
          (fun k => ω (boundaryConstraintEmbedding I r a k))) u := by
  ext c
  rw [mem_activeList_activated, boundaryCoin_exists]
  by_cases hf : ω (freshBoundaryConstraint I r a) = true
  · by_cases hx : X r ≠ a
    · by_cases hu : u = r
      · subst u
        rw [if_pos ⟨hf, hx, rfl⟩, Finset.mem_erase, mem_activeList_activated]
        by_cases hc : c = a
        · subst c
          simp [hf, hx]
        · simp [hc]
      · rw [if_neg (by tauto), mem_activeList_activated]
        simp [hu]
    · rw [if_neg (by tauto), mem_activeList_activated]
      by_cases hu : u = r
      · subst u
        by_cases hc : c = a
        · subst c
          simp [hx]
        · simp [hc]
      · simp [hu]
  · rw [if_neg (by tauto), mem_activeList_activated]
    simp [hf]

/-- Exact active hard-instance identity under the shared old coins and one
new independent boundary coin. -/
lemma activeHardListInstance_addBoundary (I : PinningData V C) (r : V) (a : C)
    (X : V → C) (ω : (addBoundary I r a).Constraint → Bool) :
    activeHardListInstance (addBoundary I r a) (activatedSet (addBoundary I r a) X ω) =
      if ω (freshBoundaryConstraint I r a) = true ∧ X r ≠ a then
        deleteListColour (activeHardListInstance I (activatedSet I X
          (fun k => ω (boundaryConstraintEmbedding I r a k)))) r a
      else activeHardListInstance I (activatedSet I X
          (fun k => ω (boundaryConstraintEmbedding I r a k))) := by
  by_cases h : ω (freshBoundaryConstraint I r a) = true ∧ X r ≠ a
  · rw [if_pos h]
    unfold activeHardListInstance deleteListColour
    congr 1
    · exact activeGraph_addBoundary I r a X ω
    · funext u
      rw [activeList_addBoundary]
      simp only [h.1, true_and]
      exact if_congr ⟨And.right, fun hu => ⟨h.2, hu⟩⟩ rfl rfl
  · rw [if_neg h]
    unfold activeHardListInstance
    congr 1
    · exact activeGraph_addBoundary I r a X ω
    · funext u
      rw [activeList_addBoundary]
      rw [if_neg (fun hh => h ⟨hh.1, hh.2.1⟩)]

end
end CI2ZF.Potts
