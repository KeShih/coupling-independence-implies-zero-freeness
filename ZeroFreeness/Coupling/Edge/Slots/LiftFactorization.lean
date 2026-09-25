import ZeroFreeness.Coupling.Edge.Slots.Moments

/-!
# Independent endpoint-colour groups in the finite slot lift

Slot assignments indexed by edge incidences split into independent groups
indexed by endpoint and colour. The factorization is an identity of the
literal finite sums over admissible assignments.
-/

namespace ZeroFreeness.Appendix.Edge

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {I J R : Type*} [Fintype I] [Fintype J] [Fintype R]
variable [DecidableEq I] [DecidableEq J] [DecidableEq R]

def finiteDistinctMass (κ : R → ℝ) (I : Type*) [Fintype I] [DecidableEq I] : ℝ :=
  ∑ f : I → R, if Function.Injective f then ∏ i, κ (f i) else 0

lemma finiteDistinctMass_eq (κ : R → ℝ) :
    finiteDistinctMass κ I = distinctSlotMass κ (Fintype.card I) := by
  let e := Fintype.equivFin I
  unfold finiteDistinctMass distinctSlotMass
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl R))
  intro f
  change (if Function.Injective f then ∏ i, κ (f i) else 0) =
    (if Function.Injective (fun j => f (e.symm j)) then ∏ j, κ (f (e.symm j)) else 0)
  have hi : Function.Injective (fun j => f (e.symm j)) ↔ Function.Injective f := by
    constructor
    · intro hf i j hij
      apply e.injective
      apply hf
      simpa using hij
    · intro hf
      exact hf.comp e.symm.injective
  by_cases hf : Function.Injective f
  · simp only [if_pos hf, if_pos (hi.mpr hf)]
    exact Fintype.prod_equiv e (fun i => κ (f i)) (fun j => κ (f (e.symm j))) (by simp)
  · simp only [if_neg hf, if_neg (fun h => hf (hi.mp h))]

/-- Regroup all incidence coordinates by their endpoint-colour key. -/
def fibreAssignmentEquiv (g : I → J) :
    (I → R) ≃ ((j : J) → {i : I // g i = j} → R) where
  toFun f _ i := f i.val
  invFun f i := f (g i) ⟨i, rfl⟩
  left_inv f := rfl
  right_inv f := by
    funext j i
    rcases i with ⟨i, hi⟩
    subst j
    rfl

def GroupedSlotInjective (g : I → J) (f : I → R) : Prop :=
  ∀ j, Function.Injective (fun i : {i : I // g i = j} => f i.val)

lemma groupedSlotInjective_iff (g : I → J) (f : I → R) :
    GroupedSlotInjective g f ↔ ∀ i j, g i = g j → f i = f j → i = j := by
  constructor
  · intro h i j hg hf
    have heq := h (g i) (a₁ := ⟨i, rfl⟩) (a₂ := ⟨j, hg.symm⟩) hf
    exact congrArg Subtype.val heq
  · intro h j i i' heq
    exact Subtype.ext (h i.val i'.val (i.property.trans i'.property.symm) heq)

def groupedSlotMass (κ : R → ℝ) (g : I → J) : ℝ :=
  ∑ f : I → R, if GroupedSlotInjective g f then ∏ i, κ (f i) else 0

/-- All endpoint-colour groups factor independently, including empty groups. -/
lemma groupedSlotMass_factorization (κ : R → ℝ) (g : I → J) :
    groupedSlotMass κ g = ∏ j, distinctSlotMass κ (Fintype.card {i : I // g i = j}) := by
  calc
    groupedSlotMass κ g =
        ∑ f : (j : J) → {i : I // g i = j} → R,
          ∏ j, (if Function.Injective (f j) then ∏ i, κ (f j i) else 0) := by
      unfold groupedSlotMass
      apply Fintype.sum_equiv (fibreAssignmentEquiv g)
      intro f
      rw [Fintype.prod_ite_zero]
      by_cases h : GroupedSlotInjective g f
      · have h' : ∀ j, Function.Injective ((fibreAssignmentEquiv g) f j) := h
        simp only [if_pos h, if_pos h']
        exact (Fintype.prod_fiberwise g (fun i => κ (f i))).symm
      · have h' : ¬ ∀ j, Function.Injective ((fibreAssignmentEquiv g) f j) := h
        simp only [if_neg h, if_neg h']
    _ = ∏ j, finiteDistinctMass κ {i : I // g i = j} := by
      exact (Fintype.prod_sum (fun j (f : {i : I // g i = j} → R) =>
        if Function.Injective f then ∏ i, κ (f i) else 0)).symm
    _ = _ := Finset.prod_congr rfl fun _ _ => finiteDistinctMass_eq κ

end
end ZeroFreeness.Appendix.Edge
