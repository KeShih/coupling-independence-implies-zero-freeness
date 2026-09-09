import CI2ZF.Potts.Model.Real.Model
import Mathlib.Tactic

namespace CI2ZF.Potts

open PottsCI

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*}

/-- Add one labelled occurrence of a pinned colour at a free vertex. -/
def addBoundary (I : PinningData V C) (u : V) (c : C) : PinningData V C where
  graph := I.graph
  boundaryCount := fun v b => I.boundaryCount v b + if v = u ∧ b = c then 1 else 0

/-- Add one boundary occurrence of colour `c` at each vertex in `S`. -/
def addBoundarySet (I : PinningData V C) (S : Finset V) (c : C) : PinningData V C where
  graph := I.graph
  boundaryCount := fun v b => I.boundaryCount v b + if v ∈ S ∧ b = c then 1 else 0

@[simp] theorem addBoundary_graph (I : PinningData V C) (u : V) (c : C) :
    (addBoundary I u c).graph = I.graph := rfl

@[simp] theorem addBoundary_count (I : PinningData V C) (u v : V) (c b : C) :
    (addBoundary I u c).boundaryCount v b =
      I.boundaryCount v b + if v = u ∧ b = c then 1 else 0 := rfl

@[simp] theorem addBoundarySet_empty (I : PinningData V C) (c : C) :
    addBoundarySet I ∅ c = I := by
  cases I
  simp [addBoundarySet]

/-- Inductively enumerate the added vertices without duplicating occurrences. -/
theorem addBoundarySet_insert (I : PinningData V C) (S : Finset V) (u : V) (c : C)
    (hu : u ∉ S) :
    addBoundarySet I (insert u S) c = addBoundary (addBoundarySet I S c) u c := by
  unfold addBoundarySet addBoundary
  congr 1
  funext v b
  by_cases hvc : b = c <;> by_cases hvu : v = u <;> by_cases hvs : v ∈ S
  all_goals simp_all

end

end CI2ZF.Potts
