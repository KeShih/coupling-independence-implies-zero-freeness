import CI2ZF.RootChildren
import CI2ZF.SoftFlipBoundary

/-!
# Boundary sensitivity of the actual root children

Single-occurrence soft boundary sensitivity is telescoped over the exact
remaining root-neighbour set. This discharges the boundary-input part of
stationary comparison using the original graph's degree bound.
-/

namespace CI2ZF.Potts

open PottsCI PottsCI.FinDist PottsCI.Vigoda
attribute [local instance] Classical.propDecidable

noncomputable section

local instance (priority := 2000) (α : Type*) : DecidableEq α := Classical.decEq α

variable {V C : Type*} [Fintype V] [Fintype C]

/-- Adding the same pinned colour at every vertex of a finite set changes
each actual soft row by at most one single-occurrence budget per vertex. -/
theorem softVigodaKernel_addBoundarySet_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (S : Finset V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softVigodaKernel (addBoundarySet I S a) x hx0 hx1 X)
      (softVigodaKernel I x hx0 hx1 X) ≤
        (1 - x) * S.card / ((Fintype.card V : ℝ) * Fintype.card C) := by
  induction S using Finset.induction_on with
  | empty => simp [W_self ham_nonneg ham_self]
  | @insert u S hu ih =>
    rw [addBoundarySet_insert I S u a hu]
    calc
      _ ≤ W ham
          (softVigodaKernel (addBoundary (addBoundarySet I S a) u a) x hx0 hx1 X)
          (softVigodaKernel (addBoundarySet I S a) x hx0 hx1 X) +
          W ham (softVigodaKernel (addBoundarySet I S a) x hx0 hx1 X)
            (softVigodaKernel I x hx0 hx1 X) :=
        W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle _ _ _
      _ ≤ (1 - x) / ((Fintype.card V : ℝ) * Fintype.card C) +
          (1 - x) * S.card / ((Fintype.card V : ℝ) * Fintype.card C) :=
        add_le_add (softVigodaKernel_addBoundary_W_le_reverse
          (addBoundarySet I S a) u a X x hx0 hx1) ih
      _ = _ := by rw [Finset.card_insert_of_notMem hu, Nat.cast_add, Nat.cast_one]; ring

/-- The concrete child-to-middle perturbation bound required in root CI. -/
theorem rootChild_soft_boundary_W_le [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (a : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (X : RootRemaining tau r → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softVigodaKernel (rootChildData tau G r a) x hx0 hx1 X)
      (softVigodaKernel (rootMiddleData tau G r) x hx0 hx1 X) ≤
        (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  rw [rootChildData_eq_addBoundarySet]
  apply (softVigodaKernel_addBoundarySet_W_le _ _ _ _ x hx0 hx1).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact_mod_cast rootBoundaryVertices_card_le tau G r hdegree

end

end CI2ZF.Potts
