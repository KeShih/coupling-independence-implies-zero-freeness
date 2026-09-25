import ZeroFreeness.Coupling.BBR.Differential

/-! Algebraic bridges between the BBR square-root message differential and
centered functions under the actual root marginal. -/
namespace ZeroFreeness.Appendix.BBR
open scoped BigOperators
open Finset
open ZeroFreeness.Appendix.Girth
noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Dividing the Euclidean projection by the square-root message centers
the relative perturbation under the actual root marginal. -/
theorem projection_div_message {x : ℝ} (hx : 0 < x)
    (t : CavityTree C) (z : C → ℝ) (a : C) :
    projection (t.message x) z a / t.message x a =
      z a / t.message x a - ∑ c, t.probability x c * (z c / t.message x c) := by
  have hsum : (∑ c, t.probability x c * (z c / t.message x c)) =
      innerSum (t.message x) z / squareMass (t.message x) := by
    simp only [innerSum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [t.probability_eq_square hx c]
    field_simp [(t.message_pos hx c).ne', (t.squareMass_pos hx).ne']
  rw [hsum]
  unfold projection
  field_simp [(t.message_pos hx a).ne', (t.squareMass_pos hx).ne']

/-- A normalized Jacobian block is the centered child perturbation times
the exact conditional-edge coefficient. -/
theorem jacobianBlock_div_message {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (parent child : CavityTree C) (z : C → ℝ) (a : C) :
    jacobianBlock x (parent.message x) (child.message x) z a / parent.message x a =
      -(1 - x) * child.probability x a / (1 - (1 - x) * child.probability x a) *
        (projection (child.message x) z a / child.message x a) := by
  have hden : 1 - (1 - x) * child.probability x a =
      excludedMass x (child.message x) a / squareMass (child.message x) := by
    rw [child.probability_eq_square hx a]
    unfold excludedMass
    field_simp [(child.squareMass_pos hx).ne']
  rw [hden, child.probability_eq_square hx a]
  unfold jacobianBlock
  field_simp [(parent.message_pos hx a).ne', (child.message_pos hx a).ne',
    (child.squareMass_pos hx).ne',
    (excludedMass_pos hx hx1 (child.message x) (child.squareMass_pos hx) a).ne']
  ring

/-- At a terminal vertex, the relative projected response is the usual
centered observable under its actual root marginal. -/
theorem terminal_projection_div_message {x : ℝ} (hx : 0 < x)
    (t : CavityTree C) (h : C → ℝ) (a : C) :
    projection (t.message x) (fun c => t.message x c * h c) a / t.message x a =
      h a - ∑ c, t.probability x c * h c := by
  have hcancel (c : C) : t.message x c * h c / t.message x c = h c := by
    field_simp [(t.message_pos hx c).ne']
  rw [projection_div_message hx]
  simp_rw [hcancel]

omit [DecidableEq C] [Nonempty C] in
/-- The fixed-message projection distributes over any finite family of
perturbations, including the empty family. -/
theorem projection_sum {D : Type*} [Fintype D]
    (y : C → ℝ) (z : D → C → ℝ) (a : C) :
    projection y (fun c => ∑ i, z i c) a = ∑ i, projection y (z i) a := by
  unfold projection innerSum
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

end
end ZeroFreeness.Appendix.BBR
