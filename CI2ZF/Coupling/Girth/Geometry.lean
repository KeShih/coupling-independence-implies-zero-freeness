import CI2ZF.Potts.Model.PottsModel
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Girth-five local geometry and directed-incidence coefficients

The local geometry uses `egirth`, whose value on a forest is infinity.
`SimpleGraph.girth`, in contrast, has the junk value zero on a forest.
This proves the triangle/four-cycle exclusions actually used by both the
second-layer disintegration and the spectral-gap assembly.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

theorem neighbors_not_adjacent (hg : 5 ≤ G.egirth) {v u w : V}
    (hvu : G.Adj v u) (hvw : G.Adj v w) : ¬ G.Adj u w := by
  intro huw
  let p : G.Walk v v := .cons hvu (.cons huw (.cons hvw.symm .nil))
  have hp : p.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [p, SimpleGraph.Walk.isPath_def, huw.ne, Ne.symm hvu.ne, Ne.symm hvw.ne]
    · simp [p]
  have h := hg.trans (G.egirth_le_length hp)
  norm_num [p] at h

theorem common_neighbor_unique (hg : 5 ≤ G.egirth) {v w u u' : V}
    (hvw : v ≠ w) (hvu : G.Adj v u) (huw : G.Adj u w)
    (hvu' : G.Adj v u') (hu'w : G.Adj u' w) : u = u' := by
  by_contra hne
  let p : G.Walk v v :=
    .cons hvu (.cons huw (.cons hu'w.symm (.cons hvu'.symm .nil)))
  have hp : p.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [p, SimpleGraph.Walk.isPath_def, huw.ne, hne, Ne.symm hvu.ne,
        Ne.symm hvu'.ne, Ne.symm hu'w.ne, Ne.symm hvw]
    · simp [p]
  have h := hg.trans (G.egirth_le_length hp)
  norm_num [p] at h

/-- The sets `W_u = N(u) \ {v}` attached to distinct neighbours of `v`
are disjoint. This assertion makes no independence claim about their spins. -/
theorem second_layer_blocks_disjoint (hg : 5 ≤ G.egirth) {v u u' : V}
    (hvu : G.Adj v u) (hvu' : G.Adj v u') (hne : u ≠ u') :
    Disjoint {w | G.Adj u w ∧ w ≠ v} {w | G.Adj u' w ∧ w ≠ v} := by
  rw [Set.disjoint_left]
  intro w hw hw'
  exact hne (common_neighbor_unique G hg (Ne.symm hw.2) hvu hw.1 hvu' hw'.1)

/-- Every neighbour of a root neighbour, except the root, is outside the
first layer. Thus there are no omitted first-layer internal edge factors. -/
theorem second_step_not_first_layer (hg : 5 ≤ G.egirth) {v u w : V}
    (hvu : G.Adj v u) (huw : G.Adj u w) : ¬ G.Adj v w := by
  intro hvw
  exact neighbors_not_adjacent G hg hvu hvw huw

/-- The incidence weights used in the unequal-degree spectral assembly. -/
def incidenceWeight (d e : ℝ) : ℝ := 2 * d / (d + e)

theorem incidenceWeight_pos {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    0 < incidenceWeight d e := by
  unfold incidenceWeight
  positivity

theorem incidenceWeight_lt_two {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    incidenceWeight d e < 2 := by
  unfold incidenceWeight
  apply (div_lt_iff₀ (add_pos hd he)).mpr
  linarith

theorem incidenceWeight_add_reverse {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    incidenceWeight d e + incidenceWeight e d = 2 := by
  unfold incidenceWeight
  rw [add_comm e d, ← add_div]
  apply (div_eq_iff (add_pos hd he).ne').mpr
  ring

/-- The exact square-defect identity, retaining the loss from unequal degrees. -/
theorem incidence_square_identity {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    incidenceWeight d e ^ 2 / d =
      (1 - (incidenceWeight d e - 1) ^ 2) / e := by
  unfold incidenceWeight
  field_simp
  ring

theorem incidence_square_le {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    incidenceWeight d e ^ 2 / d ≤ 1 / e := by
  rw [incidence_square_identity hd he]
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (incidenceWeight d e - 1)]) he.le

variable [Fintype V]

theorem degree_pos_of_adj {v u : V} (hvu : G.Adj v u) : 0 < G.degree v := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  exact Finset.card_pos.mpr ⟨u, (G.mem_neighborFinset v u).mpr hvu⟩

/-- Summing all incoming square coefficients costs at most one at each site,
including isolated vertices. This is equation `sg-incidence-sum`. -/
theorem sum_incoming_incidence_le_one (u : V) :
    (∑ v ∈ G.neighborFinset u,
      incidenceWeight (G.degree v) (G.degree u) ^ 2 / (G.degree v : ℝ)) ≤ 1 := by
  classical
  by_cases hu : G.degree u = 0
  · have hne : G.neighborFinset u = ∅ := Finset.card_eq_zero.mp hu
    simp [hne]
  · have hu0 : (0 : ℝ) < G.degree u := by exact_mod_cast (Nat.pos_of_ne_zero hu)
    calc
      _ ≤ ∑ _v ∈ G.neighborFinset u, (1 : ℝ) / G.degree u := by
        apply Finset.sum_le_sum
        intro v hv
        have hv0 : (0 : ℝ) < G.degree v := by
          exact_mod_cast degree_pos_of_adj G ((G.mem_neighborFinset u v).mp hv).symm
        exact incidence_square_le hv0 hu0
      _ = 1 := by
        simp only [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
        field_simp

end

end CI2ZF.Appendix.Girth
