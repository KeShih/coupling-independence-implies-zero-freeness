import ZeroFreeness.Coupling.Girth.Spectral.Graph.Operators

/-! Exact graph counting in the global rate-one spectral-gap assembly.
Girth five is used only to exclude triangles and repeated common neighbours. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators InnerProductSpace
open Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Every non-diagonal ordered pair with a common neighbour is counted
exactly once in the sum over stars. -/
theorem common_neighbour_sum (hg : 5 ≤ G.egirth) (u w : V) (huw : u ≠ w) (t : ℝ) :
    (∑ v, if G.Adj v u ∧ G.Adj v w then t else 0) =
      if ∃ v, G.Adj v u ∧ G.Adj v w then t else 0 := by
  by_cases hex : ∃ v, G.Adj v u ∧ G.Adj v w
  · obtain ⟨v, hvu, hvw⟩ := hex
    rw [if_pos ⟨v, hvu, hvw⟩]
    calc
      _ = (if G.Adj v u ∧ G.Adj v w then t else 0) := by
        apply Finset.sum_eq_single v
        · intro z _ hz
          have hn : ¬ (G.Adj z u ∧ G.Adj z w) := by
            intro hh
            exact hz (common_neighbor_unique G hg huw hh.1.symm hh.2 hvu.symm hvw)
          exact if_neg hn
        · intro h
          exact (h (Finset.mem_univ v)).elim
      _ = t := if_pos ⟨hvu, hvw⟩
  · rw [if_neg hex]
    apply Finset.sum_eq_zero
    intro v _
    exact if_neg (fun h => hex ⟨v, h⟩)

def edgePairSum (F : V → V → ℝ) : ℝ := ∑ u, ∑ w, if G.Adj u w then F u w else 0

def secondPairSum (F : V → V → ℝ) : ℝ :=
  ∑ u, ∑ w, if u ≠ w ∧ ∃ v, G.Adj v u ∧ G.Adj v w then F u w else 0

def distantPairSum (F : V → V → ℝ) : ℝ :=
  ∑ u, ∑ w, if u ≠ w ∧ ¬ G.Adj u w ∧ ¬ ∃ v, G.Adj v u ∧ G.Adj v w then F u w else 0

theorem off_diagonal_partition (hg : 5 ≤ G.egirth) (F : V → V → ℝ) :
    (∑ u, ∑ w, if u ≠ w then F u w else 0) =
      edgePairSum G F + secondPairSum G F + distantPairSum G F := by
  unfold edgePairSum secondPairSum distantPairSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases heq : u = w
  · subst w
    simp
  by_cases ha : G.Adj u w
  · have hn : ¬ ∃ v, G.Adj v u ∧ G.Adj v w := by
      rintro ⟨v, hvu, hvw⟩
      exact neighbors_not_adjacent G hg hvu hvw ha
    simp [Ne, heq, ha, hn]
  · by_cases hn : ∃ v, G.Adj v u ∧ G.Adj v w <;> simp [heq, ha, hn]

theorem star_second_sum (hg : 5 ≤ G.egirth) (F : V → V → ℝ) :
    (∑ v, ∑ u, ∑ w, if G.Adj v u ∧ G.Adj v w ∧ u ≠ w then F u w else 0) =
      secondPairSum G F := by
  rw [Finset.sum_comm]
  unfold secondPairSum
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases heq : u = w
  · subst w
    simp
  · have he : (∑ v, if G.Adj v u ∧ G.Adj v w ∧ u ≠ w then F u w else 0) =
        ∑ v, if G.Adj v u ∧ G.Adj v w then F u w else 0 := by
      simp [Ne, heq]
    rw [he, common_neighbour_sum G hg u w heq]
    simp [Ne, heq]

theorem weighted_edge_sum (F : V → V → ℝ) (hF : ∀ u w, F u w = F w u) :
    (∑ v, ∑ u, if G.Adj v u then incidenceWeight (G.degree v) (G.degree u) * F v u else 0) =
      edgePairSum G F := by
  let A := ∑ v, ∑ u, if G.Adj v u then incidenceWeight (G.degree v) (G.degree u) * F v u else 0
  have hswap : A = ∑ v, ∑ u, if G.Adj v u then incidenceWeight (G.degree u) (G.degree v) * F v u else 0 := by
    dsimp only [A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro u _
    rw [G.adj_comm u v, hF u v]
  have htwice : A + A = 2 * edgePairSum G F := by
    conv_lhs => rhs; rw [hswap]
    dsimp only [A]
    rw [← Finset.sum_add_distrib]
    unfold edgePairSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : G.Adj v u
    · simp only [if_pos h]
      have hv : (0 : ℝ) < G.degree v := Nat.cast_pos.mpr (degree_pos_of_adj G h)
      have hu : (0 : ℝ) < G.degree u := Nat.cast_pos.mpr (degree_pos_of_adj G h.symm)
      have he := incidenceWeight_add_reverse hv hu
      rw [← add_mul, he]
    · simp only [if_neg h, zero_add, mul_zero]
  change A = _
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sum_sq_sub_diagonal (f : V → E) :
    ‖∑ v, f v‖ ^ 2 - (∑ v, ‖f v‖ ^ 2) =
      ∑ v, ∑ u, if v ≠ u then ⟪f v, f u⟫_ℝ else 0 := by
  have hsplit : (∑ v, ∑ u, ⟪f v, f u⟫_ℝ) =
      (∑ v, ‖f v‖ ^ 2) + ∑ v, ∑ u, if v ≠ u then ⟪f v, f u⟫_ℝ else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    have he (u : V) : ⟪f v, f u⟫_ℝ =
        (if v = u then ‖f v‖ ^ 2 else 0) + (if v ≠ u then ⟪f v, f u⟫_ℝ else 0) := by
      by_cases h : v = u
      · subst u
        rw [if_pos rfl, if_neg (not_ne_iff.mpr rfl), real_inner_self_eq_norm_sq, add_zero]
      · simp [h]
    calc
      _ = ∑ u, ((if v = u then ‖f v‖ ^ 2 else 0) +
          (if v ≠ u then ⟪f v, f u⟫_ℝ else 0)) := Finset.sum_congr rfl (fun u _ => he u)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]
  linarith

end
end ZeroFreeness.Appendix.Girth
