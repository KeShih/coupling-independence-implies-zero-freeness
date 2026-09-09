import CI2ZF.Coupling.Girth.Spectral.Graph.Sums

/-! The exact global star decomposition of the rate-one Glauber square,
with every distant-pair remainder proved nonnegative. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators InnerProductSpace
open Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace GraphProjections
variable {G : SimpleGraph V} (P : GraphProjections G E)

theorem laplacian_sum_energy (f : E) : energy P.laplacian f = ∑ v, energy (P.Q v) f := by
  simp only [energy, laplacian, LinearMap.sum_apply, inner_sum]

theorem incidence_energy (v : V) (f : E) :
    ⟪P.Q v f, P.incidenceSum v f⟫_ℝ =
      ∑ u, if G.Adj v u then P.beta v u * ⟪P.Q v f, P.Q u f⟫_ℝ else 0 := by
  simp only [incidenceSum, LinearMap.sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs
  · rw [LinearMap.smul_apply, real_inner_smul_right]
  · simp

theorem neighbour_energy (v : V) (f : E) :
    energy (P.neighbourSum v) f = ∑ u, ‖if G.Adj v u then P.Q u f else 0‖ ^ 2 := by
  simp only [neighbourSum, energy, LinearMap.sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs
  · exact (P.projection u).inner_self f
  · simp

theorem neighbour_excess_energy (v : V) (f : E) :
    ‖P.neighbourSum v f‖ ^ 2 - energy (P.neighbourSum v) f =
      ∑ u, ∑ w, if G.Adj v u ∧ G.Adj v w ∧ u ≠ w then ⟪P.Q u f, P.Q w f⟫_ℝ else 0 := by
  rw [P.neighbour_energy]
  have he : P.neighbourSum v f = ∑ u, if G.Adj v u then P.Q u f else 0 := by
    simp only [neighbourSum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> rfl
  rw [he, norm_sum_sq_sub_diagonal]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  by_cases h1 : G.Adj v u <;> by_cases h2 : G.Adj v w <;> by_cases hn : u = w <;>
    simp [h1, h2, hn]

theorem starOperator_expanded (v : V) (f : E) :
    energy (P.starOperator v) f = energy (P.Q v) f +
      (∑ u, if G.Adj v u then P.beta v u * ⟪P.Q v f, P.Q u f⟫_ℝ else 0) +
      ∑ u, ∑ w, if G.Adj v u ∧ G.Adj v w ∧ u ≠ w then ⟪P.Q u f, P.Q w f⟫_ℝ else 0 := by
  rw [P.starOperator_energy, P.incidence_energy]
  have h := P.neighbour_excess_energy v f
  linarith

theorem sum_star_energy (hg : 5 ≤ G.egirth) (f : E) :
    (∑ v, energy (P.starOperator v) f) = energy P.laplacian f +
      edgePairSum G (fun v u => ⟪P.Q v f, P.Q u f⟫_ℝ) +
      secondPairSum G (fun v u => ⟪P.Q v f, P.Q u f⟫_ℝ) := by
  simp_rw [P.starOperator_expanded]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← P.laplacian_sum_energy, star_second_sum G hg]
  rw [show (∑ v, ∑ u, if G.Adj v u then P.beta v u * ⟪P.Q v f, P.Q u f⟫_ℝ else 0) =
    edgePairSum G (fun v u => ⟪P.Q v f, P.Q u f⟫_ℝ) from
      weighted_edge_sum G _ (fun v u => real_inner_comm _ _)]

theorem distant_energy_nonneg (f : E) :
    0 ≤ distantPairSum G (fun v u => ⟪P.Q v f, P.Q u f⟫_ℝ) := by
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro u _
  split_ifs with h
  · exact P.nonadjacent_pair_nonneg v u h.2.1 f
  · exact le_rfl

/-- Equation sg-global-decomposition, in its exact quadratic-form form.
The distant sum is over ordered pairs, so it equals twice the unordered sum. -/
theorem global_decomposition (hg : 5 ≤ G.egirth) (f : E) :
    ‖P.laplacian f‖ ^ 2 = (∑ v, energy (P.starOperator v) f) +
      distantPairSum G (fun v u => ⟪P.Q v f, P.Q u f⟫_ℝ) := by
  have hb := norm_sum_sq_sub_diagonal (fun v => P.Q v f)
  have he : (∑ v, P.Q v f) = P.laplacian f := by simp only [laplacian, LinearMap.sum_apply]
  rw [he, ← P.laplacian_energy, off_diagonal_partition G hg] at hb
  rw [P.sum_star_energy hg]
  linarith

theorem square_laplacian_energy (f : E) : energy (P.laplacian.comp P.laplacian) f = ‖P.laplacian f‖ ^ 2 := by
  rw [energy, LinearMap.comp_apply, ← P.laplacian_symmetric f (P.laplacian f), real_inner_self_eq_norm_sq]

end GraphProjections
end
end CI2ZF.Appendix.Girth
