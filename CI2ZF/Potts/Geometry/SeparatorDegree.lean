import CI2ZF.Potts.Geometry.SeparatorExterior

/-! The actual separator exterior preserves the original constraint-degree
budget: separator edges become boundary occurrences, while outside edges
remain free. This is the closure property needed for induction. -/

namespace CI2ZF.Potts.Separator

open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

lemma graph_degree_eq_adj_sum {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    G.degree v = ∑ w : V, if G.Adj v w then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  simp only [Finset.card_filter]

/-- Summing the newly pinned colour counts counts each separator edge once. -/
theorem exteriorData_boundary_sum (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (o : O) :
    (∑ c : C, (exteriorData I ξ).boundaryCount o c) =
      (∑ c : C, I.boundaryCount (outsideEmbedding o) c) +
        ∑ s : S, if I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o) then 1 else 0 := by
  simp only [exteriorData, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hadj : I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o)
  · change I.graph.Adj (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inr o)) at hadj
    simp [hadj, eq_comm]
  · change ¬ I.graph.Adj (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inr o)) at hadj
    simp [hadj]

/-- All neighbours of an exterior vertex are outside or on the separator. -/
theorem exteriorData_free_degree (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) (ξ : S → C) (o : O) :
    (exteriorData I ξ).graph.degree o +
        (∑ s : S, if I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o) then 1 else 0) =
      I.graph.degree (outsideEmbedding o) := by
  simp only [graph_degree_eq_adj_sum, Fintype.sum_sum_type]
  have hz (u : U) : ¬ I.graph.Adj (outsideEmbedding o) (Sum.inl u) :=
    fun hh => hsep u o hh.symm
  simp only [hz, if_false, Finset.sum_const_zero, zero_add]
  have hs (s : S) : I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o) ↔
      I.graph.Adj (outsideEmbedding o) (Sum.inr (Sum.inl s)) := I.graph.adj_comm _ _
  simp only [hs]
  change (∑ w : O, if I.graph.Adj (outsideEmbedding o) (outsideEmbedding w) then 1 else 0) +
      (∑ s : S, if I.graph.Adj (outsideEmbedding o) (Sum.inr (Sum.inl s)) then 1 else 0) = _
  exact Nat.add_comm _ _

/-- No constraint is lost or duplicated when the separator is pinned. -/
theorem exteriorData_constraintDegree (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) (ξ : S → C) (o : O) :
    (exteriorData I ξ).constraintDegree o = I.constraintDegree (outsideEmbedding o) := by
  rw [PinningData.constraintDegree, exteriorData_boundary_sum]
  unfold PinningData.constraintDegree
  rw [← exteriorData_free_degree I hsep ξ o]
  omega

/-- The actual smaller exterior remains in the same bounded-degree class. -/
theorem exteriorData_degreeBound (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) {Δ : ℕ} (hdegree : I.DegreeBound Δ) (ξ : S → C) :
    (exteriorData I ξ).DegreeBound Δ := by
  intro o
  rw [exteriorData_constraintDegree I hsep ξ o]
  exact hdegree (outsideEmbedding o)

end
end CI2ZF.Potts.Separator
