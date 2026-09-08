import CI2ZF.SeparatorDegree
import CI2ZF.BoundaryData

/-! Actual normalized one-vertex pinning with a distinguished free root.
The type `Option O` makes the common remaining vertex set exactly `O`. -/

namespace CI2ZF.Potts

open PottsCI Separator
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

variable {O C : Type*} [Fintype O] [Fintype C]

def optionMiddleData (I : PinningData (Option O) C) : PinningData O C where
  graph := I.graph.comap Option.some
  boundaryCount o := I.boundaryCount (some o)

def optionRootNeighbours (I : PinningData (Option O) C) : Finset O :=
  Finset.univ.filter (fun o => I.graph.Adj none (some o))

/-- Pin the root, dropping all conflicts that have become pinned-only. -/
def optionChildData (I : PinningData (Option O) C) (a : C) : PinningData O C :=
  addBoundarySet (optionMiddleData I) (optionRootNeighbours I) a

lemma optionChildData_count (I : PinningData (Option O) C) (a c : C) (o : O) :
    (optionChildData I a).boundaryCount o c = I.boundaryCount (some o) c +
      if I.graph.Adj none (some o) ∧ c = a then 1 else 0 := by
  simp only [optionChildData, addBoundarySet, optionMiddleData, optionRootNeighbours,
    Finset.mem_filter, Finset.mem_univ, true_and]

lemma optionMiddleData_degree (I : PinningData (Option O) C) (o : O) :
    (optionMiddleData I).graph.degree o + (if I.graph.Adj none (some o) then 1 else 0) =
      I.graph.degree (some o) := by
  simp only [graph_degree_eq_adj_sum, Fintype.sum_option]
  change (∑ w : O, if I.graph.Adj (some o) (some w) then 1 else 0) +
    (if I.graph.Adj none (some o) then 1 else 0) = _
  rw [I.graph.adj_comm none (some o)]
  omega

theorem optionChildData_constraintDegree (I : PinningData (Option O) C) (a : C) (o : O) :
    (optionChildData I a).constraintDegree o = I.constraintDegree (some o) := by
  have hb : (∑ c : C, (optionChildData I a).boundaryCount o c) =
      (∑ c : C, I.boundaryCount (some o) c) +
        (if I.graph.Adj none (some o) then 1 else 0) := by
    simp only [optionChildData_count, Finset.sum_add_distrib]
    by_cases he : I.graph.Adj none (some o) <;> simp [he]
  rw [PinningData.constraintDegree, hb]
  change (optionMiddleData I).graph.degree o + _ = _
  rw [PinningData.constraintDegree, ← optionMiddleData_degree I o]
  omega

theorem optionChildData_degreeBound (I : PinningData (Option O) C)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) (a : C) : (optionChildData I a).DegreeBound Δ := by
  intro o
  rw [optionChildData_constraintDegree]
  exact hdegree _

theorem optionRootNeighbours_card (I : PinningData (Option O) C) :
    (optionRootNeighbours I).card = I.graph.degree none := by
  rw [optionRootNeighbours, Finset.card_filter, graph_degree_eq_adj_sum, Fintype.sum_option]
  simp

theorem optionRootNeighbours_card_le (I : PinningData (Option O) C)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) : (optionRootNeighbours I).card ≤ Δ := by
  rw [optionRootNeighbours_card]
  have hd := hdegree none
  unfold PinningData.constraintDegree at hd
  omega

end
end CI2ZF.Potts
