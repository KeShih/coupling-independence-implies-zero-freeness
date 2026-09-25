import ZeroFreeness.Potts.Geometry.SeparatorDegree
import ZeroFreeness.Potts.Geometry.BFSShells

/-! Exact invariance of the actual Potts finite products and sums under
vertex reindexing, specialized to the BFS inside/shell/outside split. -/

namespace ZeroFreeness.Potts.Separator

open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

variable {V W C R : Type*} [Fintype V] [Fintype W] [Fintype C]

/-- Relabel every actual free vertex and retain its boundary counts. -/
def relabelData (I : PinningData V C) (e : V ≃ W) : PinningData W C where
  graph := I.graph.comap e.symm
  boundaryCount w := I.boundaryCount (e.symm w)

def relabelColouring (e : V ≃ W) : (V → C) ≃ (W → C) where
  toFun σ := σ ∘ e.symm
  invFun τ := τ ∘ e
  left_inv σ := by funext v; simp
  right_inv τ := by funext w; simp

section Products
variable [CommSemiring R]

lemma edgeWeight_map (e : V ≃ W) (z : R) (τ : W → C) (p : Sym2 V) :
    edgeWeight z τ (e.toEmbedding.sym2Map p) = edgeWeight z (τ ∘ e) p := by
  induction p using Sym2.ind with
  | _ u v => rfl

/-- The equality holds for the true finite product at every activity,
including zero and complex activities. -/
theorem pinningProductWeight_relabel (I : PinningData V C) (e : V ≃ W)
    (z : R) (τ : W → C) :
    pinningProductWeight (relabelData I e) z τ = pinningProductWeight I z (τ ∘ e) := by
  unfold pinningProductWeight
  apply congrArg₂ (· * ·)
  · exact Fintype.prod_equiv e.symm _ _ (fun w => by simp [relabelData])
  · have hg : (relabelData I e).graph = I.graph.map e.toEmbedding :=
      SimpleGraph.comap_symm I.graph e
    have he : (relabelData I e).graph.edgeFinset =
        I.graph.edgeFinset.map e.toEmbedding.sym2Map := by
      rw [hg]
      convert SimpleGraph.edgeFinset_map e.toEmbedding I.graph using 1
      apply Finset.coe_injective
      simp only [SimpleGraph.coe_edgeFinset]
    rw [he, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro p _
    exact edgeWeight_map e z τ p

omit [CommSemiring R] in
theorem relabelData_constraintDegree (I : PinningData V C) (e : V ≃ W) (w : W) :
    (relabelData I e).constraintDegree w = I.constraintDegree (e.symm w) := by
  unfold PinningData.constraintDegree
  congr 1
  rw [graph_degree_eq_adj_sum, graph_degree_eq_adj_sum]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

omit [CommSemiring R] in
theorem relabelData_degreeBound (I : PinningData V C) (e : V ≃ W)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) : (relabelData I e).DegreeBound Δ := by
  intro w
  rw [relabelData_constraintDegree]
  exact hdegree _

end Products

variable [CommSemiring R]

/-- The genuine finite-sum partition, over any commutative semiring. -/
def pinningProductPartition (I : PinningData V C) (z : R) : R :=
  ∑ σ : V → C, pinningProductWeight I z σ

theorem pinningProductPartition_relabel (I : PinningData V C) (e : V ≃ W) (z : R) :
    pinningProductPartition (relabelData I e) z = pinningProductPartition I z := by
  unfold pinningProductPartition
  apply Fintype.sum_equiv (relabelColouring (C := C) e).symm
  intro τ
  exact pinningProductWeight_relabel I e z τ

theorem splitPinning_partition (I : PinningData V C) (v : V) (r : ℕ) (z : R) :
    partition (BFS.splitPinning I v r) z = pinningProductPartition I z := by
  convert pinningProductPartition_relabel I (BFS.splitEquiv I.graph v r) z using 1
  unfold partition pinningProductPartition weight pinningProductWeight
  congr 2
  exact Subsingleton.elim _ _

omit [CommSemiring R] in
theorem splitPinning_degreeBound (I : PinningData V C) (v : V) (r : ℕ)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) : (BFS.splitPinning I v r).DegreeBound Δ :=
  relabelData_degreeBound I (BFS.splitEquiv I.graph v r) hdegree

omit [CommSemiring R] in
theorem splitPinning_exterior_degreeBound (I : PinningData V C) (v : V) (r : ℕ)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) (ξ : BFS.Shell I.graph v r → C) :
    (exteriorData (BFS.splitPinning I v r) ξ).DegreeBound Δ :=
  exteriorData_degreeBound _ (BFS.splitPinning_separates I v r)
    (splitPinning_degreeBound I v r hdegree) ξ

end
end ZeroFreeness.Potts.Separator
