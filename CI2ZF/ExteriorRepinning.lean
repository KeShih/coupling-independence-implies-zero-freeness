import CI2ZF.OptionPinning
import CI2ZF.PinningPolynomial

/-! Temporarily unpin one actual separator vertex. Its normalized
one-vertex children are exactly the exterior instances for the different
colours at that separator coordinate. -/

namespace CI2ZF.Potts.Separator

open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

def unpinShellEmbedding (s : S) : Option O ↪ Vertex U S O where
  toFun
    | none => Sum.inr (Sum.inl s)
    | some o => Sum.inr (Sum.inr o)
  inj' := by intro u v he; cases u <;> cases v <;> simp_all

@[simp] lemma unpinShellEmbedding_none (s : S) :
    (unpinShellEmbedding s : Option O ↪ Vertex U S O) none = Sum.inr (Sum.inl s) := rfl

@[simp] lemma unpinShellEmbedding_some (s : S) (o : O) :
    (unpinShellEmbedding s : Option O ↪ Vertex U S O) (some o) = outsideEmbedding o := rfl

/-- The common exterior with `s` free and all other separator coordinates
still pinned. Original boundary occurrences are retained at every vertex. -/
def unpinnedExteriorData (I : PinningData (Vertex U S O) C) (ξ : S → C) (s : S) :
    PinningData (Option O) C where
  graph := I.graph.comap (unpinShellEmbedding s)
  boundaryCount w c := I.boundaryCount (unpinShellEmbedding s w) c +
    ∑ t ∈ Finset.univ.erase s,
      if I.graph.Adj (Sum.inr (Sum.inl t)) (unpinShellEmbedding s w) ∧ ξ t = c then 1 else 0

lemma exterior_update_count (I : PinningData (Vertex U S O) C) (ξ : S → C)
    (s : S) (a c : C) (o : O) :
    (exteriorData I (Function.update ξ s a)).boundaryCount o c =
      (unpinnedExteriorData I ξ s).boundaryCount (some o) c +
        if I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o) ∧ c = a then 1 else 0 := by
  unfold exteriorData unpinnedExteriorData
  simp only [unpinShellEmbedding_some]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
  have he : (∑ t ∈ Finset.univ.erase s,
      if I.graph.Adj (Sum.inr (Sum.inl t)) (outsideEmbedding o) ∧ Function.update ξ s a t = c
        then 1 else 0) =
      ∑ t ∈ Finset.univ.erase s,
        if I.graph.Adj (Sum.inr (Sum.inl t)) (outsideEmbedding o) ∧ ξ t = c then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Function.update_of_ne (Finset.mem_erase.mp ht).1]
  rw [he, Function.update_self]
  simp only [eq_comm (a := a) (b := c)]
  rw [← Nat.add_assoc]
  congr 2

/-- This is an equality of the actual induced data, not merely an
assumed identity between exterior partition functions. -/
theorem optionChildData_unpinnedExterior (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (s : S) (a : C) :
    optionChildData (unpinnedExteriorData I ξ s) a = exteriorData I (Function.update ξ s a) := by
  have hg : (optionChildData (unpinnedExteriorData I ξ s) a).graph =
      (exteriorData I (Function.update ξ s a)).graph := rfl
  have hb : (optionChildData (unpinnedExteriorData I ξ s) a).boundaryCount =
      (exteriorData I (Function.update ξ s a)).boundaryCount := by
    funext o c
    rw [optionChildData_count, exterior_update_count]
    rfl
  exact congrArg₂ PinningData.mk hg hb

/-- The child partition identity holds at every complex activity, including
the hard endpoint, because pinned-only conflicts are omitted. -/
theorem unpinnedExterior_child_partition (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) (ξ : S → C) (s : S) (a : C) (z : ℂ) :
    pinningProductPartition (optionChildData (unpinnedExteriorData I ξ s) a) z =
      exteriorPartition I z (Function.update ξ s a) := by
  rw [optionChildData_unpinnedExterior]
  unfold pinningProductPartition exteriorPartition
  apply Finset.sum_congr rfl
  intro ζ _
  exact (exteriorWeight_eq_pinningProductWeight I hsep z _ ζ).symm

lemma unpinnedExterior_boundary_sum (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (s : S) (w : Option O) :
    (∑ c : C, (unpinnedExteriorData I ξ s).boundaryCount w c) =
      (∑ c : C, I.boundaryCount (unpinShellEmbedding s w) c) +
        ∑ t ∈ Finset.univ.erase s,
          if I.graph.Adj (Sum.inr (Sum.inl t)) (unpinShellEmbedding s w) then 1 else 0 := by
  simp only [unpinnedExteriorData, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases he : I.graph.Adj (Sum.inr (Sum.inl t)) (unpinShellEmbedding s w)
  · simp only [he, true_and, if_true]
    simp [eq_comm]
  · simp only [he, false_and, if_false, Finset.sum_const_zero]

lemma unpinnedExterior_free_degree_le (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (s : S) (w : Option O) :
    (unpinnedExteriorData I ξ s).graph.degree w +
        (∑ t ∈ Finset.univ.erase s,
          if I.graph.Adj (Sum.inr (Sum.inl t)) (unpinShellEmbedding s w) then 1 else 0) ≤
      I.graph.degree (unpinShellEmbedding s w) := by
  have hs := Finset.sum_erase_add Finset.univ
    (fun t : S => if I.graph.Adj (unpinShellEmbedding s w) (Sum.inr (Sum.inl t)) then 1 else 0)
    (Finset.mem_univ s)
  have he (t : S) :
      (if I.graph.Adj (Sum.inr (Sum.inl t)) (unpinShellEmbedding s w) then 1 else 0) =
      (if I.graph.Adj (unpinShellEmbedding s w) (Sum.inr (Sum.inl t)) then 1 else 0) := by
    rw [I.graph.adj_comm]
  simp only [he, graph_degree_eq_adj_sum, Fintype.sum_sum_type, Fintype.sum_option]
  change (if I.graph.Adj (unpinShellEmbedding s w) (Sum.inr (Sum.inl s)) then 1 else 0) +
      (∑ o : O, if I.graph.Adj (unpinShellEmbedding s w) (outsideEmbedding o) then 1 else 0) +
      (∑ t ∈ Finset.univ.erase s,
        if I.graph.Adj (unpinShellEmbedding s w) (Sum.inr (Sum.inl t)) then 1 else 0) ≤ _
  have hO : (∑ o : O,
      if I.graph.Adj (unpinShellEmbedding s w) (outsideEmbedding o) then 1 else 0) =
      ∑ o : O, if I.graph.Adj (unpinShellEmbedding s w) (Sum.inr (Sum.inr o)) then 1 else 0 := rfl
  omega

/-- Temporarily unpinning a separator coordinate stays in the same
constraint-degree class; inside vertices have simply been removed. -/
theorem unpinnedExterior_constraintDegree_le (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (s : S) (w : Option O) :
    (unpinnedExteriorData I ξ s).constraintDegree w ≤
      I.constraintDegree (unpinShellEmbedding s w) := by
  rw [PinningData.constraintDegree, unpinnedExterior_boundary_sum, PinningData.constraintDegree]
  have hd := unpinnedExterior_free_degree_le I ξ s w
  omega

theorem unpinnedExterior_degreeBound (I : PinningData (Vertex U S O) C)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) (ξ : S → C) (s : S) :
    (unpinnedExteriorData I ξ s).DegreeBound Δ := by
  intro w
  exact (unpinnedExterior_constraintDegree_le I ξ s w).trans (hdegree _)

/-- The temporary unpinning still has fewer free vertices than the
original instance whenever the inside is nonempty. -/
theorem unpinnedExterior_card_lt [Nonempty U] (s : S) :
    Fintype.card (Option O) < Fintype.card (Vertex U S O) := by
  have hU := Fintype.card_pos (α := U)
  have hS : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨s⟩
  simp only [Fintype.card_option, Vertex, Fintype.card_sum]
  omega

end
end CI2ZF.Potts.Separator
