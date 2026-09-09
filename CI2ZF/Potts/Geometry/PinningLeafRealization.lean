import CI2ZF.Potts.Geometry.AmbientRealization
import CI2ZF.Potts.Geometry.SeparatorDegree

/-! Every finite boundary-count datum is realized by an actual graph:
one independently pinned leaf for each boundary occurrence. Colours are
indexed by `Fin`, so the ambient vertex universe remains that of `V`. -/
namespace CI2ZF.Potts.PinningLeaves
open PottsCI Separator
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
variable {V : Type u} {C : Type v} [Fintype V] [Fintype C]

def Leaf (I : PinningData V C) :=
  Σ w : V, Σ i : Fin (Fintype.card C), Fin (I.boundaryCount w ((Fintype.equivFin C).symm i))

instance leafFintype (I : PinningData V C) : Fintype (Leaf I) :=
  inferInstanceAs (Fintype (Σ w : V, Σ i : Fin (Fintype.card C),
    Fin (I.boundaryCount w ((Fintype.equivFin C).symm i))))

abbrev Vertex (I : PinningData V C) := V ⊕ Leaf I

def colour (I : PinningData V C) (l : Leaf I) : C := (Fintype.equivFin C).symm l.2.1

def Adj (I : PinningData V C) : Vertex I → Vertex I → Prop
  | Sum.inl w, Sum.inl z => I.graph.Adj w z
  | Sum.inl w, Sum.inr l => w = l.1
  | Sum.inr l, Sum.inl w => l.1 = w
  | Sum.inr _, Sum.inr _ => False

def graph (I : PinningData V C) : SimpleGraph (Vertex I) where
  Adj := Adj I
  symm := ⟨by
    intro w z h
    cases w <;> cases z
    · exact I.graph.adj_symm h
    · exact h.symm
    · exact h.symm
    · exact h⟩
  loopless := ⟨by
    intro w
    cases w with
    | inl w => exact I.graph.irrefl
    | inr l => exact not_false⟩

omit [Fintype V] in
@[simp] theorem graph_adj_free (I : PinningData V C) (w z : V) :
    (graph I).Adj (Sum.inl w) (Sum.inl z) ↔ I.graph.Adj w z := Iff.rfl

omit [Fintype V] in
@[simp] theorem graph_adj_free_leaf (I : PinningData V C) (w : V) (l : Leaf I) :
    (graph I).Adj (Sum.inl w) (Sum.inr l) ↔ w = l.1 := Iff.rfl

omit [Fintype V] in
@[simp] theorem graph_adj_leaf_free (I : PinningData V C) (l : Leaf I) (w : V) :
    (graph I).Adj (Sum.inr l) (Sum.inl w) ↔ l.1 = w := Iff.rfl

omit [Fintype V] in
@[simp] theorem graph_adj_leaf_leaf (I : PinningData V C) (l m : Leaf I) :
    ¬ (graph I).Adj (Sum.inr l) (Sum.inr m) := not_false

/-- Summing over the real leaf vertices counts each labelled boundary
occurrence with its exact multiplicity. -/
theorem sum_leaves (I : PinningData V C) (f : V → C → ℕ) :
    (∑ l : Leaf I, f l.1 (colour I l)) =
      ∑ w : V, ∑ c : C, I.boundaryCount w c * f w c := by
  change (∑ l : (Σ w : V, Σ i : Fin (Fintype.card C),
    Fin (I.boundaryCount w ((Fintype.equivFin C).symm i))),
      f l.1 ((Fintype.equivFin C).symm l.2.1)) = _
  simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro w _
  exact Fintype.sum_equiv (Fintype.equivFin C).symm _ _ (fun _ => rfl)

theorem degree_free (I : PinningData V C) (w : V) :
    (graph I).degree (Sum.inl w) = I.constraintDegree w := by
  rw [graph_degree_eq_adj_sum, Fintype.sum_sum_type]
  simp only [graph_adj_free, graph_adj_free_leaf]
  have hs := sum_leaves I (fun z _ => if w = z then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at hs
  have hs' : (∑ l : Leaf I, if w = l.1 then 1 else 0) = ∑ c : C, I.boundaryCount w c := by
    rw [hs]
    simp [Finset.sum_ite_irrel]
  rw [hs', ← graph_degree_eq_adj_sum]
  rfl

theorem degree_leaf (I : PinningData V C) (l : Leaf I) :
    (graph I).degree (Sum.inr l) = 1 := by
  rw [graph_degree_eq_adj_sum, Fintype.sum_sum_type]
  simp only [graph_adj_leaf_free, graph_adj_leaf_leaf, if_false,
    Finset.sum_const_zero, add_zero]
  simp

/-- Leaf attachment preserves the full degree bound, provided degree
one is permitted. The original free degrees equal their constraint degrees. -/
theorem degree_le (I : PinningData V C) {Δ : ℕ} (hd : I.DegreeBound Δ) (hΔ : 1 ≤ Δ) :
    ∀ w : Vertex I, (graph I).degree w ≤ Δ := by
  intro w
  cases w with
  | inl w => exact (degree_free I w).trans_le (hd w)
  | inr l => exact (degree_leaf I l).trans_le hΔ

def freeEmbedding (I : PinningData V C) : V ↪ Vertex I := ⟨Sum.inl, Sum.inl_injective⟩

def pin (I : PinningData V C) : Vertex I → Option C :=
  Sum.elim (fun _ => none) (fun l => some (colour I l))

theorem boundary_count (I : PinningData V C) (w : V) (c : C) :
    I.boundaryCount w c =
      ∑ z : Vertex I, if (graph I).Adj (freeEmbedding I w) z ∧ pin I z = some c then 1 else 0 := by
  rw [Fintype.sum_sum_type]
  simp only [freeEmbedding, Function.Embedding.coeFn_mk, pin, Sum.elim_inl,
    Sum.elim_inr, graph_adj_free_leaf, reduceCtorEq, and_false, if_false,
    Finset.sum_const_zero, zero_add, Option.some.injEq]
  rw [sum_leaves I (fun z d => if w = z ∧ d = c then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, ite_and]
  simp

/-- A directly checkable ambient realization, with all new vertices pinned
and with no change to any normalized free-configuration weight. -/
def realization (I : PinningData V C) : AmbientRealization I (graph I) where
  free := freeEmbedding I
  pin := pin I
  free_unpinned _ := rfl
  graph_eq := rfl
  count_eq w c := by
    convert boundary_count I w c using 1
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> rfl

/-- Every bounded datum has an ambient graph in the same degree class. -/
theorem exists_bounded_realization (I : PinningData V C) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hΔ : 1 ≤ Δ) :
    ∃ G : SimpleGraph (Vertex I), (∀ w, G.degree w ≤ Δ) ∧ Nonempty (AmbientRealization I G) :=
  ⟨graph I, degree_le I hd hΔ, ⟨realization I⟩⟩

end
end CI2ZF.Potts.PinningLeaves
