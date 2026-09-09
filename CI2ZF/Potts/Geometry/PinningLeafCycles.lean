import CI2ZF.Potts.Geometry.PinningLeafRealization
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Adding the pinned degree-one vertices used by the leaf realization does
not create cycles. Every cycle projects to a cycle of the free graph with
exactly the same length. -/
namespace CI2ZF.Potts.PinningLeaves
open PottsCI
noncomputable section
universe u v
variable {V : Type u} {C : Type v} [Fintype C]

/-- A new leaf has exactly one possible neighbour. -/
theorem eq_free_of_adj_leaf (I : PinningData V C) (l : Leaf I)
    {w : Vertex I} (h : (graph I).Adj (Sum.inr l) w) :
    w = Sum.inl l.1 := by
  cases w with
  | inl w => exact congrArg Sum.inl ((graph_adj_leaf_free I l w).mp h).symm
  | inr m => exact False.elim (graph_adj_leaf_leaf I l m h)

/-- No simple cycle passes through any of the newly attached leaves. -/
theorem leaf_not_mem_cycle_support (I : PinningData V C) {x : Vertex I}
    (p : (graph I).Walk x x) (hp : p.IsCycle) (l : Leaf I) :
    Sum.inr l ∉ p.support := by
  classical
  intro hl
  let q := p.rotate (Sum.inr l) hl
  have hq : q.IsCycle := hp.rotate hl
  have hs : q.snd = Sum.inl l.1 := eq_free_of_adj_leaf I l (q.adj_snd hq.not_nil)
  have ht : q.penultimate = Sum.inl l.1 :=
    eq_free_of_adj_leaf I l ((q.adj_penultimate hq.not_nil).symm)
  exact hq.snd_ne_penultimate (hs.trans ht.symm)

/-- The support of any cycle belongs entirely to the original free vertices. -/
theorem cycle_support_subset_free (I : PinningData V C) {x : Vertex I}
    (p : (graph I).Walk x x) (hp : p.IsCycle) :
    ∀ w ∈ p.support, w ∈ Set.range (Sum.inl : V → Vertex I) := by
  intro w hw
  cases w with
  | inl w => exact ⟨w, rfl⟩
  | inr l => exact False.elim (leaf_not_mem_cycle_support I p hp l hw)

/-- Project the induced graph on the original free vertices back to the
original graph. -/
def freePartToBase (I : PinningData V C) :
    (graph I).induce (Set.range (Sum.inl : V → Vertex I)) →g I.graph where
  toFun w := Sum.elim id (fun l => l.1) w.val
  map_rel' := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ hab
    exact hab

theorem freePartToBase_injective (I : PinningData V C) :
    Function.Injective (freePartToBase I) := by
  rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ hab
  change a = b at hab
  subst b
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every cycle of the leaf realization is a cycle of the base graph, with
the same length. This also covers empty base graphs without extra hypotheses. -/
theorem exists_base_cycle_of_cycle (I : PinningData V C) {x : Vertex I}
    (p : (graph I).Walk x x) (hp : p.IsCycle) :
    ∃ a : V, ∃ q : I.graph.Walk a a, q.IsCycle ∧ q.length = p.length := by
  let hs := cycle_support_subset_free I p hp
  let q : ((graph I).induce (Set.range (Sum.inl : V → Vertex I))).Walk
      ⟨x, hs x p.start_mem_support⟩ ⟨x, hs x p.start_mem_support⟩ :=
    p.induce (Set.range (Sum.inl : V → Vertex I)) hs
  have hq : q.IsCycle := SimpleGraph.Walk.IsCycle.of_map
    (f := (SimpleGraph.Embedding.induce (Set.range (Sum.inl : V → Vertex I))).toHom) (by
    simpa only [q, SimpleGraph.Walk.map_induce] using hp)
  refine ⟨_, q.map (freePartToBase I),
    hq.map (freePartToBase_injective I), ?_⟩
  rw [SimpleGraph.Walk.length_map]
  have hlen := congrArg SimpleGraph.Walk.length (p.map_induce hs)
  simpa only [q, SimpleGraph.Walk.length_map] using hlen

end
end CI2ZF.Potts.PinningLeaves
