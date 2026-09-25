import ZeroFreeness.Potts.Geometry.BFSShellMarginals
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic

/-!
# Edge-interaction geometry for Holant

The interaction graph is the actual line graph of the input simple graph.
Its degree bound is proved from the two endpoint incidence sets.  The BFS
separator and shell transport estimates therefore apply to edge variables,
with no graph-size dependent assumptions.
-/

namespace ZeroFreeness.Holant

open Finset PottsCI PottsCI.FinDist
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Holant edge interaction graph has exactly the usual line-graph
adjacency: distinct input edges sharing an endpoint. -/
abbrev interactionGraph (G : SimpleGraph V) := G.lineGraph

/-- Every neighboring edge is incident to one of the two root endpoints,
and the root edge itself is removed from both incidence sets. -/
theorem lineGraph_neighbor_image_subset (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) :
    ((G.lineGraph.neighborFinset ⟨s(u, v), huv⟩).image Subtype.val) ⊆
      (G.incidenceFinset u).erase s(u, v) ∪ (G.incidenceFinset v).erase s(u, v) := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := mem_image.mp ha
  have hadj : G.lineGraph.Adj ⟨s(u, v), huv⟩ e := by simpa using he
  obtain ⟨hne, w, hw, hwe⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
  have hne' : e.val ≠ s(u, v) := by
    intro h
    apply hne
    exact Subtype.ext h.symm
  have hw' : w = u ∨ w = v := by simpa using hw
  rcases hw' with rfl | rfl
  · apply mem_union.mpr <| Or.inl _
    exact mem_erase.mpr ⟨hne', (G.mem_incidenceFinset _ _).mpr
      ((G.edge_mem_incidenceSet_iff).mpr hwe)⟩
  · apply mem_union.mpr <| Or.inr _
    exact mem_erase.mpr ⟨hne', (G.mem_incidenceFinset _ _).mpr
      ((G.edge_mem_incidenceSet_iff).mpr hwe)⟩

/-- The exact maximum-degree bound for the edge interaction graph. -/
theorem lineGraph_degree_le (G : SimpleGraph V) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (e : G.edgeSet) :
    G.lineGraph.degree e ≤ 2 * (Δ - 1) := by
  rcases e with ⟨⟨u, v⟩, huv⟩
  have hu : s(u, v) ∈ G.incidenceFinset u := by
    simpa using (G.mk'_mem_incidenceSet_left_iff.mpr huv)
  have hv : s(u, v) ∈ G.incidenceFinset v := by
    simpa using (G.mk'_mem_incidenceSet_right_iff.mpr huv)
  calc
    G.lineGraph.degree ⟨s(u, v), huv⟩ =
        ((G.lineGraph.neighborFinset ⟨s(u, v), huv⟩).image Subtype.val).card := by
      rw [card_image_of_injective _ Subtype.val_injective]
      rfl
    _ ≤ ((G.incidenceFinset u).erase s(u, v) ∪
          (G.incidenceFinset v).erase s(u, v)).card :=
      card_le_card (lineGraph_neighbor_image_subset G huv)
    _ ≤ ((G.incidenceFinset u).erase s(u, v)).card +
          ((G.incidenceFinset v).erase s(u, v)).card := card_union_le _ _
    _ = (G.degree u - 1) + (G.degree v - 1) := by
      rw [card_erase_of_mem hu, card_erase_of_mem hv,
        G.card_incidenceFinset_eq_degree, G.card_incidenceFinset_eq_degree]
    _ ≤ 2 * (Δ - 1) := by have := hdeg u; have := hdeg v; omega

/-- An edge ball has uniformly bounded size at each fixed radius. -/
theorem edge_ball_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (e : G.edgeSet) (r : ℕ) :
    (BFS.ball G.lineGraph e r).card ≤ (2 * (Δ - 1) + 1) ^ r :=
  BFS.ball_card_le_pow G.lineGraph e r _ (lineGraph_degree_le G Δ hdeg)

theorem edge_ball_card_le_geom (G : SimpleGraph V) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (e : G.edgeSet) (r : ℕ) :
    (BFS.ball G.lineGraph e r).card ≤
      ∑ k ∈ range (r + 1), (2 * (Δ - 1)) ^ k :=
  BFS.ball_card_le_geom G.lineGraph e r _ (lineGraph_degree_le G Δ hdeg)

/-- No original vertex can meet both an inside edge and an outside edge.
Thus no Holant factor straddles the two sides of the edge shell. -/
theorem no_vertex_inside_outside (G : SimpleGraph V) (e : G.edgeSet) (r : ℕ)
    {i o : G.edgeSet} (hi : i ∈ BFS.ball G.lineGraph e r)
    (ho : o ∉ BFS.ball G.lineGraph e (r + 1)) :
    ¬ ∃ v : V, v ∈ (i.val : Sym2 V) ∧ v ∈ (o.val : Sym2 V) := by
  intro h
  apply BFS.no_edge_inside_outside hi ho
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, h⟩
  intro hio
  subst o
  exact ho (BFS.ball_mono G.lineGraph e (by omega) hi)

/-- This includes the root factor itself, since the root edge is in every
nonnegative-radius inside ball. -/
theorem no_vertex_root_outside (G : SimpleGraph V) (e : G.edgeSet) (r : ℕ)
    {o : G.edgeSet} (ho : o ∉ BFS.ball G.lineGraph e (r + 1)) :
    ¬ ∃ v : V, v ∈ (e.val : Sym2 V) ∧ v ∈ (o.val : Sym2 V) :=
  no_vertex_inside_outside G e r (BFS.center_mem_ball G.lineGraph e r) ho

/-- If a shell is empty, the whole root edge-component is a bounded local
instance. Disconnected components never enter its ball. -/
theorem edge_component_card_of_empty_shell (G : SimpleGraph V) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (e : G.edgeSet) (r : ℕ)
    (hs : BFS.shell G.lineGraph e (r + 1) = ∅) :
    (univ.filter fun w => G.lineGraph.Reachable e w).card ≤
      ∑ k ∈ range (r + 1), (2 * (Δ - 1)) ^ k :=
  BFS.component_card_le_geom_of_shell_empty G.lineGraph e r _
    (lineGraph_degree_le G Δ hdeg) hs

/-- Actual Boolean shell marginals share one common transportation budget. -/
theorem sum_W_edge_shell_le (G : SimpleGraph V) (e : G.edgeSet)
    (μ ν : FinDist (G.edgeSet → Bool)) (offset R : ℕ) :
    (∑ i : Fin R, W ham (BFS.sphereMarginal μ G.lineGraph e (offset + i.val + 1))
      (BFS.sphereMarginal ν G.lineGraph e (offset + i.val + 1))) ≤ W ham μ ν :=
  BFS.sum_W_sphereMarginal_le μ ν G.lineGraph e offset R

/-- A full edge CI estimate selects a genuine sphere at radius `1..R`
whose marginal transportation distance is at most the CI budget divided by R. -/
theorem exists_low_W_edge_shell (G : SimpleGraph V) (e : G.edgeSet)
    (μ ν : FinDist (G.edgeSet → Bool)) {R : ℕ} (hR : 0 < R) {C : ℝ}
    (hCI : W ham μ ν ≤ C) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧
      W ham (BFS.sphereMarginal μ G.lineGraph e r)
        (BFS.sphereMarginal ν G.lineGraph e r) ≤ C / R := by
  have : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  obtain ⟨i, hi⟩ := exists_low_hamming_shell μ ν (BFS.shellLabelFrom G.lineGraph e 0 R) hCI
  refine ⟨0 + i.val + 1, by omega, by omega, ?_⟩
  have hW := BFS.W_sphereMarginal_le μ ν G.lineGraph e 0 R i
  simpa using hW.trans hi

end
end ZeroFreeness.Holant
