import CI2ZF.Holant.ShellSelection

/-! The fixed ambient interaction graph on the same unordered-edge type as
the polynomial. Nonedges are isolated, and restricting to actual graph edges
recovers the usual line graph. Every residual free-edge set inherits its
compatibility and degree bound. -/
namespace CI2ZF.Holant
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The original line graph, with isolated nonedges added to preserve the
ambient `Sym2 V` edge type through every deletion and residual pinning. -/
def ambientLineGraph (G : SimpleGraph V) : SimpleGraph (Sym2 V) where
  Adj a b := a ∈ G.edgeFinset ∧ b ∈ G.edgeFinset ∧ a ≠ b ∧
    ∃ v, v ∈ a ∧ v ∈ b
  symm.symm a b h := by
    obtain ⟨ha, hb, hn, v, hva, hvb⟩ := h
    exact ⟨hb, ha, Ne.symm hn, v, hvb, hva⟩

@[simp] theorem ambientLineGraph_adj (G : SimpleGraph V) (a b : Sym2 V) :
    (ambientLineGraph G).Adj a b ↔ a ∈ G.edgeFinset ∧ b ∈ G.edgeFinset ∧
      a ≠ b ∧ ∃ v, v ∈ a ∧ v ∈ b := Iff.rfl

/-- On genuine input edges this is exactly Mathlib's line-graph relation. -/
theorem ambientLineGraph_adj_iff_lineGraph (G : SimpleGraph V) (a b : G.edgeSet) :
    (ambientLineGraph G).Adj a.val b.val ↔ G.lineGraph.Adj a b := by
  rw [ambientLineGraph_adj, SimpleGraph.lineGraph_adj_iff_exists]
  simp [Subtype.ext_iff]

theorem ambientLineGraph_degree_nonedge (G : SimpleGraph V) (e : Sym2 V)
    (he : e ∉ G.edgeFinset) : (ambientLineGraph G).degree e = 0 := by
  change ((ambientLineGraph G).neighborFinset e).card = 0
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have h : (ambientLineGraph G).Adj e a := by simpa using ha
  exact he h.1

theorem ambientLineGraph_degree_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) (e : Sym2 V) :
    (ambientLineGraph G).degree e ≤ 2 * (Δ - 1) := by
  by_cases he : e ∈ G.edgeFinset
  · rcases e with ⟨u, v⟩
    have huv : G.Adj u v := by simpa using he
    have hu : s(u, v) ∈ G.incidenceFinset u := by
      simpa using G.mk'_mem_incidenceSet_left_iff.mpr huv
    have hv : s(u, v) ∈ G.incidenceFinset v := by
      simpa using G.mk'_mem_incidenceSet_right_iff.mpr huv
    have hsub : (ambientLineGraph G).neighborFinset s(u, v) ⊆
        (G.incidenceFinset u).erase s(u, v) ∪ (G.incidenceFinset v).erase s(u, v) := by
      intro a ha
      have hadj : (ambientLineGraph G).Adj s(u, v) a := by simpa using ha
      obtain ⟨_, hae, hne, w, hw, hwa⟩ := hadj
      have hw' : w = u ∨ w = v := by simpa using hw
      rcases hw' with rfl | rfl
      · apply mem_union.mpr (Or.inl _)
        refine mem_erase.mpr ⟨Ne.symm hne, ?_⟩
        exact (G.mem_incidenceFinset _ _).mpr ⟨by simpa using hae, hwa⟩
      · apply mem_union.mpr (Or.inr _)
        refine mem_erase.mpr ⟨Ne.symm hne, ?_⟩
        exact (G.mem_incidenceFinset _ _).mpr ⟨by simpa using hae, hwa⟩
    calc
      (ambientLineGraph G).degree s(u, v) =
          ((ambientLineGraph G).neighborFinset s(u, v)).card := rfl
      _ ≤ ((G.incidenceFinset u).erase s(u, v) ∪
            (G.incidenceFinset v).erase s(u, v)).card := card_le_card hsub
      _ ≤ ((G.incidenceFinset u).erase s(u, v)).card +
            ((G.incidenceFinset v).erase s(u, v)).card := card_union_le _ _
      _ = (G.degree u - 1) + (G.degree v - 1) := by
        rw [card_erase_of_mem hu, card_erase_of_mem hv,
          G.card_incidenceFinset_eq_degree, G.card_incidenceFinset_eq_degree]
      _ ≤ 2 * (Δ - 1) := by have := hΔ u; have := hΔ v; omega
  · rw [ambientLineGraph_degree_nonedge G e he]
    exact Nat.zero_le _

/-- Compatibility is inherited by every normalized residual whose free
edges are a subset of the original graph edges. -/
theorem ambientLineGraph_compatible (G : SimpleGraph V)
    (H : NormalizedInstance V (Sym2 V)) (hinc : H.incidence = graphIncidence)
    (hE : H.edges ⊆ G.edgeFinset) : AmbientCompatible H (ambientLineGraph G) := by
  intro a ha b hb hne v hai hbi
  exact ⟨hE ha, hE hb, hne, v, by simpa [hinc, graphIncidence] using hai,
    by simpa [hinc, graphIncidence] using hbi⟩

end
end CI2ZF.Holant
