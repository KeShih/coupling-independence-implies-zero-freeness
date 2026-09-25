import ZeroFreeness.Potts.Geometry.PinningLeafCycles
import Mathlib.Combinatorics.SimpleGraph.Girth

/-! Attaching the independently pinned degree-one boundary vertices does
not change the cycles, extended girth, or girth of the free graph. -/
namespace ZeroFreeness.Potts.PinningLeaves
open PottsCI
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
variable {V : Type u} {C : Type v} [Fintype C]

/-- The original free graph is an induced subgraph of its leaf realization. -/
def freeGraphEmbedding (I : PinningData V C) : I.graph ↪g graph I where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-- Every cycle of the free graph remains a cycle after the leaves are attached. -/
theorem egirth_le_free (I : PinningData V C) : (graph I).egirth ≤ I.graph.egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro w p hp
  have hc := hp.map (f := (freeGraphEmbedding I).toHom) (freeGraphEmbedding I).injective
  simpa only [SimpleGraph.Walk.length_map] using SimpleGraph.egirth_le_length hc

/-- A cycle of the leaf realization projects to a free-graph cycle of
exactly the same length. Thus leaf attachment cannot create a shorter cycle. -/
theorem free_egirth_le (I : PinningData V C) : I.graph.egirth ≤ (graph I).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro x p hp
  obtain ⟨a, q, hq, hlen⟩ := exists_base_cycle_of_cycle I p hp
  simpa only [hlen] using SimpleGraph.egirth_le_length hq

/-- Extended girth is unchanged, including the value infinity for acyclic graphs. -/
@[simp] theorem egirth_eq (I : PinningData V C) : (graph I).egirth = I.graph.egirth :=
  le_antisymm (egirth_le_free I) (free_egirth_le I)

/-- Mathlib's natural-valued girth is unchanged as well. For forests,
both sides take its specified value zero. -/
@[simp] theorem girth_eq (I : PinningData V C) : (graph I).girth = I.graph.girth := by
  simp only [SimpleGraph.girth, egirth_eq]

/-- Attaching the pinned leaves neither creates nor removes cycles. -/
@[simp] theorem isAcyclic_iff (I : PinningData V C) :
    (graph I).IsAcyclic ↔ I.graph.IsAcyclic := by
  rw [← SimpleGraph.egirth_eq_top, egirth_eq, SimpleGraph.egirth_eq_top]

/-- A bounded boundary-count datum has a genuine leaf realization with
the same degree bound and the same extended girth and girth. -/
theorem exists_bounded_girth_realization [Fintype V] (I : PinningData V C) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hΔ : 1 ≤ Δ) :
    ∃ G : SimpleGraph (Vertex I), (∀ w, G.degree w ≤ Δ) ∧
      G.egirth = I.graph.egirth ∧ G.girth = I.graph.girth ∧
      Nonempty (AmbientRealization I G) :=
  ⟨graph I, degree_le I hd hΔ, egirth_eq I, girth_eq I, ⟨realization I⟩⟩

end
end ZeroFreeness.Potts.PinningLeaves
