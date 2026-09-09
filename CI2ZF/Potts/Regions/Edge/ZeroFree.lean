import CI2ZF.Coupling.Edge.GeometryCI
import CI2ZF.Potts.Theorems.GraphClassPottsTransfer

/-! The edge-Potts zero-free corollary follows from the actual uniformly
coupled line-graph family, with induced closure witnessed by endpoint
geometry restrictions. -/

namespace CI2ZF.Appendix.Edge
open PottsCI CI2ZF.Potts EndpointGeometry Metric
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false
universe u v

/-- The induced-closed family of line graphs represented by finite simple
endpoint geometries with maximum endpoint load Δ. -/
def edgeGraphClass (Δ : ℕ) : GraphClass.{u} where
  contains {E} _ H := ∃ (V : Type u) (hV : Fintype V),
    let : Fintype V := hV
    ∃ g : EndpointGeometry V E, g.edgeGraph = H ∧ ∀ v, (g.incidentEdges v).card ≤ Δ
  comap_mem := by
    intro E F _ _ H ι hH
    obtain ⟨V, hV, g, hg, hd⟩ := hH
    let : Fintype V := hV
    refine ⟨V, hV, g.restrict ι, ?_, ?_⟩
    · exact (g.restrict_edgeGraph ι).trans (congrArg (fun G => G.comap ι) hg)
    · intro v
      exact (g.restrict_incident_le ι v).trans (hd v)

lemma edgeGraphClass_degree {E : Type u} [Fintype E] {Δ : ℕ}
    (H : SimpleGraph E) (hH : (edgeGraphClass Δ).contains H) :
    ∀ e, H.degree e ≤ 2 * Δ - 2 := by
  obtain ⟨V, hV, g, hg, hd⟩ := hH
  let : Fintype V := hV
  rw [← hg]
  intro e
  exact Nat.le_sub_of_add_le (g.edgeGraph_degree_bound hd e)

lemma lineGraph_mem_edgeGraphClass {V : Type u} [Fintype V] {Δ : ℕ}
    (G : SimpleGraph V) (hd : ∀ v, G.degree v ≤ Δ) :
    (edgeGraphClass Δ).contains G.lineGraph :=
  ⟨V, inferInstance, ofSimpleGraph G, ofSimpleGraph_edgeGraph G,
    fun v => (ofSimpleGraph_incident_le G v).trans (hd v)⟩

theorem edgeGraphClass_rootCoupling (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    GraphClassRootCouplingBound (edgeGraphClass.{u} Δ) C x ((Δ : ℝ) - 1) := by
  intro E _ H hH τ r a b ha hb
  obtain ⟨V, hV, g, hg, hd⟩ := hH
  let : Fintype V := hV
  subst H
  exact g.root_children_ci τ r a b hΔ hd hq x hx1 ha hb

theorem edgeGraphClass_transferInputs (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) :
    GraphClassTransferInputs (edgeGraphClass.{u} Δ) C where
  hard := ⟨(Δ : ℝ) - 1, edgeGraphClass_rootCoupling C hΔ hq PinningData.hardParameter (by norm_num)⟩
  positive := by
    intro δ _ _
    exact ⟨(Δ : ℝ) - 1, fun x hx => edgeGraphClass_rootCoupling C hΔ hq x hx.2⟩

/-- `cor:soft-edge-zf`: one radius works for every finite graph with the
specified maximum degree and every arbitrary edge-colour pinning. The
unnormalized zero at the origin has exactly its pinned-conflict order. -/
theorem edge_potts_zero_free (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ τ : PartialColouring G.edgeSet C,
      (∀ z ∈ thickening eps pottsInterval, normalizedPartition τ G.lineGraph z ≠ 0) ∧
      (∀ z ∈ thickening eps pottsInterval,
        fullPartition τ G.lineGraph z = 0 ↔ z = 0 ∧ 0 < τ.pinnedConflictCount G.lineGraph) ∧
      (fullPolynomial τ G.lineGraph).rootMultiplicity 0 = τ.pinnedConflictCount G.lineGraph := by
  have hΔ1 : 1 ≤ Δ := (by decide : 1 ≤ 2).trans hΔ
  have hqL : (2 * Δ - 2) + 1 ≤ Fintype.card C :=
    (Nat.le_succ _).trans (lineGraph_colours_slack hΔ1 hq)
  obtain ⟨eps, heps, h⟩ := graph_class_potts_transfer_of_bounded
    (edgeGraphClass.{u} Δ) C (2 * Δ - 2) hqL
    (fun H hH => edgeGraphClass_degree H hH) (edgeGraphClass_transferInputs C hΔ1 hq)
  exact ⟨eps, heps, fun G hd τ => h G.lineGraph (lineGraph_mem_edgeGraphClass G hd) τ⟩

end
end CI2ZF.Appendix.Edge
