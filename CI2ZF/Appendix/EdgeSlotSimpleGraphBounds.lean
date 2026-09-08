import CI2ZF.Appendix.EdgeSlotSimpleGraph

/-! The original maximum degree and colour threshold imply every hypothesis
of the finite weighted endpoint-label coupling for the constructed lift. -/

namespace CI2ZF.Appendix.Edge
open PottsCI
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

namespace EndpointGeometry
variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [Fintype R]

def incidentEdges (g : EndpointGeometry V E) (v : V) : Finset E :=
  Finset.univ.filter (fun e => v ∈ g.endpoints e)

@[simp] lemma mem_incidentEdges (g : EndpointGeometry V E) (v : V) (e : E) :
    e ∈ g.incidentEdges v ↔ v ∈ g.endpoints e := by simp [incidentEdges]

lemma incident_union (g : EndpointGeometry V E) (e : E) {v w : V}
    (he : g.endpoints e = {v, w}) :
    g.incidentEdges v ∪ g.incidentEdges w = insert e (g.edgeGraph.neighborFinset e) := by
  ext f
  simp only [Finset.mem_union, mem_incidentEdges, Finset.mem_insert,
    SimpleGraph.mem_neighborFinset]
  change (v ∈ g.endpoints f ∨ w ∈ g.endpoints f) ↔
    f = e ∨ (e ≠ f ∧ ∃ u, u ∈ g.endpoints e ∧ u ∈ g.endpoints f)
  constructor
  · intro hf
    by_cases hfe : f = e
    · exact Or.inl hfe
    · refine Or.inr ⟨Ne.symm hfe, ?_⟩
      rcases hf with hv | hw
      · exact ⟨v, by simp [he], hv⟩
      · exact ⟨w, by simp [he], hw⟩
  · rintro (rfl | ⟨_, u, hu, hf⟩)
    · exact Or.inl (by simp [he])
    · rw [he] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hf
      · exact Or.inr hf

lemma incident_inter (g : EndpointGeometry V E) (e : E) {v w : V}
    (hvw : v ≠ w) (he : g.endpoints e = {v, w}) :
    g.incidentEdges v ∩ g.incidentEdges w = {e} := by
  ext f
  simp only [Finset.mem_inter, mem_incidentEdges, Finset.mem_singleton]
  constructor
  · intro h
    have hv : v ∈ g.endpoints e := by rw [he]; exact Finset.mem_insert_self _ _
    have hw : w ∈ g.endpoints e := by rw [he]; simp
    exact (g.linear e f v w hv h.1 hw h.2 hvw).symm
  · rintro rfl
    simp [he]

lemma edgeGraph_degree_add_two (g : EndpointGeometry V E) (e : E) {v w : V}
    (hvw : v ≠ w) (he : g.endpoints e = {v, w}) :
    g.edgeGraph.degree e + 2 = (g.incidentEdges v).card + (g.incidentEdges w).card := by
  have h := Finset.card_union_add_card_inter (g.incidentEdges v) (g.incidentEdges w)
  rw [g.incident_union e he, g.incident_inter e hvw he, Finset.card_singleton,
    Finset.card_insert_of_notMem (by simp), SimpleGraph.card_neighborFinset_eq_degree] at h
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h

theorem edgeGraph_degree_bound (g : EndpointGeometry V E) {Δ : ℕ}
    (hdegree : ∀ v, (g.incidentEdges v).card ≤ Δ) (e : E) :
    g.edgeGraph.degree e + 2 ≤ 2 * Δ := by
  obtain ⟨v, w, hvw, he⟩ := Finset.card_eq_two.mp (g.endpoints_card e)
  rw [g.edgeGraph_degree_add_two e hvw he, two_mul]
  exact Nat.add_le_add (hdegree v) (hdegree w)

lemma slotSystem_incident (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ) (v : V) :
    (g.slotSystem κ hκ x hx b).incident v = g.incidentEdges v := rfl

lemma slotSystem_edgeDegree (g : EndpointGeometry V E) (κ : R → ℝ)
    (hκ : ∀ r, 0 ≤ κ r) (x : ℝ) (hx : 0 ≤ x) (b : E → C → ℕ) (e : E) :
    (g.slotSystem κ hκ x hx b).edgeDegree e = g.edgeGraph.degree e := by
  change ((g.slotSystem κ hκ x hx b).neighbours e).card = _
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext f
  simp only [FiniteSystem.neighbours, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]
  change (f ≠ e ∧ ∃ v, v ∈ g.endpoints e ∧ v ∈ g.endpoints f) ↔
    (e ≠ f ∧ ∃ v, v ∈ g.endpoints e ∧ v ∈ g.endpoints f)
  exact and_congr_left fun _ => ne_comm

lemma restrictedGraph_incident_le (G : SimpleGraph V) (ι : E ↪ G.edgeSet) (v : V) :
    (((ofSimpleGraph G).restrict ι).incidentEdges v).card ≤ G.degree v := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun e => (ι e).val)
  · intro e he
    change (ι e).val ∈ G.incidenceFinset v
    change e ∈ ((ofSimpleGraph G).restrict ι).incidentEdges v at he
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    exact (graphEndpoint_mem_iff G (ι e) v).mp ((mem_incidentEdges _ v e).mp he)
  · intro e _ f _ hef
    exact ι.injective (Subtype.ext hef)

lemma ofSimpleGraph_incident_le (G : SimpleGraph V) (v : V) :
    ((ofSimpleGraph G).incidentEdges v).card ≤ G.degree v :=
  restrictedGraph_incident_le G (Function.Embedding.refl _) v

theorem lineGraph_degree_bound (G : SimpleGraph V) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (e : G.edgeSet) : G.lineGraph.degree e + 2 ≤ 2 * Δ := by
  rw [← ofSimpleGraph_edgeGraph]
  exact (ofSimpleGraph G).edgeGraph_degree_bound
    (fun v => (ofSimpleGraph_incident_le G v).trans (hdegree v)) e

lemma freeEdgeGeometry_incident_le (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (v : V) : ((freeEdgeGeometry G τ).incidentEdges v).card ≤ G.degree v :=
  restrictedGraph_incident_le G (Function.Embedding.subtype _) v

theorem freeEdgeGeometry_slotSystem_bounds (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (κ : R → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (hsum : ∑ r, κ r = 1) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) :
    ((freeEdgeGeometry G τ).slotSystem κ hκ x hx (τ.boundaryCount G.lineGraph)).Bounds
      (fun _ => ∅) Δ := by
  apply slotSystem_bounds _ κ hκ hsum x hx hx1 _ hq
  · intro v
    rw [slotSystem_incident]
    exact (freeEdgeGeometry_incident_le G τ v).trans (hdegree v)
  · intro e
    rw [slotSystem_edgeDegree, freeEdgeGeometry_edgeGraph]
    change (τ.toPinningData G.lineGraph).constraintDegree e + 2 ≤ 2 * Δ
    rw [τ.constraintDegree_eq_degree]
    exact lineGraph_degree_bound G hdegree e.val

/-- The constructed finite approximants satisfy the exact finite weighted
coupling hypotheses uniformly in their number of slots. -/
theorem freeEdgeGeometry_approxSlotSystem_bounds (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) (n : ℕ) :
    ((freeEdgeGeometry G τ).approxSlotSystem x hx hx1 (τ.boundaryCount G.lineGraph) n).Bounds
      (fun _ => ∅) Δ :=
  freeEdgeGeometry_slotSystem_bounds G τ _ _ (finiteApproxSlotWeights_sum x hx hx1 _)
    x hx.le hx1.le hdegree hq

end EndpointGeometry
end
end CI2ZF.Appendix.Edge
