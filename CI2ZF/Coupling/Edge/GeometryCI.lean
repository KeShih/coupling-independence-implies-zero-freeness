import CI2ZF.Coupling.Edge.PottsCI

/-! The endpoint-geometry formulation is stable under induced pullbacks.
It provides the graph-class coupling interface needed by zero-free transfer. -/

namespace CI2ZF.Appendix.Edge
open PottsCI PottsCI.FinDist CI2ZF.Potts EndpointGeometry FiniteSystem Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
variable {V E F C : Type*} [Fintype V] [Fintype E] [Fintype F] [Fintype C] [Nonempty C]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq F := Classical.decEq F
local instance (priority := 2000) : DecidableEq C := Classical.decEq C

namespace EndpointGeometry

lemma restrict_edgeGraph (g : EndpointGeometry V E) (ι : F ↪ E) :
    (g.restrict ι).edgeGraph = g.edgeGraph.comap ι := by
  ext e f
  change (e ≠ f ∧ ∃ v, v ∈ g.endpoints (ι e) ∧ v ∈ g.endpoints (ι f)) ↔
    (ι e ≠ ι f ∧ ∃ v, v ∈ g.endpoints (ι e) ∧ v ∈ g.endpoints (ι f))
  exact and_congr_left fun _ => ⟨fun h heq => h (ι.injective heq), fun h heq => h (congrArg ι heq)⟩

lemma restrict_incident_le (g : EndpointGeometry V E) (ι : F ↪ E) (v : V) :
    ((g.restrict ι).incidentEdges v).card ≤ (g.incidentEdges v).card := by
  apply Finset.card_le_card_of_injOn ι
  · intro e he
    exact (mem_incidentEdges g v (ι e)).mpr ((mem_incidentEdges (g.restrict ι) v e).mp he)
  · intro e _ f _ hef
    exact ι.injective hef

def freeGeometry (g : EndpointGeometry V E) (τ : PartialColouring E C) : EndpointGeometry V τ.FreeVertex :=
  g.restrict (Function.Embedding.subtype _)

lemma freeGeometry_edgeGraph (g : EndpointGeometry V E) (τ : PartialColouring E C) :
    (g.freeGeometry τ).edgeGraph = τ.freeGraph g.edgeGraph :=
  g.restrict_edgeGraph (Function.Embedding.subtype _)

lemma freeGeometry_pinningData (g : EndpointGeometry V E) (τ : PartialColouring E C) :
    (g.freeGeometry τ).pinningData (τ.boundaryCount g.edgeGraph) = τ.toPinningData g.edgeGraph := by
  unfold pinningData PartialColouring.toPinningData
  congr 1
  exact g.freeGeometry_edgeGraph τ

lemma freeGeometry_targetLaw (g : EndpointGeometry V E) (τ : PartialColouring E C)
    (x : ℝ) (hx : 0 < x) :
    (g.freeGeometry τ).targetColourLaw x hx (τ.boundaryCount g.edgeGraph) =
      (τ.toPinningData g.edgeGraph).gibbs x hx.le
        ((τ.toPinningData g.edgeGraph).partition_pos_of_parameter_pos hx) := by
  have hw (φ : τ.FreeVertex → C) :
      (g.freeGeometry τ).targetColourWeight x (τ.boundaryCount g.edgeGraph) φ =
        (τ.toPinningData g.edgeGraph).weight x φ := by
    rw [targetColourWeight_eq_pinningWeight, freeGeometry_pinningData]
  apply FinDist.ext
  funext φ
  simp only [targetColourLaw, targetColourPartition, PinningData.gibbs, PinningData.partition, hw]

lemma freeGeometry_approxSlotSystem_bounds (g : EndpointGeometry V E) (τ : PartialColouring E C)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) {Δ : ℕ}
    (hdegree : ∀ v, (g.incidentEdges v).card ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) (n : ℕ) :
    ((g.freeGeometry τ).approxSlotSystem x hx hx1 (τ.boundaryCount g.edgeGraph) n).Bounds
      (fun _ => ∅) Δ := by
  apply slotSystem_bounds _ _ _ (finiteApproxSlotWeights_sum x hx hx1 _) x hx.le hx1.le _ hq
  · intro v
    rw [slotSystem_incident]
    exact (g.restrict_incident_le (Function.Embedding.subtype _) v).trans (hdegree v)
  · intro e
    rw [slotSystem_edgeDegree, freeGeometry_edgeGraph]
    change (τ.toPinningData g.edgeGraph).constraintDegree e + 2 ≤ 2 * Δ
    rw [τ.constraintDegree_eq_degree]
    exact g.edgeGraph_degree_bound hdegree e.val

theorem root_children_ci_open (g : EndpointGeometry V E) (τ : PartialColouring E C)
    (r : τ.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdegree : ∀ v, (g.incidentEdges v).card ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    W ham ((rootChildData τ g.edgeGraph r a).gibbs x hx.le
      ((rootChildData τ g.edgeGraph r a).partition_pos_of_parameter_pos hx))
      ((rootChildData τ g.edgeGraph r b).gibbs x hx.le
        ((rootChildData τ g.edgeGraph r b).partition_pos_of_parameter_pos hx)) ≤ (Δ : ℝ) - 1 := by
  apply (W_rootChildren_le_rootExcluded τ g.edgeGraph r a b x hx).trans
  rw [← freeGeometry_targetLaw g τ x hx]
  apply targetRootExcludedColourLaw_W_le (g.freeGeometry τ) x hx hx1
    (τ.boundaryCount g.edgeGraph) r a b
  intro n
  have hB := g.freeGeometry_approxSlotSystem_bounds τ x hx hx1 hdegree hq n
  apply approxRootExcludedColourLaw_W_le (g.freeGeometry τ) x hx hx1
    (τ.boundaryCount g.edgeGraph) n hB r a b
  intro ξ η hξ hη
  exact ((g.freeGeometry τ).approxSlotSystem x hx hx1 (τ.boundaryCount g.edgeGraph) n).root_state_ci
    hΔ (fun _ => ∅) hB r ξ η hξ hη

theorem root_children_ci_positive (g : EndpointGeometry V E) (τ : PartialColouring E C)
    (r : τ.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdegree : ∀ v, (g.incidentEdges v).card ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    W ham ((rootChildData τ g.edgeGraph r a).gibbs x hx.le
      ((rootChildData τ g.edgeGraph r a).partition_pos_of_parameter_pos hx))
      ((rootChildData τ g.edgeGraph r b).gibbs x hx.le
        ((rootChildData τ g.edgeGraph r b).partition_pos_of_parameter_pos hx)) ≤ (Δ : ℝ) - 1 := by
  rcases eq_or_lt_of_le hx1 with rfl | hlt
  · rw [pinningGibbs_one_eq (rootChildData τ g.edgeGraph r a) (rootChildData τ g.edgeGraph r b),
      W_self ham_nonneg ham_self]
    exact sub_nonneg.mpr (by exact_mod_cast hΔ)
  · exact g.root_children_ci_open τ r a b hΔ hdegree hq x hx hlt

theorem root_children_ci (g : EndpointGeometry V E) (τ : PartialColouring E C)
    (r : τ.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdegree : ∀ v, (g.incidentEdges v).card ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1)
    (ha : 0 < (rootChildData τ g.edgeGraph r a).partition x)
    (hb : 0 < (rootChildData τ g.edgeGraph r b).partition x) :
    W ham ((rootChildData τ g.edgeGraph r a).gibbs x x.property ha)
      ((rootChildData τ g.edgeGraph r b).gibbs x x.property hb) ≤ (Δ : ℝ) - 1 := by
  by_cases hz : (x : ℝ) = 0
  · have hx : x = PinningData.hardParameter := Subtype.ext hz
    subst x
    have hl : Tendsto (fun n => (CI2ZF.hardApproach n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    let μ (c : C) (n : ℕ) := (rootChildData τ g.edgeGraph r c).gibbs (CI2ZF.hardApproach n)
      (CI2ZF.hardApproach n).property
      ((rootChildData τ g.edgeGraph r c).partition_pos_of_parameter_pos (CI2ZF.hardApproach_pos n))
    have hlim (c : C) (hc : 0 < (rootChildData τ g.edgeGraph r c).partition 0)
        (σ : RootRemaining τ r → C) :
        Tendsto (fun n => (μ c n).w σ) atTop
          (𝓝 (((rootChildData τ g.edgeGraph r c).gibbs 0 le_rfl hc).w σ)) := by
      exact (((rootChildData τ g.edgeGraph r c).continuous_weight σ).continuousAt.tendsto.comp hl).div
        ((rootChildData τ g.edgeGraph r c).continuous_partition.continuousAt.tendsto.comp hl) hc.ne'
    apply W_le_of_pointwise_limits ham_nonneg ham_self ham_triangle ham_le_card
      (μ a) (μ b) _ _ (hlim a ha) (hlim b hb)
    exact Filter.Eventually.of_forall fun n => g.root_children_ci_positive τ r a b hΔ hdegree hq
      (CI2ZF.hardApproach n) (CI2ZF.hardApproach_pos n) (CI2ZF.hardApproach_le_one n)
  · exact g.root_children_ci_positive τ r a b hΔ hdegree hq x
      (lt_of_le_of_ne x.property (Ne.symm hz)) hx1

end EndpointGeometry
end
end CI2ZF.Appendix.Edge
