import ZeroFreeness.Coupling.Edge.Slots.Graph

/-! Canonical endpoint geometry of a finite simple graph, including arbitrary
partial edge colourings, and identification with its pinned line-graph law. -/

namespace ZeroFreeness.Appendix.Edge
open PottsCI
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

namespace EndpointGeometry
variable {V E F C : Type*} [Fintype V] [Fintype E] [Fintype F] [Fintype C]

def restrict (g : EndpointGeometry V E) (ι : F ↪ E) : EndpointGeometry V F where
  endpoint f := g.endpoint (ι f)
  injective f := g.injective (ι f)
  linear e f v w hve hvf hwe hwf hne :=
    ι.injective (g.linear (ι e) (ι f) v w hve hvf hwe hwf hne)

def graphEndpointEquiv (G : SimpleGraph V) (e : G.edgeSet) : Fin 2 ≃ e.val.toFinset :=
  (Finset.equivFinOfCardEq (Sym2.card_toFinset_of_not_isDiag e.val
    (G.not_isDiag_of_mem_edgeSet e.property))).symm

def graphEndpoint (G : SimpleGraph V) (e : G.edgeSet) (h : Fin 2) : V :=
  (graphEndpointEquiv G e h).val

lemma graphEndpoint_mem_iff (G : SimpleGraph V) (e : G.edgeSet) (v : V) :
    v ∈ endpointSet (graphEndpoint G) e ↔ v ∈ e.val := by
  constructor
  · rintro hv
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hv
    exact Sym2.mem_toFinset.mp (graphEndpointEquiv G e h).property
  · intro hv
    let a : e.val.toFinset := ⟨v, Sym2.mem_toFinset.mpr hv⟩
    refine Finset.mem_image.mpr ⟨(graphEndpointEquiv G e).symm a, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((graphEndpointEquiv G e).apply_symm_apply a)

def ofSimpleGraph (G : SimpleGraph V) : EndpointGeometry V G.edgeSet where
  endpoint := graphEndpoint G
  injective e _i _j h := (graphEndpointEquiv G e).injective (Subtype.ext h)
  linear e f v w hve hvf hwe hwf hne := Subtype.ext (Sym2.eq_of_ne_mem hne
    ((graphEndpoint_mem_iff G e v).mp hve) ((graphEndpoint_mem_iff G e w).mp hwe)
    ((graphEndpoint_mem_iff G f v).mp hvf) ((graphEndpoint_mem_iff G f w).mp hwf))

@[simp] lemma ofSimpleGraph_endpoint_mem (G : SimpleGraph V) (e : G.edgeSet) (v : V) :
    v ∈ (ofSimpleGraph G).endpoints e ↔ v ∈ e.val := graphEndpoint_mem_iff G e v

lemma ofSimpleGraph_edgeGraph (G : SimpleGraph V) : (ofSimpleGraph G).edgeGraph = G.lineGraph := by
  ext e f
  exact (and_congr_right fun _ => by
    simp only [ofSimpleGraph_endpoint_mem]).trans SimpleGraph.lineGraph_adj_iff_exists.symm

def freeEdgeGeometry (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C) :
    EndpointGeometry V τ.FreeVertex :=
  (ofSimpleGraph G).restrict (Function.Embedding.subtype _)

@[simp] lemma freeEdgeGeometry_endpoint_mem (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (e : τ.FreeVertex) (v : V) :
    v ∈ (freeEdgeGeometry G τ).endpoints e ↔ v ∈ e.val.val :=
  graphEndpoint_mem_iff G e.val v

lemma freeEdgeGeometry_edgeGraph (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C) :
    (freeEdgeGeometry G τ).edgeGraph = τ.freeGraph G.lineGraph := by
  ext e f
  change (e ≠ f ∧ ∃ v, v ∈ (freeEdgeGeometry G τ).endpoints e ∧
    v ∈ (freeEdgeGeometry G τ).endpoints f) ↔ G.lineGraph.Adj e.val f.val
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  simp only [freeEdgeGeometry_endpoint_mem]
  exact and_congr_left fun _ => ⟨fun h h' => h (Subtype.ext h'),
    fun h h' => h (congrArg Subtype.val h')⟩

lemma freeEdgeGeometry_pinningData (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C) :
    (freeEdgeGeometry G τ).pinningData (τ.boundaryCount G.lineGraph) = τ.toPinningData G.lineGraph := by
  unfold pinningData PartialColouring.toPinningData
  congr 1
  exact freeEdgeGeometry_edgeGraph G τ

/-- The limiting endpoint-slot weight is exactly the original normalized
Potts weight on the line graph after an arbitrary partial edge colouring. -/
theorem freeEdgeGeometry_targetWeight (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (x : ℝ) (φ : τ.FreeVertex → C) :
    (freeEdgeGeometry G τ).targetColourWeight x (τ.boundaryCount G.lineGraph) φ =
      (τ.toPinningData G.lineGraph).weight x φ := by
  rw [targetColourWeight_eq_pinningWeight, freeEdgeGeometry_pinningData]

lemma freeEdgeGeometry_targetPartition (G : SimpleGraph V) (τ : PartialColouring G.edgeSet C)
    (x : ℝ) :
    (freeEdgeGeometry G τ).targetColourPartition x (τ.boundaryCount G.lineGraph) =
      (τ.toPinningData G.lineGraph).partition x := by
  exact Finset.sum_congr rfl fun φ _ => freeEdgeGeometry_targetWeight G τ x φ

theorem freeEdgeGeometry_targetLaw [Nonempty C] (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (x : ℝ) (hx : 0 < x) :
    (freeEdgeGeometry G τ).targetColourLaw x hx (τ.boundaryCount G.lineGraph) =
      (τ.toPinningData G.lineGraph).gibbs x hx.le
        ((τ.toPinningData G.lineGraph).partition_pos_of_parameter_pos hx) := by
  apply FinDist.ext
  funext φ
  change (freeEdgeGeometry G τ).targetColourWeight x (τ.boundaryCount G.lineGraph) φ /
    (freeEdgeGeometry G τ).targetColourPartition x (τ.boundaryCount G.lineGraph) = _
  rw [freeEdgeGeometry_targetWeight, freeEdgeGeometry_targetPartition]
  rfl

/-- The constructed finite hard-label Gibbs measures project to colour laws
converging to the actual pinned line-graph Potts measure. -/
theorem finiteSlotLift_to_pinnedPotts [Nonempty C] (G : SimpleGraph V)
    (τ : PartialColouring G.edgeSet C) (x : ℝ) (hx : 0 < x) (hx1 : x < 1)
    (φ : τ.FreeVertex → C) :
    Filter.Tendsto (fun n => ((freeEdgeGeometry G τ).approxColourLaw x hx hx1
      (τ.boundaryCount G.lineGraph) n).w φ) Filter.atTop
        (nhds (((τ.toPinningData G.lineGraph).gibbs x hx.le
          ((τ.toPinningData G.lineGraph).partition_pos_of_parameter_pos hx)).w φ)) := by
  rw [← freeEdgeGeometry_targetLaw]
  exact (freeEdgeGeometry G τ).approxColourLaw_tendsto x hx hx1 _ φ

end EndpointGeometry
end
end ZeroFreeness.Appendix.Edge
