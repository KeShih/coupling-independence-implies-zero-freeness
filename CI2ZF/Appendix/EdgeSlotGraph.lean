import CI2ZF.Appendix.EdgeSlotLiftBounds
import CI2ZF.PottsModel
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-! The endpoint collision exponent is the literal monochromatic edge count
of a line graph. Local monochromatic cliques have disjoint edge sets. -/

namespace CI2ZF.Appendix.Edge
open PottsCI
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

namespace EndpointGeometry
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

def edgeGraph (g : EndpointGeometry V E) : SimpleGraph E where
  Adj e f := e ≠ f ∧ ∃ v, v ∈ g.endpoints e ∧ v ∈ g.endpoints f
  symm.symm _ _ h := ⟨h.1.symm, by obtain ⟨v, hv, hw⟩ := h.2; exact ⟨v, hw, hv⟩⟩
  loopless.irrefl _ h := h.1 rfl

abbrev colourGroup (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) :=
  {e : E // vc.1 ∈ g.endpoints e ∧ φ e = vc.2}

lemma endpoint_endpointIndex (g : EndpointGeometry V E) (e : E) (v : V)
    (hv : v ∈ g.endpoints e) : g.endpoint e (g.endpointIndex e v) = v := by
  obtain ⟨h, _, hh⟩ := Finset.mem_image.mp hv
  rw [← hh, endpointIndex_endpoint]

def incidenceColourEquiv (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) :
    {p : E × Fin 2 // g.incidenceColourKey φ p = vc} ≃ g.colourGroup φ vc where
  toFun p := ⟨p.val.1, (congrArg Prod.fst p.property) ▸ g.endpoint_mem p.val.1 p.val.2,
    congrArg Prod.snd p.property⟩
  invFun e := ⟨(e.val, g.endpointIndex e.val vc.1), by
    apply Prod.ext
    · exact g.endpoint_endpointIndex e.val vc.1 e.property.1
    · exact e.property.2⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, g.endpointIndex p.val.1 vc.1) = p.val
    apply Prod.ext
    · rfl
    · change g.endpointIndex p.val.1 vc.1 = p.val.2
      exact (congrArg (g.endpointIndex p.val.1) (congrArg Prod.fst p.property)).symm.trans
        (g.endpointIndex_endpoint p.val.1 p.val.2)
  right_inv _ := rfl

lemma colourGroup_card (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) :
    Fintype.card (g.colourGroup φ vc) = g.colourIncidenceCount φ vc :=
  (Fintype.card_congr (g.incidenceColourEquiv φ vc)).symm

def colourClique (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) : SimpleGraph E :=
  (⊤ : SimpleGraph (g.colourGroup φ vc)).map (Function.Embedding.subtype _)

lemma colourClique_adj (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) (e f : E) :
    (g.colourClique φ vc).Adj e f ↔ e ≠ f ∧
      (vc.1 ∈ g.endpoints e ∧ φ e = vc.2) ∧ (vc.1 ∈ g.endpoints f ∧ φ f = vc.2) := by
  rw [colourClique, SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨fun h => (SimpleGraph.top_adj _ _).mp hab (Subtype.ext h), a.property, b.property⟩
  · rintro ⟨hef, he, hf⟩
    exact ⟨⟨e, he⟩, ⟨f, hf⟩, (SimpleGraph.top_adj _ _).mpr
      (fun h => hef (Subtype.mk.inj h)), rfl, rfl⟩

lemma colourClique_card (g : EndpointGeometry V E) (φ : E → C) (vc : V × C) :
    (g.colourClique φ vc).edgeFinset.card = (g.colourIncidenceCount φ vc).choose 2 := by
  have h := SimpleGraph.card_edgeFinset_map (Function.Embedding.subtype
    (fun e => vc.1 ∈ g.endpoints e ∧ φ e = vc.2)) (⊤ : SimpleGraph (g.colourGroup φ vc))
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, colourGroup_card] at h
  convert! h using 1
  congr 1
  ext z
  simp only [SimpleGraph.mem_edgeFinset]
  rfl

def sameEdgeColour (φ : E → C) (z : Sym2 E) : Prop :=
  Sym2.lift ⟨fun e f => φ e = φ f, fun _ _ => propext eq_comm⟩ z

@[simp] lemma sameEdgeColour_mk (φ : E → C) (e f : E) :
    sameEdgeColour φ s(e, f) ↔ φ e = φ f := Iff.rfl

lemma monochromatic_edges_union (g : EndpointGeometry V E) (φ : E → C) :
    (g.edgeGraph.edgeFinset.filter (sameEdgeColour φ)) =
      Finset.univ.biUnion (fun vc : V × C => (g.colourClique φ vc).edgeFinset) := by
  ext z
  induction z using Sym2.ind with
  | _ e f =>
    have hm (H : SimpleGraph E) : s(e, f) ∈ H.edgeFinset ↔ H.Adj e f :=
      SimpleGraph.mem_edgeFinset.trans (SimpleGraph.mem_edgeSet H)
    simp only [Finset.mem_filter, hm, sameEdgeColour_mk,
      Finset.mem_biUnion, Finset.mem_univ, true_and, colourClique_adj]
    change ((e ≠ f ∧ ∃ v, v ∈ g.endpoints e ∧ v ∈ g.endpoints f) ∧ φ e = φ f) ↔ _
    constructor
    · rintro ⟨⟨hef, v, hv, hw⟩, hc⟩
      exact ⟨(v, φ e), hef, ⟨hv, rfl⟩, hw, hc.symm⟩
    · rintro ⟨vc, hef, ⟨hv, hc⟩, hw, hd⟩
      exact ⟨⟨hef, vc.1, hv, hw⟩, hc.trans hd.symm⟩

lemma colourClique_disjoint (g : EndpointGeometry V E) (φ : E → C)
    {vc wd : V × C} (hne : vc ≠ wd) :
    Disjoint (g.colourClique φ vc).edgeFinset (g.colourClique φ wd).edgeFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  induction z using Sym2.ind with
  | _ e f =>
    have ha := (g.colourClique_adj φ vc e f).mp ((SimpleGraph.mem_edgeSet _).mp
      (SimpleGraph.mem_edgeFinset.mp hz))
    have hb := (g.colourClique_adj φ wd e f).mp ((SimpleGraph.mem_edgeSet _).mp
      (SimpleGraph.mem_edgeFinset.mp hw))
    have hv : vc.1 = wd.1 := by
      by_contra hh
      exact ha.1 (g.linear e f vc.1 wd.1 ha.2.1.1 ha.2.2.1 hb.2.1.1 hb.2.2.1 hh)
    exact hne (Prod.ext hv (ha.2.1.2.symm.trans hb.2.1.2))

/-- Every monochromatic adjacent edge pair belongs to exactly one endpoint
and colour clique; the clique size gives the binomial collision exponent. -/
theorem monochromatic_edge_count (g : EndpointGeometry V E) (φ : E → C) :
    (g.edgeGraph.edgeFinset.filter (sameEdgeColour φ)).card =
      ∑ vc, (g.colourIncidenceCount φ vc).choose 2 := by
  rw [monochromatic_edges_union, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun vc _ => g.colourClique_card φ vc
  · intro vc _ wd _ hne
    exact g.colourClique_disjoint φ hne

def pinningData (g : EndpointGeometry V E) (b : E → C → ℕ) : PinningData E C where
  graph := g.edgeGraph
  boundaryCount := b

lemma targetColourWeight_eq_pinningWeight (g : EndpointGeometry V E) (x : ℝ)
    (b : E → C → ℕ) (φ : E → C) :
    g.targetColourWeight x b φ = (g.pinningData b).weight x φ := by
  unfold targetColourWeight PinningData.weight pinningData
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, ← monochromatic_edge_count]
  have hf (z : Sym2 E) : PinningData.edgeFactor x φ z =
      if sameEdgeColour φ z then x else 1 := by
    induction z using Sym2.ind with
    | _ e f => rfl
  simp only [hf]
  rw [← Finset.prod_filter]
  simp

end EndpointGeometry
end
end CI2ZF.Appendix.Edge
